{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

module AAMPlugin (plugin) where
import GhcPlugins
import CorePrep
import TyCoRep
import Data.List (intercalate)
import qualified Data.Map as Map

plugin :: Plugin
plugin = defaultPlugin {
    installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todos = do
    reinitializeGlobals
    return (CoreDoPluginPass "Say Name" pass : todos)

pass :: ModGuts -> CoreM ModGuts
pass guts = do dflags <- getDynFlags
               hsc_env <- getHscEnv
               mkIntegerId <- liftIO (lookupMkIntegerName dflags hsc_env)
               integerSDataCon <- liftIO (lookupIntegerSDataConName dflags hsc_env)
               -- Print all the bindings first.
               putMsgS "****************************************"
               putMsgS "Printing bindings"
               putMsgS "****************************************"
               newModGuts <- bindsOnlyPass (mapM (printBind dflags)) guts
               putMsgS "****************************************"
               putMsgS "Converting integers"
               putMsgS "****************************************"
               -- Then convert all the integers to immediates and print the bindings.
               _ <- bindsOnlyPass (mapM (printBind dflags)) (convertIntegers dflags mkIntegerId integerSDataCon guts)
               return newModGuts
     where printBind :: DynFlags -> CoreBind -> CoreM CoreBind
           printBind dflags bndr@(NonRec b v) = do
             putMsgS $ "Non-recurisve binding named " ++ showSDoc dflags (ppr b)
             putMsgS $ "Binding: " ++ showSDoc dflags (ppr v)
             return bndr
           printBind _ bndr = return bndr

convertIntegers :: DynFlags -> Id -> Maybe DataCon -> ModGuts -> ModGuts
convertIntegers dflags name mdc = modGuts where
    modGuts m = m { mg_binds = coreProgram (mg_binds m) }
    coreProgram = map coreBind
    coreBind (NonRec x e) = NonRec x (exp e)
    coreBind (Rec bndrs) = Rec (map bndr bndrs)
    bndr (x, e) = (x, exp e)
    exp (Var x) = Var x
    exp (Lit (LitInteger i t)) = cvtLitInteger dflags name mdc i
    exp (Lit l) = Lit l
    exp (App f a) = App (exp f) (exp a)
    exp (Lam x body) = Lam x (exp body)
    exp (Case e v t a) = Case (exp e) v t (alts a)
    exp (Let b body) = Let (coreBind b) (exp body)
    exp (Cast e co) = Cast (exp e) co
    exp (Tick t e) = Tick t (exp e)
    exp (Type ty) = Type ty
    exp (Coercion co) = Coercion co
    alts = map alt
    alt (ac, bs, e) = (ac, bs, (exp e))

sDocToString :: Outputable a => a -> String
sDocToString = showSDocUnsafe . ppr

instance Show (CoreExpr) where
    show = sDocToString

instance Show CoreBndr where
    show = sDocToString

instance Show DataCon where
    show = error "No Show instance for DataCon."

type Address = Int

type Env = Map.Map CoreBndr Value

data HeapValue
    = Clo Env CoreBndr CoreExpr
    | Con DataCon [Value]
    | Thunk Env CoreExpr
    deriving (Show)

--instance (Outputable a) => Show a where
--    show = showSDocUnsafe . ppr

-- rewrite to contain an address pointer
type Store = Map.Map Address HeapValue

-- addr -> *next* free address to be used (not the address most recently used)
data StoreTup = StoreTup {store :: Store, addr :: Address}

next_addr :: Address -> Address
next_addr = (+ 1)

store_alloc :: HeapValue -> StoreTup -> StoreTup
store_alloc v (StoreTup s a) = StoreTup (Map.insert a v s) (next_addr a)

store_lookup :: Store -> Address -> HeapValue
store_lookup s a = case Map.lookup a s of
    Nothing -> error ("No match for Address: " ++ (show a) ++ " in store: " ++ (show s))
    Just hv -> hv

env_extend :: CoreBndr -> Value -> Env -> Env
env_extend = Map.insert

env_lookup :: Env -> CoreBndr -> Value
env_lookup env name = case Map.lookup name env of
    Nothing -> error ("No match for Id: " ++ (show name) ++ " in environment: " ++ (show env))
    Just v -> v

env_lookup_maybe :: Env -> CoreBndr -> Maybe Value
env_lookup_maybe = flip Map.lookup

data Value
    = HeapValue Address -- change to StoreAddress?
    | ImValue Literal
    | ImTuple [Value]
    | TypeValue Type
    | CoerceValue Coercion

instance Show Value where
    show (HeapValue a) = "HeapValue: " ++ (show a)
    show (ImValue l) = "ImValue: " ++ (sDocToString l)
    show (ImTuple vs) = "ImTuple: " ++ "(" ++ (intercalate "," (map show vs)) ++ ")"
    show (TypeValue t) = "Type: " ++ (sDocToString t)
    show (CoerceValue co) = "Coercion: " ++ (sDocToString co)

data Kont
    = App1K Env CoreExpr
    | CaseK Env CoreBndr Type [CoreAlt]
    | CastK Coercion
    | TickK (Tickish Id)

data State
    = Return Value StoreTup [Kont]
    | Evaluate CoreExpr Env StoreTup [Kont]

-- TODO: Call this. Be careful of initial environment (needs to contain all top-level bindings).
step :: State -> State
step (Return v sto (k : ks)) = ret v sto ks k
step (Evaluate c env sto ks) = eval env sto ks c

ret :: Value -> StoreTup -> [Kont] -> Kont -> State
ret v sto ks k = case k of
    App1K env arg ->
        case v of
            HeapValue a ->
                 case (store_lookup (store sto) a) of
                    (Clo clo_env name body) -> Evaluate body env' sto' ks where
                        env' = env_extend name (HeapValue (addr sto)) clo_env
                        sto' = store_alloc (Thunk env arg) sto
                    _ -> error "Function position of application was not a closure."
            _ -> error "Function position of application was not a HeapValue."
    CaseK env bndr ty alts
        | HeapValue a <- v -> case (store_lookup (store sto) a) of
            Con dc vs -> last [g bs e | (ac, bs, e) <- alts, f ac] where
                f :: AltCon -> Bool
                f (DataAlt dc') = dc == dc'
                f (LitAlt _) = False
                f DEFAULT = True
                g :: [CoreBndr] -> CoreExpr -> State
                g bs e = Evaluate e env' sto ks where
                    env' = foldr q (env_extend bndr v env) (zip bs vs)
                    q :: (CoreBndr, Value) -> Env -> Env
--                    q (b, v') = env_extend b v'
                    q = uncurry env_extend
            _ -> error "Non-constructor in scrutiny of a case expecting a constructor."
        | ImValue l <- v -> let
            f :: AltCon -> Bool
            f (DataAlt _) = False
            f (LitAlt l') = l == l'
            f DEFAULT = True
            g :: [CoreBndr] -> CoreExpr -> State
            g _ e = Evaluate e (env_extend bndr v env) sto ks
            in last [g bs e | (ac, bs, e) <- alts, f ac]
        | ImTuple vs <- v -> let
            f :: AltCon -> Bool
            f (DataAlt _) = True  -- TODO: Explain.
            f (LitAlt _) = False
            f DEFAULT = True
            g :: [CoreBndr] -> CoreExpr -> State
            g bs e = Evaluate e env' sto ks where
                env' = foldr q (env_extend bndr v env) (zip bs vs)
                q :: (CoreBndr, Value) -> Env -> Env
                q = uncurry env_extend
            in last [g bs e | (ac, bs, e) <- alts, f ac]
        | TypeValue _ <- v -> error "TypeValue in scrutiny of a case."
        | CoerceValue _ <- v -> error "CoerceValue in scrutiny of a case."
    CastK _ ->
        -- Ignore Casts.
        Return v sto ks
    TickK _ ->
        -- Ignore Ticks.
        Return v sto ks

eval :: Env -> StoreTup -> [Kont] -> CoreExpr -> State
eval env sto ks c = case c of
    Var x ->
        -- Look up the variable in the current environment.
        Return (env_lookup env x) sto ks
    Lit l ->
        -- We assume there are no non-immediate literals.
        Return (ImValue l) sto ks
    App f a ->
        -- Wrap application in a Thunk; evaluate function.
        Evaluate f env sto (App1K env a : ks)
    Lam x body ->
        -- Create a closure.
        Return (HeapValue (addr sto)) (store_alloc (Clo env x body) sto) ks
    Case e v t alts ->
        -- Evaluate the type and the scrutiny of the case.
        Evaluate e env sto (CaseK env v (evalType env t) alts : ks)
    Let (NonRec x e) body ->
        Evaluate body env' sto' ks where
            (env', sto') = evalBndrs env env sto [(x, e)]
    Let (Rec bndrs) body ->
        Evaluate body env' sto' ks where
            (env', sto') = evalBndrs env env' sto bndrs
    Cast e co ->
        -- Evaluate the body of the cast as well as the coercion..
        Evaluate e env sto (CastK (evalCoer env co) : ks)
    Tick t e ->
        -- Continue evaluation without dealing with the Tickish Id.
        Evaluate e env sto (TickK t : ks)
    Type ty ->
        -- Evaluate inside the Type.
        Return (TypeValue (evalType env ty)) sto ks
    Coercion co ->
        -- Evaluate inside the Coercion.
        Return (CoerceValue (evalCoer env co)) sto ks

{-
The second environment taken is used to update the evaluation after the recursion completes; this implementation depends
on Haskell's laziness to compute the result properly.
-}
evalBndrs :: Env -> Env -> StoreTup -> [(CoreBndr, CoreExpr)] -> (Env, StoreTup)
evalBndrs env _ sto [] = (env, sto)
evalBndrs env env' sto ((x, e) : bs) = evalBndrs (env_extend x v env) env' sto' bs where
    (v, sto') = evalLazy env' sto e

evalLazy :: Env -> StoreTup -> CoreExpr -> (Value, StoreTup)
evalLazy e s (Var x) = ((env_lookup e x), s)
evalLazy _ s (Lit l) = (ImValue l, s)
evalLazy e s expr = (HeapValue (addr s), (store_alloc (Thunk e expr) s))

evalType :: Env -> Type -> Type
evalType env (TyVarTy v) = case (env_lookup_maybe env v) of
    Just (TypeValue t) -> t
    Just _ -> error "Failed type lookup."
    Nothing -> TyVarTy v
evalType env (AppTy t1 t2) = AppTy (evalType env t1) (evalType env t2)
evalType env (TyConApp tc kots) = TyConApp tc (map (evalType env) kots)
evalType env (ForAllTy (Named tv vf) t) = ForAllTy (Named tv vf) (evalType (Map.delete tv env) t)
evalType env (ForAllTy (Anon t1) t2) = ForAllTy (Anon (evalType env t1)) (evalType env t2)
evalType env (LitTy tl) = LitTy tl
evalType env (CastTy t kc) = CastTy (evalType env t) kc
evalType env (CoercionTy co) = CoercionTy co

-- TODO: Check that there are no expressions or types in here that need to be evaluated.
evalCoer :: Env -> Coercion -> Coercion
evalCoer e c = c
