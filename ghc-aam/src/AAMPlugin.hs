{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}

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
install opts todos = do
    reinitializeGlobals
    return (CoreDoPluginPass "Say Name" (pass opts) : todos)

pass :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
pass opts guts = do
    dflags <- getDynFlags
    hsc_env <- getHscEnv
    mkIntegerId <- liftIO (lookupMkIntegerName dflags hsc_env)
    integerSDataCon <- liftIO (lookupIntegerSDataConName dflags hsc_env)
    -- Print all the bindings first.
    putMsgS "****************************************"
    putMsgS "Printing bindings"
    putMsgS "****************************************"
    _ <- bindsOnlyPass (mapM (printBind dflags)) guts
    -- Then convert all the integers to immediates and print the bindings.
    putMsgS "****************************************"
    putMsgS "Converting integers"
    putMsgS "****************************************"
    intGuts <- bindsOnlyPass (mapM (printBind dflags)) (convertIntegers dflags mkIntegerId integerSDataCon guts)
    -- Process the bindings out of the intGuts and put the CoreExprs into a new store.
    let (env, sto) = foldr (buildThunks env) (new_env, new_store) (unwrapBinds (mg_binds intGuts))
    -- Assume each CommandLineOption is the name of a binding to investigate.
    -- Compare each CommandLineOption to the bindings in the environment. If there's a match, run the interpreter.
    let addresses = map (getAddresses env) opts
    let exprs = map (getExprs sto) addresses
    putMsgS "****************************************"
    putMsgS "Evaluating program"
    putMsgS "****************************************"
    let ! results = map (interp sto) exprs
    putMsgS "****************************************"
    putMsgS "Outputting results"
    putMsgS "****************************************"
    mapM_ putMsgS (map resultToString results)
    -- Return the original ModGuts.
    return guts where
        printBind :: DynFlags -> CoreBind -> CoreM CoreBind
        printBind dflags bndr@(NonRec b v) = do
            putMsgS $ "Non-recurisve binding named " ++ showSDoc dflags (ppr b)
            putMsgS $ "Binding: " ++ showSDoc dflags (ppr v)
            return bndr
        printBind _ bndr = return bndr

unwrapBinds :: [CoreBind] -> [(CoreBndr, CoreExpr)]
unwrapBinds = concatMap unwrapBind

unwrapBind :: CoreBind -> [(CoreBndr, CoreExpr)]
unwrapBind (NonRec b e) = [(b, e)]
unwrapBind (Rec binds) = binds

-- Use this with a foldr.
-- Wrap all the top-level bindings into Thunks with empty environments for later evaluation.
buildThunks :: Env -> (CoreBndr, CoreExpr) -> (Env, StoreTup) -> (Env, StoreTup)
buildThunks env' (b, e) (env, s) = ((env_extend b (HeapValue (addr s)) env), (store_alloc (Thunk env' e) s))

getAddresses :: Env -> CommandLineOption -> Address
getAddresses env name = case [(n, v) | (n, v) <- Map.toList env, name == nameToString n] of
    [(_, v)] -> case v of
        HeapValue a -> a
        _ -> error "getAddresses: not a HeapValue"
    [] -> error $ "getAddresses: no binding named: " ++ name ++ " in bindings: " ++ (intercalate ", " (map (nameToString . fst) (Map.toList env)))
    vs -> error $ "getAddresses: too many bindings named: " ++ name ++ " : " ++ (intercalate ", " (map (show . fst) vs))

nameToString :: NamedThing a => a -> String
nameToString = unpackFS . occNameFS . getOccName

getExprs :: StoreTup -> Address -> (Env, CoreExpr)
getExprs (StoreTup s _) a = case store_lookup s a of
    Thunk env expr -> (env, expr)
    _ -> error "invalid value in store"

interp :: StoreTup -> (Env, CoreExpr) -> Result
interp s (env, e) = interp' (Right (Evaluate e env s []))

interp' :: Either Result State -> Result
interp' (Left res) = res
interp' (Right s) = interp' (step s)

resultToString :: Result -> String
resultToString (Result v st) = "value: " ++ show v ++ "\n" ++ "store: " ++ storeToString st

storeToString :: StoreTup -> String
storeToString (StoreTup s a) = "next address: " ++ show a ++ "\n" ++ (unlines (map show (Map.toList s)))

convertIntegers :: DynFlags -> Id -> Maybe DataCon -> ModGuts -> ModGuts
convertIntegers dflags name mdc = modGuts where
    modGuts m = m { mg_binds = coreProgram (mg_binds m) }
    coreProgram = map coreBind
    coreBind (NonRec x e) = NonRec x (expr e)
    coreBind (Rec bndrs) = Rec (map bndr bndrs)
    bndr (x, e) = (x, expr e)
    expr (Var x) = Var x
    expr (Lit (LitInteger i _)) = cvtLitInteger dflags name mdc i
    expr (Lit l) = Lit l
    expr (App f a) = App (expr f) (expr a)
    expr (Lam x body) = Lam x (expr body)
    expr (Case e v t a) = Case (expr e) v t (alts a)
    expr (Let b body) = Let (coreBind b) (expr body)
    expr (Cast e co) = Cast (expr e) co
    expr (Tick t e) = Tick t (expr e)
    expr (Type ty) = Type ty
    expr (Coercion co) = Coercion co
    alts = map alt
    alt (ac, bs, e) = (ac, bs, (expr e))

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

new_store :: StoreTup
new_store = StoreTup (Map.empty) 0

next_addr :: Address -> Address
next_addr = (+ 1)

store_alloc :: HeapValue -> StoreTup -> StoreTup
store_alloc v (StoreTup s a) = StoreTup (Map.insert a v s) (next_addr a)

store_lookup :: Store -> Address -> HeapValue
store_lookup s a = case Map.lookup a s of
    Nothing -> error ("No match for Address: " ++ (show a) ++ " in store: " ++ (show s))
    Just hv -> hv

new_env :: Env
new_env = Map.empty

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

data Result = Result Value StoreTup

step :: State -> Either Result State
step (Return v sto []) = Left (Result v sto)
step (Return v sto (k : ks)) = Right (ret v sto ks k)
step (Evaluate c env sto ks) = Right (eval env sto ks c)

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
    CaseK env bndr _ alts
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
evalType _   (LitTy tl) = LitTy tl
evalType env (CastTy t kc) = CastTy (evalType env t) kc
evalType env (CoercionTy co) = CoercionTy (evalCoer env co)

evalCoer :: Env -> Coercion -> Coercion
evalCoer env (Refl r t) = Refl r (evalType env t)
evalCoer env (TyConAppCo r tc coers) = TyConAppCo r tc (map (evalCoer env) coers)
evalCoer env (AppCo co con) = AppCo (evalCoer env co) (evalCoer env con)
evalCoer env (ForAllCo tv kco co) = ForAllCo tv (evalCoer env kco) (evalCoer (Map.delete tv env) co)
evalCoer _   (CoVarCo cv) = CoVarCo cv
evalCoer env (AxiomInstCo cb bi coers) = AxiomInstCo cb bi (map (evalCoer env) coers)
evalCoer env (UnivCo ucp r t1 t2) = UnivCo new_ucp r (evalType env t1) (evalType env t2) where
    new_ucp = case ucp of
        UnsafeCoerceProv -> UnsafeCoerceProv
        PhantomProv kco -> PhantomProv (evalCoer env kco)
        ProofIrrelProv kco -> ProofIrrelProv (evalCoer env kco)
        PluginProv s -> PluginProv s
        HoleProv cohole -> HoleProv cohole  -- Don't touch the funny IORef stuff.
evalCoer env (SymCo co) = SymCo (evalCoer env co)
evalCoer env (TransCo co1 co2) = TransCo (evalCoer env co1) (evalCoer env co2)
evalCoer env (AxiomRuleCo car coers) = AxiomRuleCo car (map (evalCoer env) coers)  -- Cannot traverse `car` because functions are opaque.
evalCoer env (NthCo i co) = NthCo i (evalCoer env co)
evalCoer env (LRCo lor con) = LRCo lor (evalCoer env con)
evalCoer env (InstCo co con) = InstCo (evalCoer env co) (evalCoer env con)
evalCoer env (CoherenceCo co kco) = CoherenceCo (evalCoer env co) (evalCoer env kco)
evalCoer env (KindCo co) = KindCo (evalCoer env co)
evalCoer env (SubCo con) = SubCo (evalCoer env con)
