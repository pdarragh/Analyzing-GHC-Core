module AAMPlugin (plugin) where
import GhcPlugins
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
               bindsOnlyPass (mapM (printBind dflags)) guts
     where printBind :: DynFlags -> CoreBind -> CoreM CoreBind
           printBind dflags bndr@(NonRec b v) = do
             putMsgS $ "Non-recurisve binding named " ++ showSDoc dflags (ppr b)
             putMsgS $ "Binding: " ++ showSDoc dflags (ppr v)
             return bndr
           printBind _ bndr = return bndr

-- Types and things

data Primitave
    = ...

data Value
    = LitVal Lit
    | Clo Env Var (Exp Var)
    | Con ConName [Value]
    | Prim Primative
    | Type Type

data Thunk
    = AppT Env (Code b) (Code b)

-- Rewritten for ease of writing
data Expr b
    = Var Id
    | Lit Literal
    | App (Expr b) (Expr b)
    | Lam b (Expr b)
    | Let (Bind b) (Expr b)
    | Case (Expr b) b Type [Alt b]
    | Cast (Expr b) Coercion
    | Tick (Tickish Id) (Expr b)
    | Type Type
    | Coercion Coercion

type Code b = Expr b

data Kont
    = App0K
    | CaseK Value Type [Alt]
    | NonRecK ... (Code b)
    | CastK

type Address = Int

type Env = Map.Map Id Address

-- rewrite to contain an address pointer
type Store = Map.Map Address Value

data State
    = Return Address Store [Kont]
    | Evaluate (Code b) Env Store [Kont]

step :: State -> State
step (Return a s k) = ret s k v
step (Evaluate c env s k) = eval env s k c 

ret :: Store -> Kont -> Value -> State
ret s k v = case k of
    App0K env a:k')
        -> Evaluate (a env s (App1K env (v:k')))
    App1K env f@(Clo env' x body):k')
        -> ...

eval :: Env -> Store -> Kont -> Code -> State
eval s k c = case c of
    Var x
        -> Return (env_lookup x env) s k
    Lit l
        -> Return (store (LitVal l)) s k
    App f a
        -> Evaluate f env s (App0K a : k)
    Lam x body
        -> Return (store (Clo env x body)) s k
    Case e0 v t alts
        -> Evaluate e env s (CaseK v t alts : k)
    Let (NonRec x e0) body
        -> Evaluate c env s (NonRecK x body : k)
    Let (Rec bndrs) body
        -> 
    Cast e0 co
        -> Evaluate c env s (CastK co : k)
    Type t
        -> Return (store (Type t)) s k
    Coercion c
        -> error "AAMPlugin.eval.Coercion: No coercion case defined."
