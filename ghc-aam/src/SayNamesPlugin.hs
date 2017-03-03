module SayNamesPlugin (plugin) where
import GhcPlugins

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
