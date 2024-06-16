import Core.Context

core : Core ()
core = coreFail (UserError "user error")

main : IO ()
main = coreRun core printLn pure
