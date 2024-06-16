import Compiler.Common
import Idris.Syntax
import Core.Context
import Idris.Driver

compile : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> String ->
          ClosedTerm -> String -> Core (Maybe String)
compile _ _ _ _ _ _ = coreFail (UserError "user error when compiling")

execute : Ref Ctxt Defs -> Ref Syn SyntaxInfo -> String -> ClosedTerm -> Core ()
execute _ _ _ _ = coreFail (UserError "user error when executing")

failingCompiler : Codegen
failingCompiler = MkCG compile execute Nothing Nothing

main : IO ()
main = mainWithCodegens [("failure", failingCompiler)]
