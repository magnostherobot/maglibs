module Rflfl

import Language.Reflection
import System.FFI

%language ElabReflection

foo : String -> String -> Nat

str : String

bar : TTImp -> Nat
bar (IPi _ M1 AutoImplicit _ argTy retTy) = ?bar_rhs_7
bar _ = ?dda

flat : TTImp -> List TTImp
flat (IPi _ _ ExplicitArg _ argTy retTy) = argTy :: (flat retTy)
flat (IPi _ _ _ w argTy retTy) = flat retTy
flat x = [x]

Eq Name where
  a == b = show a == show b

Eq TTImp where
  (IVar _ a) == (IVar _ b) = a == b
  _ == _ = False

BuilderRef : Type
BuilderRef = AnyPtr

ValueRef : Type
ValueRef = AnyPtr

TypeRef : Type
TypeRef = AnyPtr

BasicBlockRef : Type
BasicBlockRef = AnyPtr

data Block = MkBlock BasicBlockRef

data Builder : Block -> Type where

%foreign "c:wow"
buildBitCast : BuilderRef -> ValueRef -> TypeRef -> PrimIO ValueRef

logTerms : Elaboration m => String -> Nat -> String -> List TTImp -> m ()
logTerms _ _ _ [] = pure ()
logTerms a n b (x :: xs) = do logTerm a n b x
                              logTerms a n b xs

replace : Eq a => List (a, a) -> List a -> List a
replace xs [] = []
replace xs (y :: ys) = (replace' xs y) :: (replace xs ys) where
  replace' : List (a, a) -> a -> a
  replace' [] y = y
  replace' ((o, n) :: xs) y with (o == y)
    _ | True  = n
    _ | False = replace' xs y

blah : TTImp -> ()
blah (IVar _ n) = ?blah_rhs_0
blah _ = ?erb

wrap : Name -> String -> Elab ()
wrap old new = do [(_, info)] <- getType old
                    | [] => fail ("empty name '" ++ show old ++ "'")
                    | _ => fail ("ambiguous name '" ++ show old ++ "'")
                  let args = flat info
                  let args = replace [(`(Rflfl.BuilderRef)
                                     , `(Rflfl.Builder block))] args
                  logTerm "" 0 "me" info
                  logTerms "" 0 "em" args

%runElab wrap `{ buildBitCast } "wow"
