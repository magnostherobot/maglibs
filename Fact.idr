module Fact

import Data.Nat

data Factor : Nat -> Nat -> Type where
  CofactorExists : {p, n : Nat} -> (q : Nat) -> n = p * q -> Factor p n

data NotFactor : Nat -> Nat -> Type where
  ZeroNotFactorS : (n : Nat) -> NotFactor Z (S n)
  ProperRemExists : {p', n : Nat} ->
                    (q', r' : Nat) ->
                    {rltp : LT r' p'} ->
                    n === ((S p') * (S q') + (S r')) ->
                    NotFactor (S p') n

data CommonFactor : Nat -> Nat -> Nat -> Type where
  CommonFactorExists : {a, b : Nat} ->
                       (p : Nat) ->
                       Factor p a ->
                       Factor p b ->
                       CommonFactor p a b

k : CommonFactor 4 8 12
k =
  let
    x = CofactorExists 2 Refl
    y = CofactorExists 3 Refl
  in
    CommonFactorExists 4 x y

Uninhabited (Factor Z (S n)) where
  uninhabited (CofactorExists _ p) = uninhabited p

cofactor : Factor p n -> (q : Nat ** Factor q n)
cofactor (CofactorExists q prf) =
  (q ** CofactorExists p $ rewrite multCommutative q p in prf)
