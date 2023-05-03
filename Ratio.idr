import Data.Nat
import Data.Nat.Factor

import Data.Vect

%default total

Coprime : Nat -> Nat -> Type
Coprime = GCD 1

data Ratio : Type where
  RZ : Ratio
  R : (n, d : Nat) ->
      {coprime : Coprime n d} ->
      {auto nnz : NonZero n} ->
      {auto dnz : NonZero d} ->
      Ratio

unfactor : {a, b : Nat} -> Factor a b -> (c ** Factor c b)
unfactor (CofactorExists c prf) =
  (c ** (CofactorExists a (rewrite multCommutative c a in prf)))

aa : {a, b : Nat} -> NonZero b -> NotBothZero a b
aa SIsNonZero = RightIsNotZero

bb : {a : Nat} -> Factor a (S b) -> NonZero a
bb {a = 0} (CofactorExists q prf) = absurd prf
bb {a = (S _)} _ = SIsNonZero

cc : {a, b, c : Nat} -> a * b = (S c) -> NonZero a
cc {a = (S _)} _ = SIsNonZero

dd : {a, b, c : Nat} -> (S c) = a * b -> NonZero a
dd {a = (S k)} prf = SIsNonZero

de : {a, b, c : Nat} -> a = b * c -> a = c * b
de Refl = multCommutative b c

ee : {a, b, c : Nat} -> (S c) = a * b -> NonZero b
ee prf = dd (de prf)

ff : {a, b, c : Nat} -> NonZero c -> c = a * b -> NonZero b
ff {c = S c'} SIsNonZero prf = dd (de prf)

ratio : (n, d : Nat) -> {auto dnz : NonZero d} -> Ratio
ratio Z _ = RZ
ratio (S n) d = let
  (g ** gf) = Data.Nat.Factor.gcd {ok = aa dnz} (S n) d
  (MkGCD (CommonFactorExists _ 
    (CofactorExists n' pn')
    (CofactorExists d' pd')
    ) _) = gf
  p = rewrite sym pn' in rewrite sym pd' in gf
  coprime = divByGcdGcdOne {a = g} p
  n'nz = ee pn'
  d'nz = ff dnz pd'
  in R n' d' {coprime} {nnz = n'nz} {dnz = d'nz}

test : Ratio
test = ratio 20 10
