import Data.Nat
import Data.Nat.Factor

import Data.Vect

%default total

Coprime : Nat -> Nat -> Type
Coprime = GCD 1

data Ratio : Type where
  RZ : Ratio
  R : (n, d : Nat) ->
      {0 coprime : Coprime n d} ->
      {0 nnz : NonZero n} ->
      {0 dnz : NonZero d} ->
      Ratio

factorMeansNonZero : {a : Nat} -> Factor a (S b) -> NonZero a
factorMeansNonZero {a = Z} (CofactorExists _ prf) = absurd prf
factorMeansNonZero {a = S _} _ = SIsNonZero

equalsMultCommutative : {a, b, c : Nat} -> a = b * c -> a = c * b
equalsMultCommutative Refl = multCommutative b c

multMeansLeftNonZero : {a : Nat} -> S _ = a * _ -> NonZero a
multMeansLeftNonZero {a = S _} _ = SIsNonZero

multMeansRightNonZero : {a, b, c : Nat} -> NonZero c -> c = a * b -> NonZero b
multMeansRightNonZero SIsNonZero = multMeansLeftNonZero . equalsMultCommutative

ratio : (n, d : Nat) -> NonZero d => Ratio
ratio Z _ = RZ
ratio (S n) (S d) = let
  (factor ** gcdProof) = Data.Nat.Factor.gcd (S n) (S d)
  MkGCD (CommonFactorExists _ 
    (CofactorExists n' pn')
    (CofactorExists d' pd')
    ) _ = gcdProof
  0 p = rewrite sym pn' in rewrite sym pd' in gcdProof
  0 coprime = divByGcdGcdOne {a = factor} p
  0 n'nz = multMeansRightNonZero SIsNonZero pn'
  0 d'nz = multMeansRightNonZero SIsNonZero pd'
  in R n' d' {coprime} {nnz = n'nz} {dnz = d'nz}

test : Ratio
test = ratio 20 10
