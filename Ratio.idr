import Data.Nat
import Data.Nat.Factor
import Decidable.Equality
import Data.Primitives.Views

%default total

Coprime : Nat -> Nat -> Type
Coprime = GCD 1

||| Representation of simple, non-negative ratios between values.
public export
data Ratio : Type where

  ||| Zero.
  RZ : Ratio

  ||| Any non-zero, non-negative ratio.
  R : (n, d : Nat) ->
      {0 coprime : Coprime n d} ->
      {0 nnz : NonZero n} ->
      {0 dnz : NonZero d} ->
      Ratio

||| Integer (as represented using a recursive view) is greater than zero.
data IRGTZ : IntegerRec i -> Type where
  MkIRGTZ : IRGTZ (IntegerSucc x)

||| Integer is greater than zero.
IGTZ : Integer -> Type
IGTZ i = IRGTZ (integerRec i)

Uninhabited (IRGTZ IntegerZ) where
  uninhabited MkIRGTZ impossible

-- FIXME
-- For some reason, this implementation really slows down compilation.
(x : IntegerRec _) => Uninhabited (IRGTZ (IntegerPred x)) where
  uninhabited MkIRGTZ impossible

equalsMultCommutative : {a, b, c : Nat} -> a = b * c -> a = c * b
equalsMultCommutative Refl = multCommutative b c

multMeansLeftNonZero : {a : Nat} -> S _ = a * _ -> NonZero a
multMeansLeftNonZero {a = S _} _ = SIsNonZero

multMeansRightNonZero : {a, b, c : Nat} -> NonZero c -> c = a * b -> NonZero b
multMeansRightNonZero SIsNonZero = multMeansLeftNonZero . equalsMultCommutative

||| The product of two non-zero numbers must be non-zero.
productNonZero : NonZero a -> NonZero b -> NonZero (a * b)
productNonZero SIsNonZero SIsNonZero = SIsNonZero

decIRGTZ : (i : Integer) -> (r : IntegerRec i) -> Dec (IRGTZ r)
decIRGTZ 0 IntegerZ = No uninhabited
decIRGTZ _ (IntegerPred _) = No uninhabited
decIRGTZ _ (IntegerSucc _) = Yes MkIRGTZ

decIGTZ : (i : Integer) -> Dec (IGTZ i)
decIGTZ i = decIRGTZ i (integerRec i)

||| If an integer is greater than zero,
||| its natural-number representation is non-zero.
-- TODO
-- Restricted to compile-time only while it is unimplemented.
0
integerToNatNonZero : IGTZ a -> NonZero (integerToNat a)

commonFactorMeansFactor : (q : Nat) -> CommonFactor q _ n -> Factor q n
commonFactorMeansFactor _ (CommonFactorExists _ _ y) = y

||| The GCD of any number and one is one.
gcdOneOne : {a : Nat} -> GCD 1 a 1
gcdOneOne = MkGCD (oneCommonFactor a 1) commonFactorMeansFactor

||| Helper function for creating Ratios.
|||
||| Will automatically simplify the numerator and denominator, and create the
||| required proofs for Ratio construction.
public export
ratio : (n, d : Nat) -> {auto 0 dnz : NonZero d} -> Ratio
ratio Z _ = RZ
ratio (S n) (S d) = let
  (factor ** gcdProof) = Data.Nat.Factor.gcd (S n) (S d)
  MkGCD (CommonFactorExists _ 
    (CofactorExists n' pn')
    (CofactorExists d' pd')
    ) _ = gcdProof
  0 factorisedGcdProof = rewrite sym pn' in rewrite sym pd' in gcdProof
  0 coprime = divByGcdGcdOne {a = factor} factorisedGcdProof
  0 n'nz = multMeansRightNonZero SIsNonZero pn'
  0 d'nz = multMeansRightNonZero SIsNonZero pd'
  in R n' d' {coprime} {nnz = n'nz} {dnz = d'nz}

export
Num Ratio where
  fromInteger x with (decIGTZ x)
    _ | No _ = RZ
    _ | Yes p = let
      0 coprime = gcdOneOne
      0 nnz = integerToNatNonZero p
      0 dnz = SIsNonZero
      in R (integerToNat x) 1 {coprime} {nnz} {dnz}

  x + RZ = x
  RZ + y = y
  (R xn xd {dnz = xdnz}) + (R yn yd {dnz = ydnz}) =
    ratio (xn * yd + yn * xd) (xd * yd) {dnz = productNonZero xdnz ydnz}

  _ * RZ = RZ
  RZ * _ = RZ
  (R xn xd {dnz = xdnz}) * (R yn yd {dnz = ydnz}) =
    ratio (xn * yn) (xd * yd) {dnz = productNonZero xdnz ydnz}

export
Show Ratio where
  show RZ = show 0
  show (R n d) = show n ++ "/" ++ show d

public export
data RatioNonZero : Ratio -> Type where
  RIsNonZero : RatioNonZero (R n d)

export
Uninhabited (RatioNonZero RZ) where
  uninhabited RIsNonZero impossible

||| Reciprocal of a ratio.
public export
recip : (x : Ratio) -> RatioNonZero x => Ratio
recip (R n d {coprime} {nnz} {dnz}) =
  R d n {coprime = symmetric coprime} {nnz = dnz} {dnz = nnz}

-- Can't implement Fractional because we can't divide by zero :(
(/) : (x, y : Ratio) -> RatioNonZero y => Ratio
x / y = x * recip y
