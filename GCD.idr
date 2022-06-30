module GCD

import Control.WellFounded
import Data.DPair
import Data.Nat

%default total

Uninhabited (LT n n) where
  uninhabited (LTESucc x) = uninhabited x

gtMeansNZ : forall b . GT a b -> NonZero a
gtMeansNZ (LTESucc _) = SIsNonZero

nzMeansGT : NonZero a -> GT a Z
nzMeansGT SIsNonZero = LTESucc LTEZero

equalMeansLTE : {a : Nat} -> a = b -> LTE a b
equalMeansLTE {a = 0}   Refl = LTEZero
equalMeansLTE {a = S _} Refl = LTESucc (equalMeansLTE Refl)

replace : {0 p : _ -> Type} -> a = b -> p a -> p b
replace Refl x = x

absurd0 : Uninhabited t => (0 _ : t) -> a
absurd0 x = void $ uninhabited x

lteAddRight : {c : Nat} -> LTE a b -> LTE a (c + b)
lteAddRight LTEZero = LTEZero
lteAddRight {c = 0} x = x
lteAddRight {c = (S c')} (LTESucc x) = LTESucc (lteAddRight $ lteSuccRight x)

ltSums : {c : Nat} -> LTE a c -> LTE b d -> LTE (a + b) (c + d)
ltSums LTEZero LTEZero = LTEZero
ltSums LTEZero (LTESucc x) = lteAddRight (LTESucc x)
ltSums (LTESucc x) y = LTESucc (ltSums x y)

OrdPrf : Ordering -> (Nat -> Nat -> Type)
OrdPrf LT = LT
OrdPrf EQ = Equal
OrdPrf GT = GT

ordPrfSucc : DPair Ordering (\o => OrdPrf o a b) ->
             DPair Ordering (\o => OrdPrf o (S a) (S b))
ordPrfSucc (MkDPair LT p) = MkDPair LT (LTESucc p)
ordPrfSucc (MkDPair EQ p) = MkDPair EQ (cong S p)
ordPrfSucc (MkDPair GT p) = MkDPair GT (LTESucc p)

compareWithProof : (a, b : Nat) -> DPair Ordering (\o => OrdPrf o a b)
compareWithProof      0      0 = MkDPair EQ Refl
compareWithProof      0 (S b') = MkDPair LT ltZero
compareWithProof (S a')      0 = MkDPair GT ltZero
compareWithProof (S a') (S b') = ordPrfSucc $ compareWithProof a' b'

record SubProofs a b x where
  constructor SP
  xLTEa : LTE x a
  xLTa  : NonZero b -> LT x a
  bNZ   : LT x a -> NonZero b
  xNZ   : LT b a -> NonZero x
  bLTa  : NonZero x -> LT b a

subWithProofs : (a, b : Nat) -> (0 _ : LTE b a) -> DPair Nat (SubProofs a b)
subWithProofs a 0 bLTEa =
  MkDPair a (SP reflexive absurd absurd gtMeansNZ nzMeansGT)
subWithProofs (S a') (S b') bLTEa =
  case subWithProofs a' b' (fromLteSucc bLTEa) of
       MkDPair x proofs => MkDPair x (SP (lteSuccRight proofs.xLTEa)
                                         (\_ => LTESucc proofs.xLTEa)
                                         (\_ => SIsNonZero)
                                         (proofs.xNZ . fromLteSucc)
                                         (LTESucc . proofs.bLTa)
                                         )

record GCDSubProofs a b x y where
  constructor GCDSP
  xGTEy : GTE x y
  xLTEa : LTE x a
  yLTEb : LTE y b
  xNZ   : LT b a -> NonZero x
  yLTa  : LT b a -> LT y a
  xNZ'  : NonZero b -> NonZero x
  yNZ   : NonZero b -> LT b a -> NonZero y
  xLTa  : NonZero b -> LT b a -> LT x a

record GCDSubResult a b where
  constructor GCDSR
  x : Nat
  y : Nat
  proofs : GCDSubProofs a b x y

gcdSub : (a, b : Nat) -> LTE b a -> GCDSubResult a b
gcdSub a b bLTEa =
  let MkDPair c proofs = subWithProofs a b bLTEa in
      case compareWithProof b c of
           MkDPair LT bLTc => GCDSR c b (GCDSP (lteSuccLeft bLTc)
                                               proofs.xLTEa
                                               reflexive
                                               proofs.xNZ
                                               id
                                               (\_ => gtMeansNZ bLTc)
                                               const
                                               (\bNZ, _ => proofs.xLTa bNZ)
                                               )
           MkDPair EQ bEQc => GCDSR c b (GCDSP (equalMeansLTE bEQc)
                                               proofs.xLTEa
                                               reflexive
                                               proofs.xNZ
                                               id
                                               (replace bEQc {p = NonZero})
                                               const
                                               (\bNZ, _ => proofs.xLTa bNZ)
                                               )
           MkDPair GT bGTc => GCDSR b c (GCDSP (lteSuccLeft bGTc)
                                               bLTEa
                                               (lteSuccLeft bGTc)
                                               (\_ => gtMeansNZ bGTc)
                                               (transitive (lteSuccRight bGTc))
                                               id
                                               (\_ => proofs.xNZ)
                                               (\_ => id)
                                               )

gcd : (a, b : Nat) -> LTE b a -> NonZero b -> Nat
gcd a b bLTEa bNZ with (sizeAccessible (a, b))
  gcd 0 (S _) bLTEa _ | _ = absurd0 bLTEa
  gcd (S a') (S b') bLTEa bNZ | Access rec =
    case compareWithProof (S a') (S b') of
         MkDPair LT aLTb => void (LTImpliesNotGTE aLTb bLTEa)
         MkDPair EQ    _ => S a'
         MkDPair GT aGTb => let
           GCDSR x y proofs = gcdSub (S a') (S b') bLTEa
           yLTEx = proofs.xGTEy
           yNZ = proofs.yNZ bNZ aGTb
           xLTa' = proofs.xLTa bNZ aGTb
           accProof = ltSums xLTa' proofs.yLTEb
           in gcd x y yLTEx yNZ | rec (x, y) accProof
