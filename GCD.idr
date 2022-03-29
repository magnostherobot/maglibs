module GCD

import Control.WellFounded
import Data.Nat

import Compare
import Minus

data Gwog = MkG Nat Nat

Sized Gwog where
  size (MkG x y) = 4 * x + y

gwehd : (k : Nat) ->
        ((y : Gwog) ->
          LT (size y) (S ((k + (3 * S k)) + 0)) ->
          Accessible (\x, y => LT (size x) (size y)) y) ->
        LT (4 * k + 3) (S ((k + (3 * S k)) + 0))
gwehd 0 f = LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))
gwehd (S k) f = ?geewfg

total
gwog : Nat -> Nat -> ()
gwog k j with (sizeAccessible (MkG k j))
  gwog 0 0 | Access rec = ()
  gwog (S k) 0 | Access rec = gwog k 3 | rec (MkG k 3) (gwehd k rec)
  gwog k (S j) | Access rec = gwog k j | rec (MkG k j) ?gweh

data Hmm = One | Two

Sized Hmm where
  size One = 1
  size Two = 2

-- total
hmm' : Hmm -> ()
hmm' One = ()
hmm' Two = hmm' One

total
hmm : Hmm -> ()
hmm x with (sizeAccessible x)
  hmm One | Access rec = ()
  hmm Two | Access rec = hmm One | rec One reflexive

total
hmmm : Hmm -> Hmm -> ()
hmmm x y with (sizeAccessible (x, y))
  hmmm One One | Access rec = ()
  hmmm One Two | Access rec = hmmm One One | rec (One, One) reflexive
  hmmm Two One | Access rec = hmmm One Two | rec (One, Two) ?gewh
  hmmm Two Two | Access rec = hmmm Two One | rec (Two, One) ?gerh

total
jgjj : (a, b : Nat) -> LTE (S (a + b)) (a + (S b))
jgjj 0 0 = LTESucc LTEZero
jgjj 0 (S k) = reflexive
jgjj (S k) 0 = LTESucc (jgjj k 0)
jgjj (S k) (S j) = LTESucc (jgjj k (S j))

gjk : (a : Nat) -> LTE a (S a)
gjk 0 = LTEZero
gjk (S k) = LTESucc (gjk k)

gegl : (a, b : Nat) -> LTE (S a + b) (a + S (S b))
gegl 0 0 = LTESucc LTEZero
gegl 0 (S k) = gjk (S (S k))
gegl (S k) b = LTESucc (gegl k b)

p0 : (x : Nat) -> x + 0 = x
p0 0 = Refl
p0 (S k) = cong S (p0 k)

sj : (x : Nat) -> LTE x (S x)

pggg : (x, a, b : Nat) -> LTE (x + a) (x + b) -> LTE a b
pggg 0 0 0 LTEZero = LTEZero
pggg 0 0 (S k) LTEZero = LTEZero
pggg 0 (S k) (S j) y = y
pggg (S k) 0 0 (LTESucc x) = LTEZero
pggg (S k) 0 (S j) (LTESucc x) = LTEZero
pggg (S k) (S j) 0 (LTESucc x) = (pggg k (S j) 0 x)
pggg (S k) (S j) (S i) (LTESucc x) = pggg k (S j) (S i) x

gggp : (x, a, b : Nat) -> LTE a b -> LTE (x + a) (x + b)
gggp 0 a b y = y
gggp (S k) 0 b y = LTESucc (gggp k 0 b y)
gggp (S k) (S j) 0 y = LTESucc (gggp k (S j) 0 y)
gggp (S k) (S j) (S i) y = LTESucc (gggp k (S j) (S i) y)

jll : (a, b : Nat) -> LTE (S (S a)) b -> LTE a b
jll 0 b x = LTEZero
jll (S k) (S _) (LTESucc x) = LTESucc (jll k _ x)

gewg' : {a, b, n : Nat} ->
        LTE b a ->
        LT n (S (S a)) ->
        LT n (S left) ->
        LTE (S (S (S a + n))) (S (S a + (S b)))
gewg' _ (LTESucc y) nlta = ?gewg_base -- gewg' u f (LTESucc u) SIsNonZero (LTESucc y)
gewg' _ (LTESucc z) nlta {a=S right} {b=S left} {n=S x} =
  LTESucc $ LTESucc $ LTESucc $ rewrite sym $ plusSuccRightSucc right (S left) in 
    LTESucc $ gggp right (S x) (S left) $ LTESucc $ jll x left ?nlta_aaa

ewgg : (a, b, c : Nat) -> LTE (S (S a + c)) (S (S b + (S a)))
ewgg 0 _ 0 = LTESucc (LTESucc LTEZero)
ewgg 0 (S k) (S j) = LTESucc (ewgg 0 k j)
ewgg a b c = LTESucc $ LTESucc ?gweg

Sized (Nat, Nat, NonZero a, GT b c) where
  size (x, y, p, q) = size (x, y)

gcd : (a, b : Nat) -> NonZero b -> GT a b -> Nat
gcd a b x y with (sizeAccessible (a, b, x, y))
  gcd (S a') (S b') _ (LTESucc x) | Access acc with (x)
    gcd (S (S a'')) (S b') _ (LTESucc x) | Access acc | LTESucc y =
      let (n ** (nnz, nlta)) = minusNZLT (S (S a'')) (S b') (LTESucc x) SIsNonZero
      in case compareWithProof n (S b') of
              (EQ ** p) => n
              (LT ** p) => gcd (S b') n nnz p | ?ewug -- acc (S b', n, nnz, p) (ewgg ?a ?b ?c)
              (GT ** p) => gcd n (S b') SIsNonZero p | ?wafasggerh -- acc (n, S b', SIsNonZero, p) ?fewgdfaf
