module TailRec

import Data.Nat
import Data.Nat.Views
import Control.WellFounded

data Step : (st, res : Type) -> (rel : a -> a -> Type) -> (v : a) -> Type where
  Cont : (v2 : a) -> (state : st) -> (0 prf : rel v2 v) -> Step st res rel v
  Done : (result : res) -> Step st res rel v

NatStep : Step (List Bool) String LT 10
NatStep = Cont 0 [] (LTESucc LTEZero)

interface Monad m => MonadRec m where
  total
  tailRecM : (step : (seed : a) -> st -> m (Step st b rel seed)) ->
             (seed : a) ->
             (initialState : st) ->
             (0 acc : Accessible rel seed) ->
             m b

MonadRec Maybe where
  tailRecM f seed ini (Access rec) = case f seed ini of
    Nothing                => Nothing
    Just (Done b)          => Just b
    Just (Cont s2 st2 rel) => tailRecM f s2 st2 (rec s2 rel)

total
natAcc : (n : Nat) -> Accessible LT n
natAcc n = Access (acc n)
  where acc : (u : Nat) -> (v : Nat) -> (prf : LT v u) -> Accessible LT v
        acc (S u') v (LTESucc vLTEu') =
          Access $ \w, wLTv => acc u' w (transitive {rel = LTE} wLTv vLTEu')
        acc Z _ _ impossible


WellFounded Nat LT where
  wellFounded _ =
    let
      f : (x : Nat) -> LT x y -> Accessible LT x
      f _ _ = Access f
    in
      Access f

fweg : (k : Nat) -> LTE k (k + k)
fweg 0 = LTEZero
fweg (S k) = LTESucc $ lteAddRight k

hr : (n : Nat) -> HalfRec n
hr n with (sizeAccessible n)
  hr 0 | _ = HalfRecZ
  hr (S n) | acc with (half n)
    hr (S (S (k + k))) | Access acc | HalfOdd k
      = ?gewg
--       = rewrite plusSuccRightSucc (S k) k
--           in HalfRecEven _ (halfRec (S k) | acc (S k) (LTESucc (LTESucc (lteAddRight _))))
    hr (S (k + k)) | Access acc | HalfEven k
      = HalfRecOdd k (hr k | acc k (LTESucc (lteAddRight k)))
