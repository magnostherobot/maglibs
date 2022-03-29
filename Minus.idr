module Minus

import Data.Nat

%default total

public export
minusNZ : (a, b : Nat) -> GT a b -> (n ** NonZero n)
minusNZ (S k)     Z _ = ((S k) ** SIsNonZero)
minusNZ (S k) (S j) p = minusNZ k j (fromLteSucc p)

public export
minusLTE : (a, b : Nat) -> GT a b -> (n ** LTE n a)
minusLTE (S k)     Z _ = ((S k) ** reflexive)
minusLTE (S k) (S j) p with (minusLTE k j (fromLteSucc p))
  _ | (n ** nltea') = (n ** lteSuccRight nltea')

public export
minusLT : (a, b : Nat) -> GT a b -> NonZero b -> (n ** LT n a)
minusLT (S k ) (S Z) _ _ = (k ** reflexive)
minusLT (S k') (S (S j)) (LTESucc p) _ with (p)
  minusLT (S (S k)) (S (S j)) (LTESucc p) _ | _ with (minusLT (S k) (S j) p SIsNonZero)
    _ | (n ** nlta') = (n ** lteSuccRight nlta')

public export
minusNZLT : (a, b : Nat) -> GT a b -> NonZero b -> (n ** (NonZero n, LT n a))
minusNZLT (S k') (S j') (LTESucc p) _ with (p)
  minusNZLT (S (S k)) (S Z) (LTESucc p) _ | _ = (S k ** (SIsNonZero, reflexive))
  minusNZLT (S (S k)) (S (S j)) (LTESucc p) _ | _ =
    let (n ** (nnz, nlta')) = minusNZLT (S k) (S j) p SIsNonZero
    in  (n ** (nnz, lteSuccRight nlta'))
