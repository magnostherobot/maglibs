module Compare

import Data.Nat

%default total

public export
OrdPrf : Ordering -> (Nat -> Nat -> Type)
OrdPrf LT = LT
OrdPrf EQ = Equal
OrdPrf GT = GT

ordPrfSucc : (o ** OrdPrf o a b) -> (o ** OrdPrf o (S a) (S b))
ordPrfSucc (LT ** p) = (LT ** LTESucc p)
ordPrfSucc (EQ ** p) = (EQ ** cong S p)
ordPrfSucc (GT ** p) = (GT ** LTESucc p)

public export
compareWithProof : (a, b : Nat) -> (o ** OrdPrf o a b)
compareWithProof     Z     Z = (EQ ** Refl)
compareWithProof     Z (S j) = (LT ** LTESucc LTEZero)
compareWithProof (S k)     Z = (GT ** LTESucc LTEZero)
compareWithProof (S k) (S j) = ordPrfSucc (compareWithProof k j)
