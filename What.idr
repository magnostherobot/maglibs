import Data.Nat

total
ltMeansNotEqual : LT a b -> Not (a = b)
ltMeansNotEqual (LTESucc x) Refl = ltMeansNotEqual x Refl

Uninhabited (LTE (S n) n) where
  uninhabited (LTESucc x) = uninhabited x

ltmne : LT a b -> Not (a = b)
ltmne (LTESucc x) Refl = uninhabited x
