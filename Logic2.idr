%hide Prelude.Not

data Not : Type -> Type where

explode : a -> Not a -> b

middle : Either a (Not a)

dneg : Not (Not a) -> a
dneg f = case middle of
              Left  x => x
              Right x => explode x f
