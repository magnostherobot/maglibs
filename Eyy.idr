import Data.List

data Ops = Pre | App

namespace PL
  public export
  data Pre : Type -> Type where
    Nil : Pre a
    (::) : a -> Pre a -> Pre a

  public export
  append : Pre a -> a -> Pre a

namespace AL
  public export
  data App : Type -> Type where
    Nil : App a
    (::) : App a -> a -> App a

  public export
  append : App a -> a -> App a

0 flexi : Ops -> (Type -> Type)
flexi Pre = PL.Pre
flexi App = ?flexi_rhs_1

-- Foldable (flexi Pre) where
--   foldr = ?d
