min : Ord a => a -> a -> a
min x y with (compare x y)
  _ | LT = x
  _ | _  = y

min_dup : Ord a => (x : a) -> Main.min x x = x
min_dup x with (compare x x)
  _ | LT = Refl
  _ | EQ = Refl
  _ | GT = Refl

min_comm : Ord a => (x, y : a) -> Main.min x y = Main.min y x
min_comm x y with (compare x y) | (compare y x)
  min_comm x y | with_pat | fjeig = ?min_comm_rhs
