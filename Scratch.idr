data N : Type where
  Next : (1 _ : N) -> N

next : {auto 1 n : N} -> N
next = Next n

newN : (1 p : (1 n : N) -> N) -> N

newp : N
newp = newN $ \n =>
       let
         n' = n
         x = Next n'
         y = Next x
         n = Next y
       in
         n
