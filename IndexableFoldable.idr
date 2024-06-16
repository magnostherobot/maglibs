import Data.Vect
import Data.Nat

interface IndexableFoldable t where
  head : t (S n) a -> a
  tail : t (S n) a -> t n a

IndexableFoldable Vect where
  head (x :: xs) = x
  tail (x :: xs) = xs

lem : {x : _} -> IndexableFoldable t => t x a -> (y : _) -> S x + y = x + S y
lem _ y = plusSuccRightSucc x y

foldlM : Monad m =>
         IndexableFoldable t =>
         IndexableFoldable u =>
         {k : _} ->
         {j : _} ->
         (func : {n : _} -> t n a -> a -> m $ t (S n) a) ->
         (acc : t j a) ->
         u k a ->
         m $ t (k + j) a
foldlM func acc xs {k =   Z} = pure acc
foldlM func acc xs {k = S n} = do acc' <- func acc (head xs)
                                  rewrite lem (tail xs) j
                                  foldlM func acc' (tail xs)
