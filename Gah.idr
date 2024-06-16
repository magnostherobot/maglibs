(>=>): Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g x = (f x) >>= g
