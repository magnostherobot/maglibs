module FreeMonad

total
data Free : (Type -> Type) -> Type -> Type where
  Pure : t -> Free f t
  Bind : f u -> (u -> Free f t) -> Free f t

Functor f => Functor (Free f) where
  map f (Pure x) = Pure (f x)
  map f (Bind x g) = Bind (map g x) (map f)

lift : Functor f => f a -> Free f a
lift x = Bind x Pure

mutual

  Functor f => Applicative (Free f) where
    Pure f <*> x = map f x
    Bind y f <*> x = (join $ lift (map f y)) <*> x
    pure = Pure

  covering
  Functor f => Monad (Free f) where
    join (Pure x) = x
    join (Bind x g) = Bind x (join . g)
    -- join (Bind x g) = join $ join $ lift (map g x)

fold : Functor f => (f a -> a) -> Free f a -> a
fold g (Pure x) = x
fold g (Bind x h) = g (map (fold g) (map h x))

test : Free Maybe Nat
test = do x <- pure $ Just 10
          ?egge
