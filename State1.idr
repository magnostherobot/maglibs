module State1

import Control.Linear.LIO

infixr 5 #<

data LLPair : Type -> Type -> Type where
  (#<) : (1 _ : a) -> b -> LLPair a b

record State1 s a where
  constructor ST1
  runState1 : (1 _ : s) -> LLPair s a

Functor (State1 st) where
  map f (ST1 g) = ST1 $ \s => case g s of
                                   (s' #< y) => (s' #< f y)

Applicative (State1 st) where
  pure x = ST1 $ \s => (s #< x)
  ST1 f <*> ST1 g = ST1 $ \s => case f s of
    (s' #< h) => case g s' of
      (s'' #< x) => (s'' #< h x)

Monad (State1 st) where
  ST1 f >>= g = ST1 $ \s => case f s of
                                 (s' #< x) => runState1 (g x) s'

record IOState1 st a io where
  constructor IOST1
  runIOState1 : LinearIO io => (1 _ : st) -> L1 io (LLPair st a)

map : (a -> b) -> IOState1 st a io -> IOState1 st b io
map f (IOST1 g) = IOST1 $ \s => do (s' #< x) <- g s
                                   pure1 (s' #< f x)

pure : LinearIO io => a -> IOState1 st a io
pure x = IOST1 $ \s => pure1 (s #< x)

(<*>) : IOState1 st (a -> b) io -> IOState1 st a io -> IOState1 st b io
IOST1 f <*> IOST1 g = IOST1 $ \s => do (s #< h) <- f s
                                       (s #< x) <- g s
                                       pure1 (s #< h x)

(>>=) : IOState1 st a io -> (a -> IOState1 st b io) -> IOState1 st b io
IOST1 f >>= g = IOST1 $ \s => do (s #< x) <- f s
                                 runIOState1 (g x) s

join : IOState1 st (IOState1 st a io) io -> IOState1 st a io
join (IOST1 f) = IOST1 $ \s => do (s #< x) <- f s
                                  runIOState1 x s

data Builder = MkB
data Module = MkM
data Value = MkV Integer

fromInteger : Integer -> Value
fromInteger = MkV

ret' : LinearIO io => (1 b : Builder) -> Value -> L1 io $ LLPair Builder ()
add' : LinearIO io =>
       (1 b : Builder) -> (x, y : Value) -> L1 io $ LLPair Builder Value

WithBuilder : Type -> (Type -> Type) -> Type
WithBuilder v io = IOState1 Builder v io

ret : Value -> WithBuilder () io
ret x = IOST1 $ \s => ret' s x

add : (x, y : Value) -> WithBuilder Value io
add x y = IOST1 $ \s => add' s x y

wrap : ((1 b : Builder) -> t -> L1 io $ LLPair Builder Value) -> t ->
       WithBuilder Value io
wrap f x = IOST1 $ \s => f s x

test : WithBuilder () io
test = do v <- add 20 10
          ret v

block : LinearIO io => Builder -> WithBuilder () io -> L1 io Builder
block b f = do (b #< ()) <- runIOState1 f b
               pure1 b

test' : LinearIO io => L1 io Builder
test' = block MkB $ do v <- add 2 11
                       ret v
