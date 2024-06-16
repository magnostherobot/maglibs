module TupleMonad

import Control.App

data Builder = MkB

data BBB : a -> Type where
  B : (1 builder : Builder) -> a -> BBB a

-- Currently there's no way that the type system would be able to tell if
-- you've used get1 twice in a row and obtained copies of the linear value.
-- Might be possible to keep track of this using a "Open/Closed" value (that
-- potentially is stored in a non-linear State).
-- So calling put1 would return a linear token value that can be passed to get1
-- to retreive a value only once.
-- Calling put1 multiple times without calling get1 should not be possible, so
-- also do the opposite: have get1 return a token alongside the main value.
-- These values should only be needed at compile time, but also need to have
-- multiplicities of 1 to ensure they're used exactly once.

get1 : (0 tag : _) -> State tag t es => App1 es t
put1 : (0 tag : _) -> State tag t es => (1 _ : t) -> App1 {u = Any} es ()

build : State Builder Builder es =>
        (f : (1 _ : Builder) -> App1 es (BBB a)) -> App es a
build f = app1 $ do b <- get1 Builder
                    B b y <- f b
                    put1 Builder b
                    pure y

add : Integer -> Integer -> (1 b : Builder) -> App1 es (BBB Integer)
ret : Integer -> (1 b : Builder) -> App1 es (BBB Unit)
br : String -> (1 b : Builder) -> App1 es (BBB Unit)

test : State Builder Builder es => App es ()
test = do app1 $ put1 Builder MkB
          x <- build (add 20 3)
          build (ret x)
