module PDA

import Data.List

Symbol : Type
Symbol = Nat

State : Type
State = Nat

Stack : Type
Stack = List Symbol

data Action = Pop | Push Symbol | Nothing

record PDA where
  constructor MkPDA
  transitions : List ((State, Symbol, Symbol), (State, Action))
  acceptors : List State
  start : State

find : Eq a => List (a, b) -> a -> List b
find [] _ = []
find ((k, v) :: kvs) x = if x == k then v :: find kvs x else find kvs x

trans : PDA -> (State, Symbol, Symbol) -> List (State, Action)
trans pda input = find pda.transitions input

bottom : Symbol

top : Stack -> Symbol
top [] = bottom
top (x :: xs) = x

pop : Stack -> Stack
pop [] = [] -- TODO should be an error
pop (x :: xs) = xs

push : Stack -> Symbol -> Stack
push = flip (::)

record Instance where
  constructor MkI
  pda : PDA
  stack : Stack
  state : State
  input : List Symbol

newInstance : PDA -> List Symbol -> Instance
newInstance pda xs = MkI pda [] pda.start xs

edit : Action -> Stack -> Stack
edit Pop xs = pop xs
edit (Push k) xs = push xs k
edit Nothing xs = xs

tail' : List a -> List a
tail' [] = []
tail' (x :: xs) = xs

act : (i : Instance) -> (State, Action) -> Instance
act (MkI pda stack state input) (state', a) =
  MkI pda (edit a stack) state' (tail' input)

step : Instance -> List Instance
step (MkI pda stack state []) = [] -- HALT
step i@(MkI pda stack state (x :: xs)) with (state, x, top stack)
  _ | input = map (act i) (trans pda input)

erg : List () -> ()
erg [] = ()
erg (x :: xs) = erg xs

mutual
  run' : List Instance -> ()
  run' is = erg $ map run is

  total
  run : Instance -> ()
  run i = run' (step i)
