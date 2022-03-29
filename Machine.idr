data Dir = Left | Right

State : Type
State = Nat

Symbol : Type
Symbol = Nat

Transition : Type
Transition = ((State, Symbol), (State, Symbol, Dir))

record TM where
  constructor MkTM
  transitions : List Transition
  acceptors : List State

-- no evidence of unique indices
TMTape : Type
TMTape = List (Integer, Symbol)

record Instance where
  constructor MkTMI
  tm : TM
  tape : TMTape
  currentState : State
  tapeLocation : Integer

find' : List Transition -> State -> Symbol -> Maybe (State, Symbol, Dir)
find' [] _ _ = Nothing
find' ((input, result) :: xs) st sy =
  if (st, sy) == input then Just result else find' xs st sy

find : TM -> State -> Symbol -> Maybe (State, Symbol, Dir)
find m = find' m.transitions

blank : Symbol
blank = 0

get : TMTape -> Integer -> Symbol
get [] _ = blank
get ((i, sy) :: xs) x = if x == i then sy else get xs x

write : TMTape -> Integer -> Symbol -> TMTape
write [] i sy = [(i, sy)]
write ((i', sy') :: xs) i sy =
  if i == i'
     then (i, sy) :: xs
     else (i', sy') :: write xs i sy

move : Integer -> Dir -> Integer
move x Left  = x - 1
move x Right = x + 1

step : Instance -> Maybe Instance
step (MkTMI tm tape st i) =
  case find tm st (get tape i) of
       Nothing => Nothing -- HALT
       Just (st', sy, dir) =>
         let
           tape' = write tape i sy
           i' = move i dir
         in
           Just $ MkTMI tm tape' st' i'

data TMResult = Accept | Reject

runMachine : TM -> TMTape -> (TMResult, TMTape)
decodeDescription : TMTape -> TM
