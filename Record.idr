data Record : List (String, Type) -> Type where
  NewRecord : Record []
  AddProp : Record kts -> (0 k : String) -> (t : Type) -> (v : t) ->
            Record ((k, t) :: kts)

addProp : Record kts -> (0 k : String) -> {t : Type} -> (v : t) ->
          Record ((k, t) :: kts)
addProp r k v = AddProp r k t v

data Idx : k -> Nat -> List (k, Type) -> Type where
  First : Idx k Z ((k, _) :: _)
  Later : Idx k i ks -> Idx k (S i) (_ :: ks)

fromLater : Idx k (S i) (x :: xs) -> Idx k i xs
fromLater (Later y) = y

dpget : Record kts -> (key : String) ->
        {auto i : Nat} -> {auto ok : Idx key i kts} -> (u ** u)
dpget (AddProp r' k t v) key with (i)
  _ | Z = (t ** v)
  _ | (S i') = dpget r' key {i = i'} {ok = fromLater ok}

Tget : Record kts -> (key : String) ->
       {auto i : Nat} -> {auto ok : Idx key i kts} -> Type
Tget r key with (dpget r key) _ | (t ** v) = t

get : (r : Record kts) -> (key : String) ->
      {auto i : Nat} -> {auto ok : Idx key i kts} -> Tget r key {i} {ok}
get r key with (dpget r key) _ | (t ** v) = v

test : Record ?
test = addProp NewRecord "wow" S

test' : ?
test' = dpget test "wow"
