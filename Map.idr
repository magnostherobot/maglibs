module Map

interface Map m where
  new : Eq k => {v : Type} -> m k v
  set : Eq k => {v : Type} -> m k v -> k -> v -> m k v
  get : m k v -> k -> Maybe v
  kvs : m k v -> List (k, v)

  has : m k v -> k -> Bool
  has m k = maybe False (\_ => True) (get m k)

  hasEq : Eq v => m k v -> k -> v -> Bool
  hasEq m k v = maybe False (==v) (get m k)

  getOrDefault : m k v -> k -> v -> v
  getOrDefault m k v = maybe v id (get m k)

  apply : Eq k => {v : Type} -> m k v -> k -> (v -> v) -> m k v
  apply m k f = case get m k of
                     Nothing => m
                     Just v => set m k (f v)

  keys : m k v -> List k
  keys = map fst . kvs

  values : m k v -> List v
  values = map snd . kvs

interface KVFoldable m where
  kvfoldr : (k -> v -> acc -> acc) -> acc -> m k v -> acc

interface KVFunctor m where
  kvmap : (k -> v -> u) -> m k v -> m k u

Map m => KVFoldable m where
  kvfoldr f acc m = foldr (uncurry f) acc (kvs m)

Map m => KVFunctor m where
  kvmap f m = ?grehf -- foldl (\acc, (k, v) => set acc k (f k v)) new (kvs m)

Functor f => KVFunctor (\k, v => f (k, v)) where
  kvmap fn xs = map (\(k, v) => (k, fn k v)) xs

KVFoldable m => Foldable (m k) where
  foldr f acc xs = kvfoldr (\k => f) acc xs

Foldable f => KVFoldable (\k, v => f (k, v)) where
  kvfoldr fn acc xs = foldr (uncurry fn) acc xs

ListMap : (k : Type) -> Eq k => Type -> Type
ListMap k v = List (k, v)

LM : Type -> Type -> Type
LM k v = List (k, v)

Map LM where
  new = []
  set xs k v = (k, v) :: xs
  get [] k = Nothing
  get ((k, v) :: xs) k' = ?greh -- if k == k' then Just v else get xs k
  kvs = id

test : KVFunctor f => f Nat Nat -> ()
test xs = ()

test' : LM Nat Nat

test'' : ()
test'' = test test'

-- KVFunctor m => Eq k => Functor (m k) where
  -- map f m = kvmap (\k => f) m
  -- map f m = map f (values m)

-- data Map : Type -> Type -> Type where
--   NewMap : Eq k => Map k v
--   MapAdd : Eq k => Map k v -> k -> v -> Map k v
-- 
-- Map' : (Type, Type) -> Type
-- Map' (k, v) = Map k v
-- 
-- add : Eq k => Map k v -> k -> v -> Map k v
-- add = MapAdd
-- 
-- add' : Eq k => Map k v -> (k, v) -> Map k v
-- add' m (k, v) = add m k v
-- 
-- get : Map k v -> k -> Maybe v
-- get NewMap _ = Nothing
-- get (MapAdd m k v) k' = if k == k' then Just v else get m k'
-- 
-- has : Eq v => Map k v -> k -> v -> Bool
-- has m k v = maybe False (==v) (get m k)
-- 
-- has' : Eq v => Map k v -> (k, v) -> Bool
-- has' m (k, v) = has m k v
-- 
-- mapFrom : Eq k => Foldable f => f (k, v) -> Map k v
-- mapFrom = foldl add' NewMap

-- Map m => Foldable (m k) where
  -- foldr f acc new = acc
  -- foldr f acc (add m k v) = f v (foldr f acc m)

  -- null NewMap = True
  -- null _ = False

-- Eq (Map k v) where
  -- m == n = ?gwe
