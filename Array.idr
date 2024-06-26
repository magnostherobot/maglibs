module Array

import Data.Vect
import Data.Nat
import System.FFI

||| Type used to represent C-style arrays.
|||
||| @n number of items in the array.
||| @t type of item contained in the array.
public export
data Arr : (n : Nat) -> (t : Type) -> Type where

Arr' = Ptr AnyPtr

public export
forgetArrType : Arr _ _ -> Arr'
forgetArrType = believe_me

public export
recallArrType : Arr' -> Arr _ _
recallArrType = believe_me

%foreign ("C:array_append_anyptr,libarray")
prim__arrayAppendAnyPtr : Arr' -> Int -> AnyPtr -> PrimIO Arr'

appendAnyPtr : {n : _} ->
               HasIO io =>
               Arr n AnyPtr ->
               AnyPtr ->
               io $ Arr (S n) AnyPtr
appendAnyPtr xs x = do let xs' = forgetArrType xs
                       res' <- primIO $ prim__arrayAppendAnyPtr xs' (cast n) x
                       pure $ recallArrType res'

||| Interface used to add support for adding elements of a new type to arrays.
public export
interface Appendable a where

  ||| Appends a value to an existing array.
  |||
  ||| @n number of items in the array prior to appending the new element.
  ||| @xs the array to append an element to.
  ||| @x the element to append to the array.
  append : {n : _} -> HasIO io =>
           (xs : Arr n a) -> (x : a) -> io $ Arr (S n) a

public export
Appendable AnyPtr where
  append = appendAnyPtr

||| Interface used to add array support for types that can be erased to AnyPtrs.
public export
interface EraseableToAnyPtr e where

  ||| Erases a type to an AnyPtr.
  |||
  ||| @e the type being erased.
  erase : e -> AnyPtr

public export
EraseableToAnyPtr e => Appendable e where
  append xs x = append xs x

forget : Ptr t -> AnyPtr
forget = prim__forgetPtr

public export
EraseableToAnyPtr (Ptr t) where
  erase = forget

structToPtr : Struct _ _ -> AnyPtr
structToPtr = believe_me

public export
EraseableToAnyPtr (Struct n ms) where
  erase = structToPtr

%foreign ("C:new_array,libarray")
prim__newArray : PrimIO Arr'

||| Creates a new, empty array.
|||
||| @t the type of elements carried by the new array.
public export
newArray : HasIO io => (0 t : Type) -> io $ Arr Z t
newArray t = do arr <- primIO prim__newArray
                pure $ recallArrType arr

foldl' : ({n : _} -> Vect n t -> t -> Vect (S n) t) ->
         Vect j t ->
         Vect k t ->
         Vect (j + k) t

test : Vect n a -> Vect n a
test xs = foldl' (flip (::)) [] xs

toArray'' : HasIO io => Appendable a => Vect n a -> io $ Arr n a
-- toArray'' xs = foldl' ?gweg ?fewg ?gewg

-- TODO
appendMany : HasIO io => Appendable t => {n : _} ->
             Arr n t -> Vect m t -> io $ Arr (m + n) t
-- appendMany xs [] = pure xs
-- appendMany xs (y :: ys) =
--   do xs' <- append xs y
--      appendMany xs' ys

toArray' : {a : _} -> {n : _} ->
           Appendable a => HasIO io => (xs : Vect n a) -> io $ Arr n a
toArray' [] = newArray a
toArray' (x :: xs) = do xs' <- toArray' xs
                        append xs' x

||| Converts a Vect to an array.
|||
||| @a the type of elements in the array.
||| @n the number of elements in the Vect.
||| @xs the Vect to be converted.
public export
toArray : {a : _} -> {n : _} ->
          Appendable a => HasIO io => (xs : Vect n a) -> io $ Arr n a
toArray xs = toArray' (reverse xs)

%foreign ("C:print_array,libarray")
prim__printArray : Arr' -> Int -> PrimIO ()

printArray : HasIO io => {n : _} -> Arr n AnyPtr -> io ()
printArray xs = let xs' = forgetArrType xs
                in primIO $ prim__printArray xs' (cast n)

main : IO ()
main = do arr <- newArray AnyPtr
          x <- malloc 16
          arr <- append arr x
          y <- malloc 16
          arr <- append arr y
          printArray arr
