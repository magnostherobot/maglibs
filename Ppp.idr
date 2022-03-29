import Data.Nat

data Instruction = R | La | RP | LP

data Cell : Nat -> Type where
  MkCell : (m : Nat) -> {auto lt : LT m n} -> Cell n

gio : (n : Nat) -> GT n 1 -> mod 1 n = 1
gio 1 (LTESucc LTEZero) impossible
gio 1 (LTESucc (LTESucc x)) impossible
gio (S (S k)) x = ?gio_rhs_3

lem : (m : Nat) -> (n : Nat) -> NonZero n -> LT (mod (S m) n) n
lem Z (S k) nnz = ?lem_rhs_2
lem (S j) (S k) nnz = ?lem_rhs_3

ltnz : LT _ n -> NonZero n
ltnz (LTESucc x) = SIsNonZero

partial
inc : {n : _} -> Cell n -> Cell n
inc (MkCell m {lt}) =
  let
    nnz = ltnz lt
    p = lem m n nnz
  in
    MkCell {lt=p} $ mod (S m) n
