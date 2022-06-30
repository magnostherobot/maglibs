import Data.Nat
import Control.WellFounded

import Compare

lteSelf : (a : Nat) -> LTE a a
lteSelf 0 = LTEZero
lteSelf (S k) = LTESucc (lteSelf k)

lteEqual : {a : Nat} -> a = b -> LTE a b
lteEqual {a=Z} Refl = LTEZero
lteEqual {a=(S k)} Refl = LTESucc (lteEqual Refl)

rem : LTE a b -> LTE b a -> a = b
rem LTEZero LTEZero = Refl
rem (LTESucc x) (LTESucc y) = cong S (rem x y)

total
ltMeansNotEqual : LT a b -> Not (a = b)
ltMeansNotEqual (LTESucc x) Refl = ltMeansNotEqual x Refl

mre : NonZero a -> GT a Z
mre SIsNonZero = LTESucc LTEZero

mer : GT a _ -> NonZero a
mer (LTESucc _) = SIsNonZero

sub0 : (a, b : Nat) -> LTE b a -> Nat
sub0 a Z _ = a
sub0 (S a') (S b') p = sub0 a' b' (fromLteSucc p)

||| Subtract b from a, and provide proof that the result is
||| less than or equal to a.
sub1 : (a, b : Nat) -> LTE b a -> (x ** LTE x a)
sub1 a Z _ = (a ** lteSelf a)
sub1 (S a') (S b') bltea with (sub1 a' b' (fromLteSucc bltea))
  _ | (x ** xltea') = (x ** lteSuccRight xltea')

nzltenz : (a, b : Nat) -> LTE b a -> NonZero b -> NonZero a
nzltenz 0 0 LTEZero y = y
nzltenz (S k) 0 LTEZero y = SIsNonZero
nzltenz (S k) (S j) (LTESucc x) SIsNonZero = SIsNonZero

||| Subtract b from a, and provide proof that the result is
||| less than a.
sub2 : (a, b : Nat) -> LTE b a -> NonZero a -> NonZero b -> (x ** LT x a)
sub2 (S a') 1 _ _ _ = (a' ** lteSelf (S a'))
sub2 (S a') (S (S b'')) p _ _ =
 let
   p' = fromLteSucc p
   nza' = (nzltenz a' (S b'') p' SIsNonZero)
   (x ** xlta') = sub2 a' (S b'') p' nza' SIsNonZero
 in
   (x ** lteSuccRight xlta')

||| Subtract b from a, and provide proof that the result is
||| less than a.
sub3 : (a, b : Nat) -> LTE b a -> NonZero b -> (x ** LT x a)
sub3 a b bltea bnz = sub2 a b bltea (nzltenz a b bltea bnz) bnz

||| Subtract the smaller of the given numbers from the larger.
sub4 : (a, b : Nat) -> Nat
sub4 a b = case compareWithProof a b of
                (GT ** p) => sub0 a b (lteSuccLeft p)
                (EQ ** p) => Z
                (LT ** p) => sub0 b a (lteSuccLeft p)

||| Subtract b from a, then return b and the result in a tuple in which the
||| first element is the larger of the two (accompanied with a proof of such).
sub5 : (a, b : Nat) -> LTE b a -> (x : (Nat, Nat) ** LTE (fst x) (snd x))
sub5 a b lte =
  let
    c = sub0 a b lte
  in
    case compareWithProof b c of
         (LT ** p) => ((b, c) ** lteSuccLeft p)
         (EQ ** p) => ((b, c) ** lteEqual p)
         (GT ** p) => ((c, b) ** lteSuccLeft p)

||| Subtract b from a, then return b and the result in a tuple in which the
||| first element is the larger of the two, accompanied with proofs that:
||| - the first element of the tuple is larger than or equal to the second;
||| - the first element of the tuple is less than or equal to a;
||| - the second element of the tuple is less than or equal to a.
sub6 : (a, b : Nat) -> LTE b a ->
       (x : (Nat, Nat) ** (GTE (fst x) (snd x), LTE (fst x) a, LTE (snd x) a))
sub6 a b bltea =
  let
    (c ** cltea) = sub1 a b bltea
  in
    case compareWithProof b c of
         (GT ** bgtc) => ((b, c) ** (lteSuccLeft bgtc, bltea, cltea))
         (EQ ** beqc) => ((c, b) ** (lteEqual beqc, cltea, bltea))
         (LT ** bltc) => ((c, b) ** (lteSuccLeft bltc, cltea, bltea))

||| Subtract b from a, and provide proof that the result is non-zero.
sub7 : (a, b : Nat) -> LT b a -> (x ** NonZero x)
sub7 (S a') Z _ = ((S a') ** SIsNonZero)
sub7 (S a') (S b') (LTESucc b'lta') = sub7 a' b' b'lta'

||| Subtract b from a, and provide proof that:
||| - the result in non-zero;
||| - the result is less than a
sub8 : (a, b : Nat) -> LT b a -> NonZero b -> GT a 1 ->
       (x ** (NonZero x, LT x a))
sub8 1 _ _ _ agt1 = absurd agt1
sub8 (S (S a'')) 1 _ _ _ =
  (S a'' ** (SIsNonZero, lteSelf (S (S a''))))
sub8 2 (S (S _)) blta _ _ = absurd blta
sub8 (S (S (S a'''))) (S (S b'')) blta bnz agt1 =
  case sub8 (S (S a''')) (S b'') (fromLteSucc blta) SIsNonZero (%search) of
       (x ** (xnz, xlta')) => (x ** (xnz, lteSuccRight xlta'))

aGreater : (a, b : Nat) -> LT b a -> NonZero b -> GT a 1
aGreater 1 (S _) blta _ = absurd blta
aGreater (S (S _)) _ _ _ = LTESucc (LTESucc LTEZero)

||| Subtract b from a, and provide proof that:
||| - the result in non-zero;
||| - the result is less than a
sub9 : (a, b : Nat) -> LT b a -> NonZero b -> (x ** (NonZero x, LT x a))
sub9 a b blta bnz = sub8 a b blta bnz (aGreater a b blta bnz)

||| Subtract b from a, and provide proof that:
||| - the result in non-zero;
||| - the result is less than or equal to a
subA : (a, b : Nat) -> LT b a -> NonZero a -> (x ** (NonZero x, LTE x a))
subA a 0 _ anz = (a ** (anz, lteSelf a))
subA 1 (S _) blta _ = absurd blta
subA (S (S a'')) (S b') (LTESucc b'lta') anz =
  case subA (S a'') b' b'lta' SIsNonZero of
       (x ** (xnz, xltea')) => (x ** (xnz, lteSuccRight xltea'))

||| Subtract b from a, and provide proof that:
||| - the result in non-zero;
||| - the result is less than or equal to a
subB : (a, b : Nat) -> LT b a -> (x ** (NonZero x, LTE x a))
subB a b blta = subA a b blta (mer blta)

Uninhabited (LTE (S n) n) where
  uninhabited (LTESucc x) = uninhabited x

||| Subtract b from a, and provide proofs that:
||| - the result is less than or equal to a;
||| - if b was not zero, that the result is strictly less than a;
||| - if b was strictly less than a, that the result is not zero;
||| - if the result is strictly less than a, that b was not zero;
||| - if the result is not zero, that b was strictly less than a.
subX : (a, b : Nat) -> LTE b a -> (x ** ( LTE x a
                                        , NonZero b -> LT x a
                                        , LT b a -> NonZero x
                                        , LT x a -> NonZero b
                                        , NonZero x -> LT b a
                                        ))
subX a 0 bltea = (a ** (lteSelf a, absurd, mer, absurd, mre))
subX (S a') (S b') bltea =
  case subX a' b' (fromLteSucc bltea) of
       (c ** (p1, p2, p3, p4, p5)) => (c ** ( lteSuccRight p1
                                            , \_ => LTESucc p1
                                            , p3 . fromLteSucc
                                            , \_ => SIsNonZero
                                            , LTESucc . p5
                                            ))

gtgt : (a, b, c : Nat) -> GT a b -> GT b c -> GT a c
gtgt (S k) (S j) 0 _ _ = LTESucc LTEZero
gtgt (S k) (S j) (S i) (LTESucc x) (LTESucc y) = LTESucc (gtgt k j i x y)

ltlt : (a, b, c : Nat) -> LT c b -> LT b a -> LT c a
ltlt (S k) (S j) 0 _ _ = LTESucc LTEZero
ltlt (S k) (S j) (S i) (LTESucc x) (LTESucc y) = LTESucc (ltlt k j i x y)

subC : (a, b : Nat) -> LT b a ->
       (x : (Nat, Nat) ** ( GTE (fst x) (snd x)
                          , LTE (fst x) a
                          , LT (snd x) a
                          , NonZero (fst x)
                          ))
subC a b blta =
  let
    bltea = lteSuccLeft blta
    (c ** (p1, p2, p3, p4, p5)) = subX a b bltea
  in
    case compareWithProof b c of
         (LT ** bltc) => ((c, b) ** (lteSuccLeft bltc, p1, blta, p3 blta))
         (EQ ** beqc) => ((c, b) ** (lteEqual beqc, p1, blta, p3 blta))
         (GT ** bgtc) => let clta = gtgt a b c blta bgtc in
                           ((b, c) ** (lteSuccLeft bgtc, bltea, clta, p4 clta))

eee : a = b -> NonZero a -> NonZero b
eee Refl x = x

subCX : (a, b : Nat) -> LTE b a ->
        (x : (Nat, Nat) ** ( GTE (fst x) (snd x)
                           , LTE (fst x) a
                           , LTE (snd x) b
                           , LT b a -> NonZero (fst x)
                           , LT b a -> LT (snd x) a
                           , NonZero b -> NonZero (fst x)
                           , NonZero b -> LT b a -> NonZero (snd x)
                           , NonZero b -> LT b a -> LT (fst x) a
                           ))
subCX a b bltea =
  let
    (c ** (p1, p2, p3, p4, p5)) = subX a b bltea
  in
    case compareWithProof b c of
      (LT ** p) => ((c, b) ** ( lteSuccLeft p
                              , p1
                              , reflexive
                              , p3
                              , id
                              , \_ => mer p
                              , const
                              , \bnz, _ => p2 bnz
                              ))
      (EQ ** p) => ((c, b) ** ( lteEqual p
                              , p1
                              , reflexive
                              , p3
                              , id
                              , eee p
                              , const
                              , \bnz, _ => p2 bnz
                              ))
      (GT ** p) => ((b, c) ** ( lteSuccLeft p
                              , bltea
                              , lteSuccLeft p
                              , \_ => mer p
                              , ltlt a b c p
                              , id
                              , \_ => p3
                              , \_ => id
                              ))

jjj : LT a b -> LTE b a -> Void
jjj (LTESucc x) y = jjj y x

-- gcd : (a, b : Nat) -> LTE b a -> NonZero b -> Nat
-- gcd 0 (S _) bltea _ = absurd bltea
-- gcd (S a') (S b') bltea bnz =
--   case compareWithProof (S a') (S b') of
--        (LT ** altb) => void (jjj altb bltea)
--        (EQ **    _) => S a'
--        (GT ** blta) => let ((x, y) ** (p1, p2, p3, p4, p5, p6, p7)) = subCX (S a') (S b') bltea in
--                     gcd x y p1 (p7 bnz blta)

LTLTE : (Nat, Nat) -> (Nat, Nat) -> Type
LTLTE (a, b) (x, y) = (LT a x, LTE b y)

LTLTEAccessible : (Nat, Nat) -> Type
LTLTEAccessible = Accessible (\x, y => LTLTE x y)

ltlteAccessible : (x : (Nat, Nat)) -> LTLTEAccessible x
ltlteAccessible x = Access (acc x)
  where
    acc : (x : (Nat, Nat)) -> (y : (Nat, Nat)) -> LTLTE y x -> LTLTEAccessible y
    acc (0, _) (_, _) (lt, _) = absurd lt
    acc ((S x'), y) (a, b) (lt, lte) =
      Access $ \(u, v), (n, m) =>
        acc (x', y) (u, v) (transitive n (fromLteSucc lt), transitive m lte)

-- gcd : (a, b : Nat) -> LTE b a -> NonZero b -> Nat
-- gcd a b bltea bnz with (ltlteAccessible (a, b))
--   gcd 0 (S _) bltea _ | _ = absurd bltea
--   gcd (S a') (S b') bltea bnz | Access rec =
--     case compareWithProof (S a') (S b') of
--          (LT ** altb) => void (jjj altb bltea)
--          (EQ **    _) => S a'
--          (GT ** blta) => let ((x, y) ** (p1, p2, p3, p4, p5, p6, p7, p8)) = subCX (S a') (S b') bltea in
--                              gcd x y p1 (p7 bnz blta) | rec (x, y) (p8 bnz blta, p3)

total
ttt : (a, b, c : Nat) -> LTE a b -> LTE a (c + b)
ttt 0 b c LTEZero = LTEZero
ttt (S a') (S b') 0 (LTESucc x) = LTESucc x
ttt (S a') (S b') (S k) (LTESucc x) = LTESucc $ ttt a' (S b') k (lteSuccRight x)

total
rrr : (a, b, c, d : Nat) -> LTE a c -> LTE b d -> LTE (a + b) (c + d)
rrr 0 0 _ _ LTEZero LTEZero = LTEZero
rrr 0 (S b') c (S d') LTEZero (LTESucc x) = ttt (S b') (S d') c (LTESucc x)
rrr (S a') b (S c') d (LTESucc x) y = LTESucc (rrr a' b c' d x y)

total
gcd : (a, b : Nat) -> LTE b a -> NonZero b -> Nat
gcd a b bltea bnz with (sizeAccessible (a, b))
  gcd 0 (S _) bltea _ | _ = absurd bltea
  gcd (S a') (S b') bltea bnz | Access rec =
    case compareWithProof (S a') (S b') of
         (LT ** altb) => void (jjj altb bltea)
         (EQ **    _) => S a'
         (GT ** blta) => let ((x, y) ** (p1, p2, p3, p4, p5, p6, p7, p8)) = subCX (S a') (S b') bltea in
                             gcd x y p1 (p7 bnz blta) | rec (x, y) (LTESucc $ rrr x y a' (S b') (fromLteSucc $ p8 bnz blta) p3)
