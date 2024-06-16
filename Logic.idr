%hide Prelude.Not

data Contra : Type where
  -- no constructors

Not : Type -> Type
Not a = a -> Contra

explode : Contra -> a

infixr 5 /\
(/\) : Type -> Type -> Type
(/\) = (,)

infixr 5 \/
(\/) : Type -> Type -> Type
(\/) = Either

infixr 5 <->
(<->) : Type -> Type -> Type
a <-> b = (a -> b) /\ (b -> a)

conjuctionIsolationLeft : a /\ b -> a
conjuctionIsolationLeft (x, y) = x

conjunctionIsolationRight : a /\ b -> b
conjunctionIsolationRight (x, y) = y

conjunctionSwap : a /\ b -> b /\ a
conjunctionSwap (x, y) = (y, x)

modusPonens : (a -> b) -> a -> b
modusPonens = ($)

modusTollens : (a -> b) -> Not b -> Not a
modusTollens = flip (.)

impliesTransitive : (a -> b) -> (b -> c) -> (a -> c)
impliesTransitive = flip (.)

disjunctionIntroductionLeft : a -> a \/ b
disjunctionIntroductionLeft = Left

disjunctionIntroductionRight : b -> a \/ b
disjunctionIntroductionRight = Right

disjunctionSwap : a \/ b -> b \/ a
disjunctionSwap (Left  x) = Right x
disjunctionSwap (Right x) = Left  x

hmm : (a -> Not a) -> Not a
hmm f x = f x x

dv1 : a /\ b -> Not (Not a \/ Not b)
dv1 (x, y) (Left  f) = f x
dv1 (x, y) (Right f) = f y

dv2 : Not a \/ Not b -> Not (a /\ b)
dv2 (Left  f) (x, y) = f x
dv2 (Right f) (x, y) = f y

dv3 : Not (a /\ b) -> Not a \/ Not b

dv4 : Not (Not a \/ Not b) -> a /\ b

middle : a \/ Not a

dneg : Not (Not a) -> a
dneg f = case middle of
              Left  x => x
              Right x => explode (f x)

fff : (a -> b) -> (Not a -> b) -> b
fff f g = either f g middle

impliesImplies : ((a -> b) -> c) -> (b -> c)
impliesImplies f x = f (\_ => x)

disjuntionImplesLeft : (a \/ b -> c) -> (a -> c)
disjuntionImplesLeft f x = f (Left x)

disjuntionImplesRight : (a \/ b -> c) -> (b -> c)
disjuntionImplesRight f x = f (Right x)
