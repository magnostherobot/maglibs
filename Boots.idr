Source : Type

Compiler : Type
-- Compiler = Source -> Compiler

CompilesItself : Compiler -> Source -> Type
-- CompilesItself compiler source = (compiler source = compiler)

AlwaysReturnsSelf : {a : Type} -> (a -> a) -> Type
AlwaysReturnsSelf f = {x : a} -> f x = f

ReturnsSelfWhenGiven : (a -> a) -> a -> Type
ReturnsSelfWhenGiven f x = (f x = f)

foo : AlwaysReturnsSelf f -> {x : _} -> ReturnsSelfWhenGiven f x
foo p = p

DescribesWith : a -> (c : a -> a) -> (f : a -> a) -> Type
DescribesWith x c f = (c x = f)

CompilesSelf : {a : Type} -> (c : a -> a) -> Type
CompilesSelf f = {x : a} -> DescribesWith x f f

recT : Type
recT = {a : Type} -> a -> recT

f : recT
f x = f

-- trivial : recT
-- trivial x = trivial
-- 
-- bootstrapper : (x : _) -> (c ** CompilesSelf c)
-- bootstrapper x = (?a ** ?b)
