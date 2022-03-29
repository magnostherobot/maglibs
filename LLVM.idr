module LLVM

import System.FFI
import Data.Vect

import Array

llvmext : String -> String
llvmext x = "C:" ++ x ++ ",libLLVM-10"

Opaque : String -> Type
Opaque x = AnyPtr

ModuleRef     = Opaque "LLVMModuleRef"
ValueRef      = Opaque "LLVMValueRef"
TypeRef       = Opaque "LLVMTypeRef"
BuilderRef    = Opaque "LLVMBuilderRef"
BasicBlockRef = Opaque "LLVMBasicBlockRef"

%foreign (llvmext "LLVMModuleCreateWithName")
prim__createModuleWithName : String -> PrimIO ModuleRef

||| Creates a module with the given name.
createModuleWithName : HasIO io => String -> io ModuleRef
createModuleWithName n = primIO $ prim__createModuleWithName n

%foreign (llvmext "LLVMAddFunction")
prim__addFunction : ModuleRef -> String -> TypeRef -> PrimIO ValueRef

||| Adds a function to a module, and returns the new function.
addFunction : HasIO io => ModuleRef -> String -> TypeRef -> io ValueRef
addFunction m n t = primIO $ prim__addFunction m n t

%foreign (llvmext "LLVMVoidType")
voidType : TypeRef

%foreign (llvmext "LLVMFunctionType")
prim__functionType : (ret : TypeRef) ->
                     (args : Arr') ->
                     (argc : Int) ->
                     (variadic : Int) ->
                     TypeRef

functionType : {argc : Nat} ->
               (ret : TypeRef) ->
               (args : Arr argc TypeRef) ->
               (variadic : Bool) ->
               TypeRef
functionType ret args variadic =
  let args' = forgetArrType args
  in  prim__functionType ret args' (cast argc) (if variadic then 1 else 0)

functionTypeVect : HasIO io =>
                   {argc : Nat} ->
                   (ret : TypeRef) ->
                   (args : Vect argc TypeRef) ->
                   (variadic : Bool) ->
                   io TypeRef
functionTypeVect ret args variadic =
  do args' <- toArray args
     pure $ functionType ret args' variadic

%foreign (llvmext "LLVMIntType")
prim__intType : Int -> TypeRef

intType : Nat -> TypeRef
intType w = prim__intType (cast w)

%foreign (llvmext "LLVMInt32Type")
prim__int32Type : TypeRef

%foreign (llvmext "LLVMTypeOf")
prim__typeOf : ValueRef -> TypeRef

%foreign (llvmext "LLVMWriteBitcodeToFile")
prim__writeBitcodeToFile : ModuleRef -> String -> PrimIO ()

writeBitcodeToFile : HasIO io => ModuleRef -> String -> io ()
writeBitcodeToFile m n = primIO $ prim__writeBitcodeToFile m n

%foreign (llvmext "LLVMPositionBuilderAtEnd")
prim__positionBuilderAtEnd : BuilderRef -> BasicBlockRef -> PrimIO ()

positionBuilderAtEnd : HasIO io => BuilderRef -> BasicBlockRef -> io ()
positionBuilderAtEnd builder block =
  primIO $ prim__positionBuilderAtEnd builder block

%foreign (llvmext "LLVMSetInstructionCallConv")
prim__setInstructionCallConv : ValueRef -> Int -> PrimIO ()

-- TODO https://llvm.org/doxygen/group__LLVMCCoreTypes.html
data CallConv = CCC | FastCC | ColdCC | GHCCC
 
callConv : CallConv -> Int
callConv cc = case cc of CCC => 0; FastCC => 8; ColdCC => 9; GHCCC => 10

setInstructionCallConv : HasIO io => ValueRef -> CallConv -> io ()
setInstructionCallConv f cc =
  primIO $ prim__setInstructionCallConv f (callConv cc)

%foreign (llvmext "LLVMBuildCall2")
prim__buildCall : BuilderRef -> TypeRef -> ValueRef -> Arr' -> Int -> String ->
                  PrimIO ValueRef

buildCall : {argc : Nat} ->
            HasIO io =>
            (builder : BuilderRef) ->
            (funcType : TypeRef) ->
            (func : ValueRef) ->
            (args : Arr argc ValueRef) ->
            (name : String) ->
            io ValueRef
buildCall builder funcType func args name =
  let
    args' = forgetArrType args
    argc' = cast argc
  in
    primIO $ prim__buildCall builder funcType func args' argc' name

%foreign (llvmext "LLVMBuildBr")
prim__buildBr : BuilderRef -> BasicBlockRef -> PrimIO ValueRef

buildBr : HasIO io => BuilderRef -> BasicBlockRef -> io ValueRef
buildBr builder target = primIO $ prim__buildBr builder target

%foreign (llvmext "LLVMBuildICmp")
prim__buildICmp : BuilderRef -> Int -> ValueRef -> ValueRef ->
                  String -> PrimIO ValueRef

data IntPredicate = EQ | NE | UGT | UGE | ULT | ULE | SGT | SGE | SLT | SLE

intPred : IntPredicate -> Int
intPred EQ  = 32
intPred NE  = 33
intPred UGT = 34
intPred UGE = 35
intPred ULT = 36
intPred ULE = 37
intPred SGT = 38
intPred SGE = 39
intPred SLT = 40
intPred SLE = 41

buildICmp : HasIO io =>
            (builder : BuilderRef) ->
            (pred : IntPredicate) ->
            (x, y : ValueRef) ->
            (name : String) ->
            io ValueRef
buildICmp builder pred x y name =
  let
    pred' = intPred pred
  in
    primIO $ prim__buildICmp builder pred' x y name

%foreign (llvmext "LLVMSizeOf")
prim__sizeOf : TypeRef -> ValueRef

sizeOf : TypeRef -> ValueRef
sizeOf = prim__sizeOf

%foreign (llvmext "LLVMPointerType")
prim__pointerType : TypeRef -> Int -> TypeRef

-- TODO support address spaces
pointerType : TypeRef -> TypeRef
pointerType t = prim__pointerType t 0

%foreign (llvmext "LLVMAppendBasicBlock")
prim__appendBasicBlock : ValueRef -> String -> PrimIO BasicBlockRef

appendBasicBlock : HasIO io => ValueRef -> String -> io BasicBlockRef
appendBasicBlock f name = primIO $ prim__appendBasicBlock f name

main : IO ()
main = do mod <- createModuleWithName "test_module"
          let int = intType 32
          funcT <- functionTypeVect voidType [int, int] False
          func <- addFunction mod "test_function" funcT
          writeBitcodeToFile mod "test.bc"
          pure ()
