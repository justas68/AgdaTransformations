module main where

open import Agda.Builtin.Nat public
open import Agda.Builtin.String public
open import Agda.Builtin.List public
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool public
open import Agda.Builtin.Char public

postulate Name : Set
{-# BUILTIN QNAME Name #-}

data QName : Set where
  QName' : String -> QName

data CaseType : Set where
 CTData : QName -> CaseType
 CTNat : CaseType
 CTInt : CaseType
 CTChar : CaseType
 CTString : CaseType
 CTFloat : CaseType
 CTQName : CaseType

data CaseInfo : Set where
 CaseInfo' : Bool -> CaseType -> CaseInfo

data TPrim' : Set where
  PAdd : TPrim'
  PSub : TPrim'
  PMul : TPrim'
  PGeq : TPrim'
  PLt : TPrim'
  PEqI : TPrim'
  PIf : TPrim'

data Literal : Set where
  LitNat : Nat -> Literal
  LitChar : String -> Literal

data TError' : Set where
  TUnreachable : TError'

data TTerm : Set
data TAlt : Set
data GoMethodCallParam : Set
data GoCase : Set
Type = TTerm

data TTerm where
 TVar : Nat -> TTerm
 TPrim : TPrim' -> TTerm
 TDef : QName -> TTerm
 TCon : QName -> TTerm
 TLam : TTerm -> TTerm
 TApp : TTerm -> List TTerm -> TTerm
 TLet : TTerm -> TTerm -> TTerm
 TLit : Literal -> TTerm
 TCase : Nat -> CaseInfo -> TTerm -> List TAlt -> TTerm
 TErased : TTerm
 TError : TError' -> TTerm

data TAlt where
  TACon : QName -> Nat -> TTerm -> TAlt

data LocalId : Set where
  LocalId' : Nat -> LocalId

data GlobalId : Set where
  GlobalId' : List String -> GlobalId

data Comment : Set where
  Comment' : String -> Comment

data MemberId : Set where
  MemberId' : String -> MemberId

data TypeId : Set where
  TypeId' : String -> TypeId
  ConstructorType : String -> String -> TypeId
  GenericFunctionType : String -> String -> TypeId
  FunctionType : String -> String -> TypeId
  FunctionReturnElement : String -> TypeId
  EmptyFunctionParameter : TypeId
  EmptyType : TypeId
  PiType : TypeId -> TypeId -> TypeId

data GoTerm : Set where
  Self : GoTerm
  Local : LocalId -> GoTerm
  Global : GlobalId -> GoTerm
  GoVar : Nat -> GoTerm
  GoSwitch : GoTerm -> MemberId -> List GoCase -> GoTerm
  GoMethodCall : MemberId -> List GoMethodCallParam -> GoTerm
  GoCreateStruct : MemberId -> List GoTerm -> GoTerm
  GoIf : GoTerm -> GoTerm -> GoTerm -> GoTerm
  GoLet : String -> GoTerm -> GoTerm -> GoTerm
  PrimOp : GoTerm -> GoTerm -> GoTerm -> GoTerm
  ReturnExpression : GoTerm -> TypeId -> GoTerm
  GoInt : Nat -> GoTerm
  Const : String -> GoTerm
  UndefinedTerm : GoTerm
  GoErased : GoTerm
  GoLam : GoTerm -> GoTerm
  Null : GoTerm

data GoCase where
  GoCase' : MemberId -> Nat -> Nat -> Nat -> List GoTerm -> GoCase

data GoMethodCallParam where
   GoMethodCallParam' : GoTerm -> TypeId -> GoMethodCallParam

fullName : QName -> MemberId
fullName (QName' s) = (MemberId' s)

fullNameReverse : MemberId -> QName
fullNameReverse (MemberId' s) = (QName' s)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

literal : Literal -> GoTerm
literal (LitNat x) = (GoInt x)
literal (LitChar x) = Const x

getTypelessMethodCallParams : List GoTerm -> List GoMethodCallParam
getTypelessMethodCallParams [] = []
getTypelessMethodCallParams (x ∷ xs) = (GoMethodCallParam' x EmptyType) ∷ (getTypelessMethodCallParams xs)

getExpFromMethodParam : List GoMethodCallParam -> List GoTerm
getExpFromMethodParam [] = []
getExpFromMethodParam ((GoMethodCallParam' x _) ∷ xs) = x ∷ (getExpFromMethodParam xs)

getVarName : Nat -> String
getVarName n = (primShowChar (primNatToChar ((primCharToNat 'a') + n)))

compilePrim : TPrim' -> GoTerm
compilePrim PEqI = Const "helper.Equals"
compilePrim PSub = Const "helper.Minus"
compilePrim PMul = Const "helper.Multiply"
compilePrim PAdd = Const "helper.Add"
compilePrim PGeq = Const "helper.MoreOrEquals"
compilePrim PLt = Const "helper.Less"
compilePrim PIf = Const "if"

{-# TERMINATING #-}
compileTerm : Nat -> TTerm -> GoTerm

{-# TERMINATING #-}
compileGoTerm : Nat -> GoTerm -> TTerm

compileAlt : Nat -> Nat -> TAlt -> GoCase
compileAlt argCount switchVar (TACon con ar body) = do
  let compiled = compileTerm (argCount + ar) body
  let memId = fullName con
  GoCase' memId switchVar argCount ar (compiled ∷ [])

decompileAlt : Nat -> GoCase -> TAlt
decompileAlt n (GoCase' memId switchVar argCount ar (compiled ∷ [])) = do
  let decompiled = compileGoTerm (n + ar) compiled
  let con = fullNameReverse memId
  TACon con ar decompiled
decompileAlt n (GoCase' memId switchVar argCount ar _) = do
  let con = fullNameReverse memId
  TACon con ar (TError TUnreachable)  
  
compileTerm n tterm = go tterm
    where
    go : TTerm -> GoTerm -- +
    go (TVar x) = GoVar (n - x) -- +
    go (TApp (TDef q) x) = do -- +
      let memberId = fullName q
      GoMethodCall memberId (getTypelessMethodCallParams (map go x))
    go (TApp (TCon q) x) = do -- +
      let memberId = fullName q
      GoCreateStruct memberId (map go x)
    go (TApp (TPrim PIf) (c ∷ x ∷ y ∷ [])) = GoIf (compileTerm n c) (compileTerm n x) (compileTerm n y) -- +
    go (TApp (TPrim p) (x ∷ y ∷ [])) = PrimOp (go (TPrim p)) (go x) (go y) -- +
    go (TCon q) = do
      let memberId = fullName q
      GoCreateStruct memberId [] -- +
    go (TDef q) = do
      let memberId = fullName q
      GoMethodCall memberId [] -- +
    go (TLet varDef nextExp) = GoLet (getVarName (n + 1)) (go varDef) (compileTerm (n + 1) nextExp) -- +
    go (TCase sc (CaseInfo' false (CTData q)) (TError TUnreachable) alts) = do
      let cases = map (compileAlt n (n - sc)) alts
      GoSwitch (GoVar (n - sc)) (fullName q) cases
    go (TLit l) = literal l -- +
    go (TPrim p) = compilePrim p -- +
    go TErased = GoErased -- +
    go (TLam t) = GoLam (go t) -- +
    go (TError TUnreachable) = UndefinedTerm
    go _ = Null

compileGoTerm  n goterm = go' goterm
  where
  go' : GoTerm -> TTerm
  go' (GoVar x) = TVar (n - x)
  go' (GoMethodCall memberId []) = TDef (fullNameReverse memberId)
  go' (GoMethodCall memberId x) = TApp (TDef (fullNameReverse memberId))  (map go' (getExpFromMethodParam x))
  go' (GoCreateStruct memberId []) = TCon (fullNameReverse memberId)
  go' (GoCreateStruct memberId x) = TApp (TCon (fullNameReverse memberId)) (map go' x)
  go' (GoIf c x y) = TApp (TPrim PIf) ((compileGoTerm n c) ∷ (compileGoTerm n x) ∷ (compileGoTerm n y) ∷ [])
  go' (PrimOp op x y) = TApp (go' op) ((go' x) ∷ (go' y) ∷ [])
  go' (GoLet var t1 t2) = TLet (go' t1) (compileGoTerm (n + 1) t2)
  go' (GoSwitch (GoVar vn) name cases) = TCase (n - vn) (CaseInfo' false (CTData (fullNameReverse name))) (TError TUnreachable) (map (decompileAlt n) cases)
  go' (Const "helper.Equals") = TPrim PEqI
  go' (Const "helper.Minus") = TPrim PSub
  go' (Const "helper.Multiply") = TPrim PMul
  go' (Const "helper.Add") = TPrim PAdd
  go' (Const "helper.MoreOrEquals") = TPrim PGeq
  go' (Const "helper.Less") = TPrim PLt
  go' (Const "if") = TPrim PIf
  go' (GoInt x) = TLit (LitNat x)
  go' (Const x) = TLit (LitChar x)
  go' (GoLam x) = TLam (go' x)
  go' GoErased = TErased
  go' UndefinedTerm = TError TUnreachable
  go' _ = TErased

cong : {A B : Set} -> {a1 a2 : A} -> (f : A -> B) -> a1 ≡ a2 -> f a1 ≡ f a2
cong f refl = refl

trans : {A : Set} -> {a1 a2 a3 : A} → a1 ≡ a2 → a2 ≡ a3 → a1 ≡ a3
trans refl refl = refl

postulate minus-brackets : (m n : Nat) -> (m - (m - n)) ≡ n


data Test1 : Set where
  Test1' : Test1
  Test1'' : Test1
  TestPrim : TPrim' -> Test1

data Test2 : Set where
  Test2' : Test2
  Test22 : Test2
  TestConst : String -> Test2

compilePrim' : TPrim' -> Test2
compilePrim' PEqI = TestConst "helper.Equals"
compilePrim' PSub = TestConst "helper.Minus"
compilePrim' PMul = TestConst "helper.Multiply"
compilePrim' PAdd = TestConst "helper.Add"
compilePrim' PGeq = TestConst "helper.MoreOrEquals"
compilePrim' PLt = TestConst "helper.Less"
compilePrim' PIf = TestConst "if"

compileTest1 : Test1 -> Test2
compileTest1 Test1' = Test2'
compileTest1 Test1'' = Test22
compileTest1 (TestPrim p) = compilePrim' p

compileTest2 : Test2 -> Test1
compileTest2 Test2' = Test1'
compileTest2 Test22 = Test1''
compileTest2 (TestConst "helper.Equals") = TestPrim PEqI
compileTest2 (TestConst "helper.Minus") = TestPrim PSub
compileTest2 (TestConst "helper.Multiply") = TestPrim PMul
compileTest2 (TestConst "helper.Add") = TestPrim PAdd
compileTest2 (TestConst "helper.MoreOrEquals") = TestPrim PGeq
compileTest2 (TestConst "helper.Less") = TestPrim PLt
compileTest2 (TestConst "if") = TestPrim PIf
compileTest2 (TestConst x) = TestPrim PIf


addFunction : TTerm
addFunction = 
        TApp (TPrim PIf)
        (TApp (TPrim PEqI) (TLit (LitNat 0) ∷ TVar 1 ∷ []) ∷
        TVar 0 ∷
        TLet (TApp (TPrim PSub) (TVar 1 ∷ TLit (LitNat 1) ∷ []))
        (TApp (TPrim PAdd)
          (TLit (LitNat 1) ∷
          TApp (TDef (QName' "demo.add")) (TVar 0 ∷ TVar 1 ∷ []) ∷ []))
        ∷ [])

addEquals : addFunction ≡ (compileGoTerm 1 (compileTerm 1 addFunction))
addEquals = refl

lengthFunction : TTerm
lengthFunction = 
            TCase 0 (CaseInfo' false (CTData (QName' "demo.List")))
            (TError TUnreachable)
            (TACon (QName' "List_empty") 0 (TLit (LitNat 0)) ∷
            TACon (QName' "List_append") 2
            (TApp (TPrim PAdd)
              (TLit (LitNat 1) ∷
              TApp (TDef (QName' "length")) (TErased ∷ TVar 0 ∷ []) ∷ []))
            ∷ [])

lengthEquals : lengthFunction ≡ (compileGoTerm 0 (compileTerm 0 lengthFunction))
lengthEquals = refl            

maxFunction : TTerm
maxFunction = 
    TApp (TPrim PIf)
    (TApp (TPrim PEqI) (TLit (LitNat 0) ∷ TVar 1 ∷ []) ∷
    TVar 0 ∷
    TLet (TApp (TPrim PSub) (TVar 1 ∷ TLit (LitNat 1) ∷ []))
    (TApp (TPrim PIf)
      (TApp (TPrim PEqI) (TLit (LitNat 0) ∷ TVar 1 ∷ []) ∷
      TVar 2 ∷
      TLet (TApp (TPrim PSub) (TVar 1 ∷ TLit (LitNat 1) ∷ []))
      (TApp (TPrim PAdd)
        (TLit (LitNat 1) ∷
        TApp (TDef (QName' "max")) (TVar 1 ∷ TVar 0 ∷ []) ∷ []))
      ∷ []))
    ∷ [])

maxEquals : maxFunction ≡ (compileGoTerm 1 (compileTerm 1 maxFunction))
maxEquals = refl

bubblesortiterFuntion : TTerm
bubblesortiterFuntion = TLet (TVar 0)
  (TCase 1 (CaseInfo' false (CTData (QName' "Vec")))
  (TError TUnreachable)
  (TACon (QName' "Vec_appendV") 3
    (TApp (TPrim PIf)
    (TApp (TPrim PGeq) (TVar 5 ∷ TLit (LitNat 1) ∷ []) ∷
      TLet (TVar 4)
      (TCase 1 (CaseInfo' false (CTData (QName' "Vec")))
      (TError TUnreachable)
      (TACon (QName' "Vec_appendV") 3
        (TApp (TPrim PIf)
        (TApp (TPrim PGeq) (TVar 9 ∷ TLit (LitNat 2) ∷ []) ∷
          TLet (TApp (TDef (QName' ">")) (TVar 5 ∷ TVar 1 ∷ []))
          (TCase 0 (CaseInfo' false (CTData (QName' "Agda.Builtin.Bool")))
          (TError TUnreachable)
          (TACon (QName' "Agda.Builtin.Bool.Bool.false") 0
            (TApp (TCon (QName' "Vec_appendV"))
            (TErased ∷
              TVar 6 ∷
              TApp (TDef (QName' "bubblesortiter"))
              (TApp (TPrim PSub) (TVar 10 ∷ TLit (LitNat 1) ∷ []) ∷
              TApp (TCon (QName' "Vec_appendV")) (TErased ∷ TVar 2 ∷ TVar 1 ∷ [])
              ∷ [])
              ∷ []))
            ∷
            TACon (QName' "Agda.Builtin.Bool.Bool.false") 0
            (TApp (TCon (QName' "Vec_appendV"))
            (TErased ∷
              TVar 2 ∷
              TApp (TDef (QName' "bubblesortiter"))
              (TApp (TPrim PSub) (TVar 10 ∷ TLit (LitNat 1) ∷ []) ∷
              TApp (TCon (QName' "Vec_appendV")) (TErased ∷ TVar 6 ∷ TVar 1 ∷ [])
              ∷ [])
              ∷ []))
            ∷ []))
          ∷ TVar 8 ∷ []))
        ∷ TACon (QName' "Vec_emptyV") 0 (TVar 0) ∷ []))
      ∷ TVar 4 ∷ []))
    ∷ TACon (QName' "Vec_emptyV") 0 (TVar 0) ∷ []))

bubblesort'Function : TTerm
bubblesort'Function = TLet (TApp (TDef (QName' "eq")) (TVar 2 ∷ TVar 0 ∷ []))
  (TCase 0
  (CaseInfo' false (CTData (QName' "Agda.Builtin.Bool.Bool")))
  (TError TUnreachable)
  (TACon (QName' "Agda.Builtin.Bool.Bool.false") 0
    (TApp (TDef (QName' "bubblesort'"))
    (TVar 3 ∷
      TApp (TDef (QName' "bubblesortiter")) (TVar 3 ∷ TVar 2 ∷ []) ∷
      TApp (TPrim PAdd) (TLit (LitNat 1) ∷ TVar 1 ∷ []) ∷ []))
    ∷ TACon (QName' "Agda.Builtin.Bool.Bool.true") 0 (TVar 2) ∷ []))

bubblesortFunction : TTerm
bubblesortFunction = TApp (TDef (QName' "bubblesort'")) (TVar 1 ∷ TVar 0 ∷ TLit (LitNat 0) ∷ [])

bubblesortiterFuntionEquals : bubblesortiterFuntion ≡ (compileGoTerm 2 (compileTerm 2 bubblesortiterFuntion))
bubblesortiterFuntionEquals = refl

bubblesort'FunctionEquals : bubblesort'Function ≡ (compileGoTerm 3 (compileTerm 3 bubblesort'Function))
bubblesort'FunctionEquals = refl

bubblesortFunctionEquals : bubblesortFunction ≡ (compileGoTerm 2 (compileTerm 2 bubblesortFunction))
bubblesortFunctionEquals = refl

isPrimeFunction : TTerm
isPrimeFunction = TLet (TLet
  (TApp (TDef (QName' "dividersCount"))
    (TErased ∷ TVar 0 ∷ TVar 0 ∷ []))
  (TApp (TPrim PIf)
    (TApp (TPrim PEqI) (TLit (LitNat 2) ∷ TVar 0 ∷ []) ∷
    TCon (QName' "Agda.Builtin.Bool.Bool.true") ∷
    TApp (TPrim PIf)
    (TApp (TPrim PEqI) (TLit (LitNat 1) ∷ TVar 0 ∷ []) ∷
      TCon (QName' "Agda.Builtin.Bool.Bool.false") ∷
      TApp (TPrim PIf)
      (TApp (TPrim PGeq) (TVar 0 ∷ TLit (LitNat 2) ∷ []) ∷
      TCon (QName' "Agda.Builin.Bool.Bool.false") ∷
      TCon (QName' "Agda.Builtin.Bool.Bool.false") ∷ [])
      ∷ [])
    ∷ [])))
  (TApp (TPrim PIf)
  (TApp (TPrim PEqI) (TLit (LitNat 0) ∷ TVar 1 ∷ []) ∷
    TCon (QName' "Agda.Builtin.Bool.Bool.false") ∷
    TApp (TPrim PIf)
    (TApp (TPrim PEqI) (TLit (LitNat 1) ∷ TVar 1 ∷ []) ∷
    TCon (QName' "Agda.Builtin.Bool.Bool.false") ∷ TVar 0 ∷ [])
    ∷ []))

isPrimeFunctionEqual : isPrimeFunction ≡ (compileGoTerm 1 (compileTerm 1 isPrimeFunction))
isPrimeFunctionEqual = refl