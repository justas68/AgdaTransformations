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
 caseLazy : Bool -> CaseInfo
 caseType : CaseType -> CaseInfo

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
  TAGuard : TTerm -> TTerm -> TAlt
  TALit : Literal -> TTerm -> TAlt

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
  GoSwitch : GoTerm -> List GoCase -> GoTerm
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

∣_-_∣ : Nat -> Nat -> Nat
∣ 0  - y     ∣ = y
∣ x     - 0  ∣ = x
∣ suc x - suc y ∣ = ∣ x - y ∣

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
    go (TLit l) = literal l -- +
    go (TPrim p) = compilePrim p -- +
    go TErased = GoErased -- +
    go (TLam t) = GoLam (go t) -- +
    go (TError TUnreachable) = UndefinedTerm
    go _ = Null

{-# TERMINATING #-}
compileGoTerm : Nat -> Nat -> GoTerm -> TTerm
compileGoTerm it  n goterm = go' it goterm
  where
  go' : Nat -> GoTerm -> TTerm
  go' 10 _ = TError TUnreachable
  go' iterates (GoVar x) = TVar (n - x)
  go' _ (GoMethodCall memberId []) = TApp (TDef (fullNameReverse memberId)) []
  go' iterates (GoMethodCall memberId x) = TApp (TDef (fullNameReverse memberId))  (map (go' (iterates + 1)) (getExpFromMethodParam x))
  go' iterates (GoCreateStruct memberId []) = TApp (TCon (fullNameReverse memberId)) []
  go' iterates (GoCreateStruct memberId x) = TApp (TCon (fullNameReverse memberId)) (map (go' (iterates + 1)) x)
  go' iterates (GoIf c x y) = TApp (TPrim PIf) ((compileGoTerm (iterates + 1) n c) ∷ (compileGoTerm (iterates + 1) n x) ∷ (compileGoTerm (iterates + 1) n y) ∷ [])
  go' iterates (PrimOp op x y) = TApp (go' (iterates + 1) op) ((go' (iterates + 1) x) ∷ (go' (iterates + 1) y) ∷ [])
  go' iterates (GoLet var t1 t2) = TLet (go' (iterates + 1) t1) (compileGoTerm (iterates + 1) (n + 1) t2)
  go' _ (Const "helper.Equals") = TPrim PEqI
  go' _ (Const "helper.Minus") = TPrim PSub
  go' _ (Const "helper.Multiply") = TPrim PMul
  go' _ (Const "helper.Add") = TPrim PAdd
  go' _ (Const "helper.MoreOrEquals") = TPrim PGeq
  go' _ (Const "helper.Less") = TPrim PLt
  go' _ (Const "if") = TPrim PIf
  go' _ (GoInt x) = TLit (LitNat x)
  go' _ (Const x) = TLit (LitChar x)
  go' iterates (GoLam x) = TLam (go' (iterates + 1) x)
  go' _ GoErased = TErased
  go' _ UndefinedTerm = TError TUnreachable
  go' _ _ = TErased

data

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

justEq : (x : Test1) -> (x ≡ (compileTest2 (compileTest1 x)))
justEq Test1' = refl
justEq Test1'' = refl
justEq (TestPrim p) = {!   !}
