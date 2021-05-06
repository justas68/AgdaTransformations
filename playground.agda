module playground where

open import Agda.Builtin.Nat public
open import Agda.Builtin.String public
open import Agda.Builtin.List public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Char public


data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set} -> {a1 a2 : A} -> (f : A -> B) -> a1 ≡ a2 -> f a1 ≡ f a2
cong f refl = refl

trans : {A : Set} -> {a1 a2 a3 : A} → a1 ≡ a2 → a2 ≡ a3 → a1 ≡ a3
trans refl refl = refl

postulate minus-brackets : (m n : Nat) -> (m - (m - n)) ≡ n

zero+- : (a : Nat) -> (0 + a) ≡ a
zero+- a = refl

zero++ : (a : Nat) -> (a + 0) ≡ (0 + a)
zero++ zero = refl
zero++ (suc a) = cong suc (zero++ a)

zero-+ : (a : Nat) -> (a + 0) ≡ a
zero-+ zero = refl
zero-+ (suc n) = cong suc (zero-+ n)

plus-two : Nat -> Nat
plus-two = _+_ 2

+-suc : (a b : Nat) -> (a + (suc b)) ≡ suc ( a + b)
+-suc zero b = refl
+-suc (suc a) b = cong suc (+-suc a b)

number+- : (a b : Nat) -> (a + b) ≡ (b + a)
number+- a zero = zero-+ a
number+- a (suc b) = trans (+-suc a b) (cong suc (number+- a b))

_! : Nat -> Nat
0 ! = 1
(suc n) ! = (suc n) * (n !)

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} (i : Fin n) → Fin (suc n)

data Term (n : Nat) : Set where
  Lit : Nat → Term n
  _⊠_ : Term n → Term n → Term n
  _⊞_ : Term n → Term n → Term n
  Let_In_ : Term n → Term (suc n) → Term n
  Var : Fin n → Term n

infixl 5 _⊢_⇓_

infixr 5 _::_

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infix 4 _[_]=_

data _[_]=_ {A : Set} : ∀ {n} → Vec A n → Fin n → A → Set where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x :: xs [ zero ]= x
  there : ∀ {n} {i} {x y} {xs : Vec A n}
          (xs[i]=x : xs [ i ]= x) → y :: xs [ suc i ]= x

-- With starting state E, program x evaluates to y
data _⊢_⇓_ {n : Nat} ( E : Vec Nat n) : Term n → Nat → Set where
  lit-e : ∀{n}

            -------------
          → E ⊢ Lit n ⇓ n

  times-e : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ v₁
          → E ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ e₁ ⊠ e₂ ⇓ v₁ * v₂

  plus-e  : ∀{e₁ e₂}{v₁ v₂}

          → E ⊢ e₁ ⇓ v₁
          → E ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ e₁ ⊞ e₂ ⇓ v₁ + v₂

  var-e   : ∀{n}{x} → E [ x ]= n
            -------------
          → E ⊢ Var x ⇓ n
  let-e   : ∀{e₁}{e₂}{v₁ v₂}

          → E        ⊢ e₁ ⇓ v₁
          → (v₁ :: E) ⊢ e₂ ⇓ v₂
            ---------------------
          → E ⊢ Let e₁ In e₂ ⇓ v₂

data Inst  : Nat → Nat → Nat → Nat → Set where
  num   : ∀{w s} → Nat → Inst w s (suc w) s
  plus  : ∀{w s} → Inst (suc (suc w)) s (suc w) s
  times : ∀{w s} → Inst (suc (suc w)) s (suc w) s
  push  : ∀{w s} → Inst (suc w) s w (suc s)
  pick  : ∀{w s} → Fin s → Inst w s (suc w) s
  pop   : ∀{w s} → Inst w (suc s) w s

data SM (w s : Nat) : Nat → Nat → Set where
  halt : SM w s w s
  _::_  : ∀{w′ s′ w″ s″} → Inst w s w′ s′ → SM w′ s′ w″ s″ → SM w s w″ s″

infixr 5 _⊕_
_⊕_ : ∀{w s w′ s′ w″ s″} → SM w s w′ s′ → SM w′ s′ w″ s″ → SM w s w″ s″
halt    ⊕ q = q
(x :: p) ⊕ q = x :: (p ⊕ q)

infixl 5 _∣_∣_↦_∣_

data _∣_∣_↦_∣_ : ∀{w s w′ s′}
   → Vec Nat w → Vec Nat s
   → Inst w s w′ s′
   → Vec Nat w′ → Vec Nat s′
   → Set where
  num-e   : ∀{w s}{n}{W : Vec _ w}{S : Vec _ s}
           -------------------------
         → W ∣ S ∣ num n ↦ n :: W ∣ S
  plus-e  : ∀{w s}{n m}{W : Vec _ w}{S : Vec _ s}
         ----------------------------------------
       → (n :: m :: W) ∣ S ∣ plus ↦ (m + n :: W) ∣ S
  times-e : ∀{w s}{n m}{W : Vec _ w}{S : Vec _ s}
           -----------------------------------------
         → (n :: m :: W) ∣ S ∣ times ↦ (m * n :: W) ∣ S
  push-e  : ∀{w s}{n}{W : Vec _ w}{S : Vec _ s}
           --------------------------------
         → (n :: W) ∣ S ∣ push ↦ W ∣ (n :: S)
  pick-e  : ∀{w s}{x}{n}{W : Vec _ w}{S : Vec _ s}
         → S [ x ]= n
           ----------------------------
         → W ∣ S ∣ pick x ↦ (n :: W) ∣ S
  pop-e   : ∀{w s}{n}{W : Vec _ w}{S : Vec _ s}
           -------------------------
         → W ∣ (n :: S) ∣ pop ↦ W ∣ S

infixl 5 _∣_∣_⇓_∣_

data _∣_∣_⇓_∣_ {w s : Nat}(W : Vec Nat w)(S : Vec Nat s) : ∀{w′ s′}
  → SM w s w′ s′
  → Vec Nat w′ → Vec Nat s′
  → Set where

 halt-e : W ∣ S ∣ halt ⇓ W ∣ S

 _::_ : ∀{w′ s′ w″ s″}{i}{is}
     → {W′ : Vec Nat w′}{S′ : Vec Nat s′}
     → {W″ : Vec Nat w″}{S″ : Vec Nat s″}

     → W ∣ S ∣ i ↦ W′ ∣ S′
     → W′ ∣ S′ ∣ is ⇓ W″ ∣ S″
       --------------------------
     → W ∣ S ∣ (i :: is) ⇓ W″ ∣ S″

infixl 4 _⟦⊕⟧_
_⟦⊕⟧_ : ∀{w w′ w″ s s′ s″}{P}{Q}
     → {W : Vec Nat w}{S : Vec Nat s}
     → {W′ : Vec Nat w′}{S′ : Vec Nat s′}
     → {W″ : Vec Nat w″}{S″ : Vec Nat s″}

     → W ∣ S ∣ P ⇓ W′ ∣ S′
     → W′ ∣ S′ ∣ Q ⇓ W″ ∣ S″
       -------------------------
     → W ∣ S ∣ P ⊕ Q ⇓ W″ ∣ S″

halt-e ⟦⊕⟧ ys = ys
x :: xs ⟦⊕⟧ ys = x :: (xs ⟦⊕⟧ ys)

Sound : ∀{w s} → Term s → SM w s (suc w) s → Set
Sound {w} t u = ∀{v}{E}{W : Vec Nat w}
              → W ∣ E ∣ u ⇓ (v :: W) ∣ E
                -----------------------
              → E ⊢ t ⇓ v

Complete : ∀{w s} → Term s → SM w s (suc w) s → Set
Complete {w} t u = ∀{v}{E}{W : Vec Nat w}
                 → E ⊢ t ⇓ v
                   -----------------------
                 → W ∣ E ∣ u ⇓ (v :: W) ∣ E
