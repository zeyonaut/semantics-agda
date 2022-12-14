{-# OPTIONS --without-K --exact-split --safe #-}

module Prelude where

open import Agda.Primitive public
  using    ( Level
           ; SSet
           ; lzero
           ; lsuc
           ; _⊔_)
  renaming ( Set to Type )

-- Implicit level parameters for convenience.
private variable ℓ ℓ₀ ℓ₁ ℓ₂ : Level

-- Zero type.
data 𝟎 : Type where

-- Unit type.
open import Agda.Builtin.Unit public
  renaming (tt to ⋆ ; ⊤ to 𝟏)

-- Booleans.
open import Agda.Builtin.Bool public

-- Natural numbers.
open import Agda.Builtin.Nat public
  using (zero ; suc ; _<_) renaming (Nat to ℕ ; _+_ to _+ℕ_)

-- Integers.
data ℤ : Type where
  posi : ℕ → ℤ
  nsuc : ℕ → ℤ
  
-- Paths.
data _≡_ {A : Type ℓ} : A → A → Type ℓ where
  refl : (x : A) → x ≡ x
infix 0 _≡_

{-# BUILTIN EQUALITY _≡_  #-}

-- Coproduct types.
data _+_ (L : Type ℓ₀) (R : Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁) where
  in₀ : L → (L + R)
  in₁ : R → (L + R)

-- Dependent pair types.
record Σ (B : Type ℓ₀) (F : B → Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁) where
  constructor
    _,_
  field
    πₗ : B
    πᵣ : F πₗ
open Σ public
infix 0 _,_

{-# BUILTIN SIGMA Σ #-}

-- Product types.
_×_ : Type ℓ₀ → Type ℓ₁ → Type (ℓ₀ ⊔ ℓ₁)
L × R = Σ L λ _ → R

-- 3-ary product types.
record _×_×_ (T₀ : Type ℓ₀) (T₁ : Type ℓ₁) (T₂ : Type ℓ₂) : Type (ℓ₀ ⊔ (ℓ₁ ⊔ ℓ₂)) where
  constructor
    _,_,_
  field
    π₀ : T₀
    π₁ : T₁
    π₂ : T₂
open _×_×_ public
infix 0 _,_,_

-- Negation and inequality.
¬ : Type ℓ → Type ℓ
¬ T = T → 𝟎

_≠_ : {A : Type ℓ} (x y : A) → Type ℓ
x ≠ y = (x ≡ y) → 𝟎 

-- Decidability.
_is-decidable : Type ℓ → Type ℓ
T is-decidable = T + (¬ T) 

-- Path operators.
sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym (refl _) = refl _

_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl _ ∙ refl _ = refl _
infixr 7 _∙_

_ap_ : {A : Type ℓ₀} {B : Type ℓ₁} (f : A → B) → {x y : A} (p : x ≡ y) → f x ≡ f y
f ap refl a = refl (f a)

-- Bool recursor.
Bool-if : {T : Type} → (b : Bool) → (t f : T) → T
Bool-if true  t f = t
Bool-if false t f = f

-- Finite sets, vectors, and vector operators.
data Fin : (n : ℕ) → Type where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

data Vec (A : Type) : (n : ℕ) → Type where
  [] : Vec A zero
  _::_ : {n : ℕ} (x : A) (xs : Vec A n) → Vec A (suc n)

_#_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A
(x :: v) # zero    = x
(x :: v) # (suc k) = v # k

_/_↦_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A → Vec A n
(x :: xs) / zero  ↦ x' = x' :: xs
(x :: xs) / suc k ↦ x' = x  :: (xs / k ↦ x')

-- Operators for natural numbers and integers.
_+ℤ_ : (x : ℤ) → (y : ℤ) → ℤ
posi x +ℤ posi y = posi (x +ℕ y)
posi zero +ℤ nsuc y = nsuc y
posi (suc x) +ℤ nsuc zero = posi x
posi (suc x) +ℤ nsuc (suc y) = posi x +ℤ nsuc y
nsuc x +ℤ posi zero = nsuc x
nsuc zero +ℤ posi (suc y) = posi y
nsuc (suc x) +ℤ posi (suc y) = nsuc x +ℤ posi y
nsuc x +ℤ nsuc y = nsuc (suc (x +ℕ y))

≥Bℕ : (l r : ℕ) → Bool
≥Bℕ zero r = true
≥Bℕ (suc l) zero = false
≥Bℕ (suc l) (suc r) = ≥Bℕ l r

_≥Bℤ_ : (l r : ℤ) → Bool
_≥Bℤ_ (posi a) (posi b) = ≥Bℕ a b
_≥Bℤ_ (posi a) (nsuc b) = true
_≥Bℤ_ (nsuc a) (posi b) = false
_≥Bℤ_ (nsuc a) (nsuc b) = ≥Bℕ b a