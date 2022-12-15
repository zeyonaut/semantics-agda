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
  using (zero ; suc) renaming (Nat to ℕ ; _+_ to _+ℕ_)

-- Integers.
data ℤ : Type where
  pos  : ℕ → ℤ
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
infix 0 _+_

-- Dependent pair types.
record Σ (B : Type ℓ₀) (F : B → Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁) where
  constructor
    _,_
  field
    π₀ : B
    π₁ : F π₀
open Σ public
infix 0 _,_
{-# BUILTIN SIGMA Σ #-}

∃ : {B : Type ℓ₀} (F : B → Type ℓ₁) → Type (ℓ₀ ⊔ ℓ₁)
∃ {B = B} F = Σ B F

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

open import Agda.Builtin.Maybe public
  using (Maybe) renaming (nothing to none ; just to some)

-- Decidability.
data _is-decidable (T : Type ℓ) : Type ℓ where
  yes : T   → T is-decidable
  no  : ¬ T → T is-decidable

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
infixr 10 _::_

_#_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A
(x :: v) # zero    = x
(x :: v) # (suc k) = v # k

_/_↦_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A → Vec A n
(x :: xs) / zero  ↦ x' = x' :: xs
(x :: xs) / suc k ↦ x' = x  :: (xs / k ↦ x')

_<_ : ℕ → ℕ → Type
_     < zero  = 𝟎
zero  < suc _ = 𝟏
suc a < suc b = a < b

<→F : {a b : ℕ} → a < b → Fin b
<→F {a = zero}  {b = suc b} p = zero
<→F {a = suc a} {b = suc b} p = suc (<→F p)

fin : (a : ℕ) {b : ℕ} {p : a < b} → Fin b
fin a {p = p} = <→F p

-- Operators for natural numbers and integers.
_+ℤ_ : (x : ℤ) → (y : ℤ) → ℤ
pos x +ℤ pos y = pos (x +ℕ y)
pos zero +ℤ nsuc y = nsuc y
pos (suc x) +ℤ nsuc zero = pos x
pos (suc x) +ℤ nsuc (suc y) = pos x +ℤ nsuc y
nsuc x +ℤ pos zero = nsuc x
nsuc zero +ℤ pos (suc y) = pos y
nsuc (suc x) +ℤ pos (suc y) = nsuc x +ℤ pos y
nsuc x +ℤ nsuc y = nsuc (suc (x +ℕ y))

≥Bℕ : (l r : ℕ) → Bool
≥Bℕ l       zero    = true
≥Bℕ zero    (suc r) = false
≥Bℕ (suc l) (suc r) = ≥Bℕ l r

_≥Bℤ_ : (l r : ℤ) → Bool
_≥Bℤ_ (pos a)  (pos b)  = ≥Bℕ a b
_≥Bℤ_ (pos a)  (nsuc b) = true
_≥Bℤ_ (nsuc a) (pos b)  = false
_≥Bℤ_ (nsuc a) (nsuc b) = ≥Bℕ b a