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
private variable ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

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

uncurry : {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
  → (A → B → C) → A × B → C
uncurry f (a , b) = f a b

const : {T : Type ℓ₁}
  → (S : Type ℓ₀) → T → (S → T)
const _ t s = t

_∘_ : {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
  → (A → B) → (B → C) → A → C
(f ∘ g) a = (g (f a))

open import Agda.Builtin.Maybe public
  using (Maybe) renaming (nothing to none ; just to some)

-- Generalized implication.
_═[_]⇒_ : {S : Type ℓ₀} {T : Type ℓ₁}
  → (D : S → Type ℓ₂) (R : S → T  → Type ℓ₃) (C : T → Type ℓ₄)
  → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
D ═[ R ]⇒ C = ∀ {s t} → R s t → D s → C t

_preserves_ : {T : Type ℓ₀}
  → (R : T → T → Type ℓ₁) (P : T → Type ℓ₂)
  → Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
R preserves P = P ═[ R ]⇒ P 
{-# INLINE _preserves_ #-}

record Map! {S : Type ℓ₀} {T : Type ℓ₁}
  (D : S → Type ℓ₂) (R : S → T  → Type ℓ₃) (C : T → Type ℓ₄)
  : Type (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄) where
  field
   map : D ═[ R ]⇒ C
  _$_ : ∀ {s t} → R s t → D s → C t
  m $ w = map m w
  _#_ : ∀ {s t} → D s → R s t → C t
  w # m = map m w

open Map! {{...}} using (_$_ ; _#_)

map! : {S : Type ℓ₀} {T : Type ℓ₁}
  (D : S → Type ℓ₂) (R : S → T  → Type ℓ₃) (C : T → Type ℓ₄)
  → D ═[ R ]⇒ C
  → Map! D R C
map! D R C convert .Map!.map = convert

map!-preserves : {T : Type ℓ₀}
    → (R : T → T → Type ℓ₁) (P : T → Type ℓ₂) (transport : R preserves P)
    → Map! P R P
map!-preserves R P transport .Map!.map = transport

map!-× : Map! (uncurry (_×_))
              (λ ((S₀ , S₁) : Type ℓ₀ × Type ℓ₁) ((T₀ , T₁) : Type ℓ₂ × Type ℓ₃) → (S₀ → T₀) × (S₁ → T₁))
              (uncurry (_×_))
map!-× .Map!.map (f₀ , f₁) (s₀ , s₁) = f₀ s₀ , f₁ s₁

-- Decidability.
data _is-decidable (T : Type ℓ) : Type ℓ where
  no  : ¬ T → T is-decidable
  yes :   T → T is-decidable

record Decide-Equality! (T : Type ℓ) : Type ℓ where
  constructor
    decide-equality!
  field
    _=?_ : (a  b : T) → (a ≡ b) is-decidable

-- Identifying properties. 
_is-identifying : {S : Type ℓ₀}
  → (F : S → Type ℓ₁)
  → Type (ℓ₀ ⊔ ℓ₁)
F is-identifying = ∀ {x y} → F x → F y → x ≡ y

-- Path operators.
sym : {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym (refl _) = refl _

_∙_ : {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl _ ∙ refl _ = refl _
infixr 7 _∙_

_ap_ : {A : Type ℓ₀} {B : Type ℓ₁} (f : A → B) → {x y : A} (p : x ≡ y) → f x ≡ f y
f ap refl a = refl (f a)

id : {T : Type ℓ} → T → T
id x = x

swap : {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
  → (A → B → C) → B → A → C
swap f b a = f a b

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

_$V_ : {A : Type} {n : ℕ} → Vec A n → Fin n → A
(x :: v) $V zero    = x
(x :: v) $V (suc k) = v $V k

map!-Vec = map! Fin (swap Vec) (id _) _$V_

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

-- Literal overloading
open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public

instance
  nat!-ℕ : Number ℕ
  nat!-ℕ .Number.Constraint _ = 𝟏
  nat!-ℕ .Number.fromNat    n = n

nat!-Fin : {k : ℕ} → Number (Fin k)
nat!-Fin {k = k} .Number.Constraint n         = n < k
nat!-Fin {k = k} .Number.fromNat    n {{n<k}} = fin n {k} {n<k}
nat!-ℤ : Number ℤ
nat!-ℤ .Number.Constraint _ = 𝟏
nat!-ℤ .Number.fromNat    n = pos n
neg!-ℤ : Negative ℤ
neg!-ℤ .Negative.Constraint _       = 𝟏
neg!-ℤ .Negative.fromNeg    zero    = pos zero
neg!-ℤ .Negative.fromNeg    (suc n) = nsuc n