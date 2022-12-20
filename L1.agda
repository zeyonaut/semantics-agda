{-# OPTIONS --without-K --exact-split --safe #-}

module L1 where

open import Prelude

open Map! {{...}} using (_$_)
instance _ = map!-Vec

-- Stores.
Store : (n : ℕ) → Type
Store n = Vec ℤ n

-- Operators.
data Op : Type where
  o+ : Op
  o≥ : Op

-- Expressions.
data Ex (k : ℕ) : Type where
  int: : (n : ℤ) → Ex k
  bool: : (n : Bool) → Ex k
  skip : Ex k
  _op[_]_ : (e₀ : Ex k) (o : Op) (e₁ : Ex k) → Ex k
  if_then_else_ : (e₀ e₁ e₂ : Ex k) → Ex k
  _:=_ : (l : Fin k) (e : Ex k) → Ex k
  ^ : (l : Fin k) → Ex k 
  _;_ : (e₀ e₁ : Ex k) → Ex k
  while_loop_ : (e₀ e₁ : Ex k) → Ex k

nat!-Ex : ∀ {k} → Number (Ex k)
nat!-Ex .Number.Constraint _ = 𝟏
nat!-Ex .Number.fromNat    n = int: (pos n)
neg!-Ex : ∀ {k} → Negative (Ex k)
neg!-Ex .Negative.Constraint _       = 𝟏
neg!-Ex .Negative.fromNeg    zero    = int: (pos zero)
neg!-Ex .Negative.fromNeg    (suc n) = int: (nsuc n)

-- Values.
_is-a-value : {k : ℕ} (e : Ex k) → Type
(int: _)             is-a-value = 𝟏
(bool: _)            is-a-value = 𝟏
skip                 is-a-value = 𝟏
(_ op[ _ ] _)        is-a-value = 𝟎
(if _ then _ else _) is-a-value = 𝟎
(_ := _)             is-a-value = 𝟎
(^ _)                is-a-value = 𝟎
(_ ; _)              is-a-value = 𝟎
(while _ loop _)     is-a-value = 𝟎

-- Single-step reduction.
data ⟨_,_─→_,_⟩ {k : ℕ} : (e : Ex k) (s : Store k) (e' : Ex k) (s' : Store k) → Type where
  op+-n : (n₀ n₁ : ℤ) (s : Store k)
    → ⟨ (int: n₀) op[ o+ ] (int: n₁) , s ─→ int: (n₀ +ℤ n₁) , s ⟩
  op≥-n : (n₀ n₁ : ℤ) (s : Store k)
    → ⟨ (int: n₀) op[ o≥ ] (int: n₁) , s ─→ bool: (n₀ ≥Bℤ n₁) , s ⟩
  op-r₀ : {e₀ e₀' : Ex k} {s s' : Store k}
    → (r₀ : ⟨ e₀ , s ─→ e₀' , s' ⟩) (o : Op) (e₁ : Ex k)
    → ⟨ e₀ op[ o ] e₁ , s ─→ e₀' op[ o ] e₁ , s' ⟩
  op-r₁ : {e₁ e₁' : Ex k} {s s' : Store k}
    → (n₀ : ℤ) (o : Op) (r₁ : ⟨ e₁ , s ─→ e₁' , s' ⟩)
    → ⟨ (int: n₀) op[ o ] e₁ , s ─→ (int: n₀) op[ o ] e₁' , s' ⟩
  deref : (l : Fin k) (s : Store k)
    → ⟨ ^ l , s ─→ int: (s $ l) , s ⟩
  assign-n : (l : Fin k) (n : ℤ) (s : Store k)
    → ⟨ l := (int: n) , s ─→ skip , s / l ↦ n ⟩ 
  assign-r : {e e' : Ex k} {s s' : Store k}
    → (l : Fin k) (r : ⟨ e , s ─→ e' , s' ⟩)
    → ⟨ l := e , s ─→ l := e' , s' ⟩
  seq-n : (e₁ : Ex k) (s : Store k)
    → ⟨ skip ; e₁ , s ─→ e₁ , s ⟩
  seq-r : {e₀ e₀' : Ex k} {s s' : Store k}
    → (r₀ : ⟨ e₀ , s ─→ e₀' , s' ⟩) (e₁ : Ex k)
    → ⟨ e₀ ; e₁ , s ─→ e₀' ; e₁ , s' ⟩
  if-n : (n₀ : Bool)  (e₁ e₂ : Ex k) (s : Store k)
    → ⟨ if (bool: n₀) then e₁ else e₂ , s ─→ Bool-if n₀ e₁ e₂ , s ⟩
  if-r : {e₀ e₀' : Ex k} {s s' : Store k}
    → (r₀ : ⟨ e₀ , s ─→ e₀' , s' ⟩) (e₁ e₂ : Ex k)
    → ⟨ if e₀ then e₁ else e₂ , s ─→ if e₀' then e₁ else e₂ , s' ⟩
  while : (e₀ e₁ : Ex k) (s : Store k)
    → ⟨ while e₀ loop e₁ , s ─→ if e₀ then (e₁ ; (while e₀ loop e₁)) else skip , s ⟩

_─→_ : {k : ℕ} → Ex k × Store k → Ex k × Store k → Type
(e , s) ─→ (e' , s') = ⟨ e , s ─→ e' , s' ⟩

-- Multi-step reduction.
data ⟨_,_─→*_,_⟩ {k : ℕ} : (e : Ex k) (s : Store k) (e' : Ex k) (s' : Store k) → Type where
  [] : (e : Ex k) (s : Store k)
    → ⟨ e , s ─→* e , s ⟩
  _::_ : {e e' e'' : Ex k} {s s' s'' : Store k}
    → (r : ⟨ e , s ─→ e' , s' ⟩) (r* : ⟨ e' , s' ─→* e'' , s'' ⟩)
    → ⟨ e , s ─→* e'' , s'' ⟩

_─→*_ : {k : ℕ} → Ex k × Store k → Ex k × Store k → Type
(e , s) ─→* (e' , s') = ⟨ e , s ─→* e' , s' ⟩

-- Expression types.
data Ty : Type where
  int bool unit : Ty

-- Reference types.
data Tyₗ : Type where
  ^int : Tyₗ

-- Contexts.
Ctx : (k : ℕ) → Type
Ctx k = Vec Tyₗ k

-- Typing judgements.
data _⊢_⦂_ {k : ℕ} (Γ : Ctx k) : (e : Ex k) (T : Ty) → Type where
  ty-int : (n : ℤ)
    → Γ ⊢ (int: n) ⦂ int
  ty-deref : {l : Fin k}
    → (p : Γ $ l ≡ ^int)
    → Γ ⊢ (^ l) ⦂ int
  ty-op+ : {e₀ e₁ : Ex k}
    → (t₀ : Γ ⊢ e₀ ⦂ int) (t₁ : Γ ⊢ e₁ ⦂ int)
    → Γ ⊢ (e₀ op[ o+ ] e₁) ⦂ int
  ty-bool : (b : Bool)
    → Γ ⊢ (bool: b) ⦂ bool
  ty-op≥ : {e₀ e₁ : Ex k}
    → (t₀ : Γ ⊢ e₀ ⦂ int) (t₁ : Γ ⊢ e₁ ⦂ int)
    → Γ ⊢ (e₀ op[ o≥ ] e₁) ⦂ bool
  ty-if : {e₀ e₁ e₂ : Ex k} {T : Ty}
    → (t₀ : Γ ⊢ e₀ ⦂ bool) (t₁ : Γ ⊢ e₁ ⦂ T) (t₂ : Γ ⊢ e₂ ⦂ T)
    → Γ ⊢ (if e₀ then e₁ else e₂) ⦂ T
  ty-skip : Γ ⊢ skip ⦂ unit
  ty-assign : {e : Ex k} {l : Fin k}
    → (p : Γ $ l ≡ ^int) (t : Γ ⊢ e ⦂ int)
    → Γ ⊢ (l := e) ⦂ unit
  ty-while : {e₀ e₁ : Ex k}
    → (t₀ : Γ ⊢ e₀ ⦂ bool) (t₁ : Γ ⊢ e₁ ⦂ unit)
    → Γ ⊢ (while e₀ loop e₁) ⦂ unit
  ty-seq : {e₀ e₁ : Ex k} {T : Ty}
    → (t₀ : Γ ⊢ e₀ ⦂ unit) (t₁ : Γ ⊢ e₁ ⦂ T)
    → Γ ⊢ (e₀ ; e₁) ⦂ T