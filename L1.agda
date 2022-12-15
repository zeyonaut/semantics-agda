{-# OPTIONS --without-K --exact-split --safe #-}

module L1 where

open import Prelude

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

-- Values.
_is-value : {k : ℕ} (e : Ex k) → Type
(int: _)             is-value = 𝟏
(bool: _)            is-value = 𝟏
skip                 is-value = 𝟏
(_ op[ _ ] _)        is-value = 𝟎
(if _ then _ else _) is-value = 𝟎
(_ := _)             is-value = 𝟎
(^ _)                is-value = 𝟎
(_ ; _)              is-value = 𝟎
(while _ loop _)     is-value = 𝟎

-- Reduction steps.
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
    → ⟨ ^ l , s ─→ int: (s # l) , s ⟩
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

_is-reducible : {k : ℕ} → (es : Ex k × Store k) → Type
_is-reducible {k = k} (e , s) = Σ (Ex k × Store k) λ (e' , s') → ⟨ e , s ─→ e' , s' ⟩

-- Reduction chains.
data ⟨_,_─→*_,_⟩ {k : ℕ} : (e : Ex k) (s : Store k) (e' : Ex k) (s' : Store k) → Type where
  [] : (e : Ex k) (s : Store k)
    → ⟨ e , s ─→* e , s ⟩
  _::_ : {e e' e'' : Ex k} {s s' s'' : Store k}
    → (r : ⟨ e , s ─→ e' , s' ⟩) (r* : ⟨ e' , s' ─→* e'' , s'' ⟩)
    → ⟨ e , s ─→* e'' , s'' ⟩

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
    → (p : Γ # l ≡ ^int)
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
    → (p : Γ # l ≡ ^int) (t : Γ ⊢ e ⦂ int)
    → Γ ⊢ (l := e) ⦂ unit
  ty-while : {e₀ e₁ : Ex k}
    → (t₀ : Γ ⊢ e₀ ⦂ bool) (t₁ : Γ ⊢ e₁ ⦂ unit)
    → Γ ⊢ (while e₀ loop e₁) ⦂ unit
  ty-seq : {e₀ e₁ : Ex k} {T : Ty}
    → (t₀ : Γ ⊢ e₀ ⦂ unit) (t₁ : Γ ⊢ e₁ ⦂ T)
    → Γ ⊢ (e₀ ; e₁) ⦂ T

-- Ty has decidable equality.
_ty=?_ : (a b : Ty) → (a ≡ b) is-decidable
int  ty=? int  = yes (refl int)
int  ty=? bool = no λ ()
int  ty=? unit = no λ ()
bool ty=? int  = no λ ()
bool ty=? bool = yes (refl bool)
bool ty=? unit = no λ ()
unit ty=? int  = no λ ()
unit ty=? bool = no λ ()
unit ty=? unit = yes (refl unit)

-- Tyₗ has decidable equality.
_tyl=?_ : (a b : Tyₗ) → (a ≡ b) is-decidable
^int tyl=? ^int = yes (refl ^int)

-- Inversion helpers for typing judgements.
invert-op+ : {k : ℕ} {e₀ e₁ : Ex k} {T : Ty} {Γ : Ctx k}
  → (t : Γ ⊢ e₀ op[ o+ ] e₁ ⦂ T)
  → (Σ (Ex k) (Γ ⊢_⦂ int)) × (Σ (Ex k) (Γ ⊢_⦂ int))
invert-op+ {e₀ = e₀} _            .π₀ .π₀ = e₀
invert-op+           (ty-op+ t₀ _).π₀ .π₁ = t₀
invert-op+ {e₁ = e₁} _            .π₁ .π₀ = e₁
invert-op+           (ty-op+ _ t₁).π₁ .π₁ = t₁

invert-op≥ : {k : ℕ} {e₀ e₁ : Ex k} {T : Ty} {Γ : Ctx k}
  → (t : Γ ⊢ e₀ op[ o≥ ] e₁ ⦂ T)
  → (Σ (Ex k) (Γ ⊢_⦂ int)) × (Σ (Ex k) (Γ ⊢_⦂ int))
invert-op≥ {e₀ = e₀} _            .π₀ .π₀ = e₀
invert-op≥           (ty-op≥ t₀ _).π₀ .π₁ = t₀
invert-op≥ {e₁ = e₁} _            .π₁ .π₀ = e₁
invert-op≥           (ty-op≥ _ t₁).π₁ .π₁ = t₁

invert-if : {k : ℕ} {e₀ e₁ e₂ : Ex k} {T : Ty} {Γ : Ctx k}
  → (t : Γ ⊢ if e₀ then e₁ else e₂ ⦂ T)
  → (Σ (Ex k) (Γ ⊢_⦂ bool)) × (Σ (Ex k) (Γ ⊢_⦂ T)) × (Σ (Ex k) (Γ ⊢_⦂ T))
invert-if {e₀ = e₀} t             .π₀ .π₀ = e₀
invert-if           (ty-if t₀ _ _).π₀ .π₁ = t₀
invert-if {e₁ = e₁} t             .π₁ .π₀ = e₁
invert-if           (ty-if _ t₁ _).π₁ .π₁ = t₁
invert-if {e₂ = e₂} t             .π₂ .π₀ = e₂
invert-if           (ty-if _ _ t₂).π₂ .π₁ = t₂

invert-assign : {k : ℕ} {Γ : Ctx k} {l : Fin k} {e : Ex k} {T : Ty} 
  → (t : Γ ⊢ l := e ⦂ T)
  → (Γ # l ≡ ^int) × (Σ (Ex k) (Γ ⊢_⦂ int))
invert-assign         (ty-assign p _).π₀ = p
invert-assign {e = e} _              .π₁ .π₀ = e
invert-assign         (ty-assign _ t).π₁ .π₁ = t

invert-deref : {k : ℕ} {Γ : Ctx k} {l : Fin k} {T : Ty} 
  → (t : Γ ⊢ ^ l ⦂ T)
  → (Γ # l ≡ ^int)
invert-deref (ty-deref p) = p

invert-seq : {k : ℕ} {e₀ e₁ : Ex k} {T : Ty} {Γ : Ctx k}
  → (t : Γ ⊢ e₀ ; e₁ ⦂ T)
  → (Σ (Ex k) (Γ ⊢_⦂ unit)) × (Σ (Ex k) (Γ ⊢_⦂ T))
invert-seq {e₀ = e₀} _            .π₀ .π₀ = e₀
invert-seq           (ty-seq t₀ _).π₀ .π₁ = t₀
invert-seq {e₁ = e₁} _            .π₁ .π₀ = e₁
invert-seq           (ty-seq _ t₁).π₁ .π₁ = t₁

invert-while : {k : ℕ} {e₀ e₁ : Ex k} {T : Ty} {Γ : Ctx k}
  → (t : Γ ⊢ while e₀ loop e₁ ⦂ T)
  → (Σ (Ex k) (Γ ⊢_⦂ bool)) × (Σ (Ex k) (Γ ⊢_⦂ unit))
invert-while {e₀ = e₀} _              .π₀ .π₀ = e₀
invert-while           (ty-while t₀ _).π₀ .π₁ = t₀
invert-while {e₁ = e₁} _              .π₁ .π₀ = e₁
invert-while           (ty-while _ t₁).π₁ .π₁ = t₁