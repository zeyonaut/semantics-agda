{-# OPTIONS --without-K --exact-split --safe  #-}

module L1Properties where

open import Prelude
open import L1

private variable
  ℓ ℓ₀ ℓ₁ ℓ₂ : Level

-- Enable equality decision syntax.
open Decide-Equality! {{...}} using (_=?_)
private instance
  _ = decide-equality!-Ty
  _ = decide-equality!-Tyₗ

-- Enable map application syntax.
open Map! {{...}} using (map ; _$_ ; _#_)
private instance
  _ = map!-Vec
  _ = map!-×

-- Theorem (Determinacy):
-- Any reduction steps with the same source have equal targets.
identify-targets : {k : ℕ} {e : Ex k} {s : Store k}
  → ((e , s) ─→_) is-identifying
identify-targets (op+-n n₀ n₁ s   ) (op+-n .n₀ .n₁ .s)   = refl (int:  (n₀ +ℤ n₁)  , s)
identify-targets (op≥-n n₀ n₁ s   ) (op≥-n .n₀ .n₁ .s)   = refl (bool: (n₀ ≥Bℤ n₁) , s)
identify-targets (op-r₀ r₀ o e₁   ) (op-r₀ r₀' .o .e₁)   = map (       _op[ o ] e₁ , id) ap identify-targets r₀ r₀'
identify-targets (op-r₁ n₀ o r₁   ) (op-r₁ .n₀ .o r₁')   = map (int: n₀ op[ o ]_   , id) ap identify-targets r₁ r₁'
identify-targets (deref l s       ) (deref .l s)         = refl (int: (s $ l)      , s)
identify-targets (assign-n l n s  ) (assign-n .l .n s)   = refl (skip              , s / l ↦ n)
identify-targets (assign-r l r₀   ) (assign-r .l r₀')    = map (l :=_              , id) ap identify-targets r₀ r₀'
identify-targets (seq-n e₁ s      ) (seq-n .e₁ .s)       = refl (e₁                , s)
identify-targets (seq-r r₀ e₁     ) (seq-r r₀' .e₁)      = map (_; e₁              , id) ap identify-targets r₀ r₀'
identify-targets (if-n n₀ e₁ e₂ s ) (if-n .n₀ .e₁ .e₂ s) = refl (Bool-if n₀ e₁ e₂  , s)
identify-targets (if-r r₀ e₁ e₂   ) (if-r r₀' .e₁ .e₂)   = map (if_then e₁ else e₂ , id) ap identify-targets r₀ r₀'
identify-targets (while e₀ e₁ s   ) (while .e₀ .e₁ .s)   = refl (if e₀ then e₁ ; (while e₀ loop e₁) else skip , s)

-- Theorem (Progress):
-- Any well-typed expression in any store is a value or is reducible.
progress : {k : ℕ} {Γ : Ctx k} {e : Ex k} {T : Ty}
         → (t : Γ ⊢ e ⦂ T) (s : Store k)
         → e is-a-value + (e , s) is-reducible
progress                    (ty-int n)           s = in₀ ⋆
progress                    (ty-deref {l = l} p) s = in₁ ((int: (s $ l) , s) , deref l s)
progress {e = _ op[ _ ] e₁} (ty-op+ t₀ t₁)       s
  with progress t₀ s | progress t₁ s | t₀ | t₁
... | in₀ ⋆                 | in₀ ⋆                 | ty-int n₀ | ty-int n₁ = in₁ ((int: (n₀ +ℤ n₁)      , s)  , op+-n n₀ n₁ s)
... | in₀ ⋆                 | in₁ ((e₁' , s') , r₁) | ty-int n₀ | _         = in₁ ((int: n₀ op[ o+ ] e₁' , s') , op-r₁ n₀ o+ r₁)
... | in₁ ((e₀' , s') , r₀) | _                     | _         | _         = in₁ ((e₀'     op[ o+ ] e₁  , s') , op-r₀ r₀ o+ e₁)
progress                    (ty-bool b)     s = in₀ ⋆
progress {e = _ op[ _ ] e₁} (ty-op≥ t₀ t₁) s
  with progress t₀ s | progress t₁ s | t₀ | t₁
... | in₀ ⋆                 | in₀ ⋆                 | ty-int n₀ | ty-int n₁ = in₁ ((bool: (n₀ ≥Bℤ n₁)    , s)  , op≥-n n₀ n₁ s)
... | in₀ ⋆                 | in₁ ((e₁' , s') , r₁) | ty-int n₀ | _         = in₁ ((int: n₀ op[ o≥ ] e₁' , s') , op-r₁ n₀ o≥ r₁)
... | in₁ ((e₀' , s') , r₀) | _                     | _         | _         = in₁ ((e₀'     op[ o≥ ] e₁  , s') , op-r₀ r₀ o≥ e₁)
progress {e = if _ then e₁ else e₂} (ty-if t₀ _ _) s
  with progress t₀ s | t₀
... | in₀ x                | ty-bool n = in₁ ((Bool-if n e₁ e₂       , s)   , if-n n e₁ e₂ s) 
... | in₁ ((e₀' , s') , r) | _         = in₁ ((if e₀' then e₁ else e₂ , s') , if-r r e₁ e₂)
progress ty-skip                 s = in₀ ⋆
progress (ty-assign {l = l} p t) s
  with progress t s | t
... | in₀ ⋆               | ty-int n = in₁ ((skip    , (s / l ↦ n)) , assign-n l n s)
... | in₁ ((e' , s') , r) | _        = in₁ ((l := e' , s')          , assign-r l r)
progress {e = while e₀ loop e₁} (ty-while _ _) s = in₁ ((if e₀ then (e₁ ; (while e₀ loop e₁)) else skip , s), while e₀ e₁ s)
progress {e = e₀ ; e₁}          (ty-seq t₀ t₁) s
  with progress t₀ s | t₀
... | in₀ ⋆                | ty-skip = in₁ ((e₁       , s)  , seq-n e₁ s)
... | in₁ ((e₀' , s') , r) | _       = in₁ ((e₀' ; e₁ , s') , seq-r r e₁)

-- Theorem (Type Preservation):
-- Single-step reduction preserves typing judgements.
transport-step : {k : ℕ} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (⟨_, s ─→_, s' ⟩) preserves (Γ ⊢_⦂ T)
transport-step (op+-n n₀ n₁ _)    (ty-op+ _ _)     = ty-int (n₀ +ℤ n₁)
transport-step (op≥-n n₀ n₁ _)    (ty-op≥ _ _)     = ty-bool (n₀ ≥Bℤ n₁)
transport-step (op-r₀ r₀ .o+ _)   (ty-op+ t₀ t₁)   = ty-op+ (transport-step r₀ t₀) t₁
transport-step (op-r₀ r₀ .o≥ _)   (ty-op≥ t₀ t₁)   = ty-op≥ (transport-step r₀ t₀) t₁
transport-step (op-r₁ _ .o+ r₁)   (ty-op+ t₀ t₁)   = ty-op+ t₀ (transport-step r₁ t₁)
transport-step (op-r₁ _ .o≥ r₁)   (ty-op≥ t₀ t₁)   = ty-op≥ t₀ (transport-step r₁ t₁)
transport-step (deref l s)        (ty-deref _)     = ty-int (s $ l)
transport-step (assign-n _ _ _)   (ty-assign _ _)  = ty-skip
transport-step (assign-r _ r)     (ty-assign p t)  = ty-assign p (transport-step r t)
transport-step (seq-n _ _)        (ty-seq _ t₁)    = t₁
transport-step (seq-r r₀ _)       (ty-seq t₀ t₁)   = ty-seq (transport-step r₀ t₀) t₁
transport-step (if-n true _ _ _)  (ty-if _ t₁ _)   = t₁
transport-step (if-n false _ _ _) (ty-if _ _ t₂)   = t₂
transport-step (if-r r₀ _ _)      (ty-if t₀ t₁ t₂) = ty-if (transport-step r₀ t₀) t₁ t₂
transport-step (while _ _ _)      (ty-while t₀ t₁) = ty-if t₀ (ty-seq t₁ (ty-while t₀ t₁)) ty-skip

-- Enable application of reduction steps to typing derivations.
map!-Reduction-Step = λ {k} {s : Store k} {s'} {Γ} {T} → map!-preserves (⟨_, s ─→_, s' ⟩) (Γ ⊢_⦂ T) transport-step
private instance _ = map!-Reduction-Step
  
-- Theorem (Multi-step Type Preservation):
-- Multi-step reduction preserves typing judgements.
transport-chain : {k : ℕ} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (⟨_, s ─→*_, s' ⟩) preserves (Γ ⊢_⦂ T)
transport-chain ([] _ _)  t = t 
transport-chain (r :: r*) t = transport-chain r* (t # r)

-- Enable application of reduction chains to typing derivations.
map!-Reduction-Chain = λ {k} {s : Store k} {s'} {Γ} {T} → map!-preserves (⟨_, s ─→*_, s' ⟩) (Γ ⊢_⦂ T) transport-chain
private instance _ = map!-Reduction-Chain

-- Theorem (Type Safety):
-- Any reduction chain with a well-typed source has a target which is a value or is reducible.
safety : {k : ℕ} {e e' : Ex k} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (r* : ⟨ e , s ─→* e' , s' ⟩) (t : Γ ⊢ e ⦂ T)
  → e' is-a-value + (e' , s') is-reducible
safety {s' = s'} r* t = progress (t # r*) s'

-- Theorem (Uniqueness of Typing):
-- Any typing derivations with the same context and expression have equal types.
identify-types : {k : ℕ} {Γ : Ctx k} {e : Ex k}
  → (Γ ⊢ e ⦂_) is-identifying
identify-types (ty-int _)      (ty-int _)      = refl int
identify-types (ty-deref _)    (ty-deref _)    = refl int
identify-types (ty-op+ _ _)    (ty-op+ _ _)    = refl int
identify-types (ty-bool _)     (ty-bool _)     = refl bool
identify-types (ty-op≥ _ _)    (ty-op≥ _ _)    = refl bool
identify-types (ty-if _ t₁ _)  (ty-if _ u₁ _)  = identify-types t₁ u₁
identify-types ty-skip         ty-skip         = refl unit
identify-types (ty-assign _ _) (ty-assign _ _) = refl unit
identify-types (ty-while _ _)  (ty-while _ _)  = refl unit
identify-types (ty-seq _ t₁)   (ty-seq _ u₁)   = identify-types t₁ u₁

-- Theorem (Type Inference):
-- For any context and expression, the existence of an assignable type is decidable.
_⊢_⦂…∃? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k)
  → (∃ (Γ ⊢ e ⦂_)) is-decidable
Γ ⊢ (int: n)         ⦂…∃? = yes (int  , ty-int n)
Γ ⊢ (bool: n)        ⦂…∃? = yes (bool , ty-bool n)
Γ ⊢ skip             ⦂…∃? = yes (unit , ty-skip)
Γ ⊢ (e₀ op[ o+ ] e₁) ⦂…∃?
  with Γ ⊢ e₀ ⦂…∃? | Γ ⊢ e₁ ⦂…∃?
... | no  ¬∃₀       | _             = no λ (_ , t) → ¬∃₀ (int , invert-ty t .π₀)
... | yes _         | no  ¬∃₁       = no λ (_ , t) → ¬∃₁ (int , invert-ty t .π₁)
... | yes (T₀ , t₀) | yes (T₁ , t₁)
  with T₀ =? int | T₁ =? int
... | no  T₀≠int      | _               = no  λ (_ , t) → T₀≠int (identify-types t₀ (invert-ty t .π₀))
... | yes _           | no  T₁≠int      = no  λ (_ , t) → T₁≠int (identify-types t₁ (invert-ty t .π₁))
... | yes (refl .int) | yes (refl .int) = yes (int , ty-op+ t₀ t₁)
Γ ⊢ (e₀ op[ o≥ ] e₁) ⦂…∃? 
  with Γ ⊢ e₀ ⦂…∃? | Γ ⊢ e₁ ⦂…∃?
... | no  ¬∃₀       | _             = no λ (_ , t) → ¬∃₀ (int , invert-ty t .π₀)
... | yes _         | no ¬∃₁        = no λ (_ , t) → ¬∃₁ (int , invert-ty t .π₁)
... | yes (T₀ , t₀) | yes (T₁ , t₁)
  with T₀ =? int | T₁ =? int
... | no  T₀≠int      | _               = no  λ (_ , t) → T₀≠int (identify-types t₀ (invert-ty t .π₀))
... | yes _           | no  T₁≠int      = no  λ (_ , t) → T₁≠int (identify-types t₁ (invert-ty t .π₁))
... | yes (refl .int) | yes (refl .int) = yes (bool , ty-op≥ t₀ t₁)
Γ ⊢ (if e₀ then e₁ else e₂) ⦂…∃?
  with Γ ⊢ e₀ ⦂…∃? | Γ ⊢ e₁ ⦂…∃? | Γ ⊢ e₂ ⦂…∃?
... | no  ¬∃₀       | _             | _             = no λ (_ , t) → ¬∃₀ (bool , (invert-ty t .π₀))
... | yes _         | no  ¬∃₁       | _             = no λ (T , t) → ¬∃₁ (T    , (invert-ty t .π₁))
... | yes _         | yes _         | no  ¬∃₂       = no λ (T , t) → ¬∃₂ (T    , (invert-ty t .π₂))
... | yes (T₀ , t₀) | yes (T₁ , t₁) | yes (T₂ , t₂)
  with T₀ =? bool | T₁ =? T₂
... | no  T₀≠bool      | _              = no  λ (_ , t) → T₀≠bool (identify-types t₀ (invert-ty t .π₀))
... | yes _            | no  T₁≠T₂      = no  λ (_ , t) → T₁≠T₂ (identify-types t₁ (invert-ty t .π₁) ∙ identify-types (invert-ty t .π₂) t₂)
... | yes (refl .bool) | yes (refl .T₁) = yes (T₁ , ty-if t₀ t₁ t₂)
Γ ⊢ (l := e) ⦂…∃?
  with Γ ⊢ e ⦂…∃?
... | no  ¬∃        = no  λ (T , t) → ¬∃ (int , invert-ty t .π₁)
... | yes (T₀ , t₀)
  with (Γ $ l) =? ^int | T₀ =? int
... | no  Γ$l≠^int | _               = no  λ (_ , t) → Γ$l≠^int (invert-ty t .π₀)
... | yes _        | no T₀≠int       = no  λ (_ , t) → T₀≠int (identify-types t₀ (invert-ty t .π₁))
... | yes Γ$l=^int | yes (refl .int) = yes (unit , ty-assign Γ$l=^int t₀)
Γ ⊢ (^ l) ⦂…∃?
  with (Γ $ l) =? ^int
... | no  Γ$l≠^int = no  λ (T , t) → Γ$l≠^int (invert-ty t)
... | yes Γ$l=^int = yes (int , ty-deref Γ$l=^int)
Γ ⊢ (e₀ ; e₁) ⦂…∃?
  with Γ ⊢ e₀ ⦂…∃? | Γ ⊢ e₁ ⦂…∃?
... | no  ¬∃₀       | _             = no  λ (_ , t) → ¬∃₀ (unit , invert-ty t .π₀)
... | yes _         | no  ¬∃₁       = no  λ (T , t) → ¬∃₁ (T    , invert-ty t .π₁)
... | yes (T₀ , t₀) | yes (T₁ , t₁)
  with T₀ =? unit
... | no  T₀≠unit      = no  λ (_ , t) → T₀≠unit (identify-types t₀ (invert-ty t .π₀))
... | yes (refl .unit) = yes (T₁ , ty-seq t₀ t₁)
Γ ⊢ (while e₀ loop e₁) ⦂…∃?
  with Γ ⊢ e₀ ⦂…∃? | Γ ⊢ e₁ ⦂…∃?
... | no  ¬∃₀       | _             = no  λ (_ , t) → ¬∃₀ (bool , invert-ty t .π₀)
... | yes _         | no  ¬∃₁       = no  λ (_ , t) → ¬∃₁ (unit , invert-ty t .π₁)
... | yes (T₀ , t₀) | yes (T₁ , t₁)
  with T₀ =? bool | T₁ =? unit
... | no  T₀≠bool      | _                = no  λ (_ , t) → T₀≠bool (identify-types t₀ (invert-ty t .π₀))
... | yes _            | no  T₁≠unit      = no  λ (_ , t) → T₁≠unit (identify-types t₁ (invert-ty t .π₁))
... | yes (refl .bool) | yes (refl .unit) = yes (unit , ty-while t₀ t₁)

-- Theorem (Decidability of Typing Judgements):
-- Any typing judgement is decidable.
_⊢?_⦂_ : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (T : Ty)
  → (Γ ⊢ e ⦂ T) is-decidable
Γ ⊢? e ⦂ T
  with Γ ⊢ e ⦂…∃?
... | no  ¬∃        = no λ t → ¬∃ (T , t)
... | yes (T' , t')
  with T =? T'
... | no  T≠T'       = no  λ t → T≠T' (identify-types t t')
... | yes (refl .T') = yes t'

-- Values are irreducible in any store.
value→irreducible : {k : ℕ} {e : Ex k}
  → (v : e is-a-value) (s : Store k)
  → ¬ ((e , s) is-reducible)
value→irreducible () s ((.(int: (n₀ +ℤ n₁)) , .s) , op+-n n₀ n₁ .s)
value→irreducible () s ((.(bool: (n₀ ≥Bℤ n₁)) , .s) , op≥-n n₀ n₁ .s)
value→irreducible () s ((.(_ op[ o ] e₁) , _) , op-r₀ r o e₁)
value→irreducible () s ((.(int: n₀ op[ o ] _) , _) , op-r₁ n₀ o r)
value→irreducible () s ((.(int: (s $ l)) , .s) , deref l .s)
value→irreducible () s ((.skip , .(s / l ↦ n)) , assign-n l n .s)
value→irreducible () s ((.(l := _) , _) , assign-r l r)
value→irreducible () .(π₁ es') (es' , seq-n .(π₀ es') .(π₁ es'))
value→irreducible () s ((.(_ ; e₁) , _) , seq-r _ e₁)
value→irreducible () s ((.(Bool-if n₀ e₁ e₂) , .s) , if-n n₀ e₁ e₂ .s)
value→irreducible () s ((.(if _ then e₁ else e₂) , _) , if-r _ e₁ e₂)
value→irreducible () s ((.(if e₀ then e₁ ; (while e₀ loop e₁) else skip) , .s) , while e₀ e₁ .s)

-- Evaluation.
evaluate : {k : ℕ} {Γ : Ctx k} {e : Ex k} {T : Ty}
  → (t : Γ ⊢ e ⦂ T) (s : Store k) (depth : ℕ)
  → Maybe (Σ (Ex k × Store k) λ (e' , s') → ⟨ e , s ─→* e' , s' ⟩)
evaluate {e = e} _ s zero = some ((e , s), [] e s) 
evaluate {e = e} t s (suc depth)
  with progress t s
... | in₀ v               = some ((e , s) , [] e s)
... | in₁ ((e' , s') , r)
  with evaluate (t # r) s' depth
... | some ((e'' , s'') , r*) = some ((e'' , s'') , r :: r*)
... | none                    = none

-- Type inference and evaluation.
ty? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k)
  → Maybe Ty
ty? Γ e with Γ ⊢ e ⦂…∃?
... | no  _       = none
... | yes (T , _) = some T

ev? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (s : Store k) (depth : ℕ)
  → Maybe (Ex k × Store k)
ev? Γ e s depth
  with Γ ⊢ e ⦂…∃?
... | no  _       = none
... | yes (_ , t)
  with evaluate t s depth
... | none           = none
... | some (es' , _) = some es'

step? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (s : Store k)
  → Maybe (Ex k × Store k)
step? Γ e s
  with Γ ⊢ e ⦂…∃?
... | no  _       = none
... | yes (_ , t)
  with progress t s
... | in₀ _         = none
... | in₁ (es' , _) = some es'