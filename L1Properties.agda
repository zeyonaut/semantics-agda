{-# OPTIONS --without-K --exact-split --safe  #-}

module L1Properties where

open import Prelude
open import L1

-- Theorem (Determinacy):
-- Any two reduction steps with the same initial pair have equal final pairs.
determinacy : {k : ℕ} {e e₀ e₁ : Ex k} {s s₀ s₁ : Store k}
  → (r : ⟨ e , s ─→ e₀ , s₀ ⟩) (r' : ⟨ e , s ─→ e₁ , s₁ ⟩)
  → (e₀ ≡ e₁) × (s₀ ≡ s₁)
determinacy (op+-n n₀ n₁ s)   (op+-n .n₀ .n₁ .s)   = refl (int! (n₀ +ℤ n₁))                              , refl s
determinacy (op≥-n n₀ n₁ s)   (op≥-n .n₀ .n₁ .s)   = refl (bool! (n₀ ≥Bℤ n₁))                            , refl s
determinacy (op-r₀ r₀ o e₁)   (op-r₀ r₀' .o .e₁)   = (_op[ o ] e₁)        ap determinacy r₀ r₀' .πₗ      , determinacy r₀ r₀' .πᵣ
determinacy (op-r₁ n₀ o r₁)   (op-r₁ .n₀ .o r₁')   = ((int! n₀) op[ o ]_) ap determinacy r₁ r₁' .πₗ      , determinacy r₁ r₁' .πᵣ
determinacy (deref l s)       (deref .l s)         = refl (int! (s # l))                                 , refl s
determinacy (assign-n l n s)  (assign-n .l .n s)   = refl skip                                           , refl (s / l ↦ n)
determinacy (assign-r l r₀)   (assign-r .l r₀')    = (l :=_)              ap determinacy r₀ r₀' .πₗ      , determinacy r₀ r₀' .πᵣ
determinacy (seq-n e₁ s)      (seq-n .e₁ .s)       = refl e₁                                             , refl s
determinacy (seq-r r₀ e₁)     (seq-r r₀' .e₁)      = (_; e₁)              ap determinacy r₀ r₀' .πₗ      , determinacy r₀ r₀' .πᵣ
determinacy (if-n n₀ e₁ e₂ s) (if-n .n₀ .e₁ .e₂ s) = refl (Bool-if n₀ e₁ e₂)                             , refl s
determinacy (if-r r₀ e₁ e₂)   (if-r r₀' .e₁ .e₂)   = (if_then e₁ else e₂) ap determinacy r₀ r₀' .πₗ      , determinacy r₀ r₀' .πᵣ
determinacy (while e₀ e₁ s)   (while .e₀ .e₁ .s)   = refl (if e₀ then e₁ ; (while e₀ loop e₁) else skip) , refl s

-- Theorem (Progress):
-- A well-typed expression is a value or is reducible with any store.
progress : {k : ℕ} {Γ : Ctx k} {e : Ex k} {T : Ty}
         → (t : Γ ⊢ e ⦂ T) (s : Store k)
         → e is-value + (e , s) is-reducible
progress                    (ty-int n)           s = in₀ ⋆
progress                    (ty-deref {l = l} p) s = in₁ ((int! (s # l) , s) , deref l s)
progress {e = _ op[ _ ] e₁} (ty-op+ t₀ t₁)       s
  with progress t₀ s | progress t₁ s | t₀ | t₁
... | in₀ ⋆                 | in₀ ⋆                 | ty-int n₀ | ty-int n₁ = in₁ ((int! (n₀ +ℤ n₁)      , s)  , op+-n n₀ n₁ s)
... | in₀ ⋆                 | in₁ ((e₁' , s') , r₁) | ty-int n₀ | _         = in₁ ((int! n₀ op[ o+ ] e₁' , s') , op-r₁ n₀ o+ r₁)
... | in₁ ((e₀' , s') , r₀) | _                     | _         | _         = in₁ ((e₀'     op[ o+ ] e₁  , s') , op-r₀ r₀ o+ e₁)
progress                    (ty-bool b)     s = in₀ ⋆
progress {e = _ op[ _ ] e₁} (ty-op≥ t₀ t₁) s
  with progress t₀ s | progress t₁ s | t₀ | t₁
... | in₀ ⋆                 | in₀ ⋆                 | ty-int n₀ | ty-int n₁ = in₁ ((bool! (n₀ ≥Bℤ n₁)    , s)  , op≥-n n₀ n₁ s)
... | in₀ ⋆                 | in₁ ((e₁' , s') , r₁) | ty-int n₀ | _         = in₁ ((int! n₀ op[ o≥ ] e₁' , s') , op-r₁ n₀ o≥ r₁)
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
-- Any reduction step with a well-typed initial expression has a well-typed final expression.
preserve : {k : ℕ} {e e' : Ex k} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (r : ⟨ e , s ─→ e' , s' ⟩) (t : Γ ⊢ e ⦂ T)
  → (Γ ⊢ e' ⦂ T)
preserve (op+-n n₀ n₁ _)    (ty-op+ _ _)     = ty-int (n₀ +ℤ n₁)
preserve (op≥-n n₀ n₁ _)    (ty-op≥ _ _)     = ty-bool (n₀ ≥Bℤ n₁)
preserve (op-r₀ r₀ .o+ _)   (ty-op+ t₀ t₁)   = ty-op+ (preserve r₀ t₀) t₁
preserve (op-r₀ r₀ .o≥ _)   (ty-op≥ t₀ t₁)   = ty-op≥ (preserve r₀ t₀) t₁
preserve (op-r₁ _ .o+ r₁)   (ty-op+ t₀ t₁)   = ty-op+ t₀ (preserve r₁ t₁)
preserve (op-r₁ _ .o≥ r₁)   (ty-op≥ t₀ t₁)   = ty-op≥ t₀ (preserve r₁ t₁)
preserve (deref l s)        (ty-deref _)     = ty-int (s # l)
preserve (assign-n _ _ _)   (ty-assign _ _)  = ty-skip
preserve (assign-r _ r)     (ty-assign p t)  = ty-assign p (preserve r t)
preserve (seq-n _ _)        (ty-seq _ t₁)    = t₁
preserve (seq-r r₀ _)       (ty-seq t₀ t₁)   = ty-seq (preserve r₀ t₀) t₁
preserve (if-n true _ _ _)  (ty-if _ t₁ _)   = t₁
preserve (if-n false _ _ _) (ty-if _ _ t₂)   = t₂
preserve (if-r r₀ _ _)      (ty-if t₀ t₁ t₂) = ty-if (preserve r₀ t₀) t₁ t₂
preserve (while _ _ _)      (ty-while t₀ t₁) = ty-if t₀ (ty-seq t₁ (ty-while t₀ t₁)) ty-skip

-- Corollary (Type Preservation for Reduction Chains):
-- Any reduction chain with a well-typed initial expression has a well-typed final expression.
preserve* : {k : ℕ} {e e' : Ex k} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (r* : ⟨ e , s ─→* e' , s' ⟩) (t : Γ ⊢ e ⦂ T)
  → (Γ ⊢ e' ⦂ T)
preserve* ([] _ _) t = t
preserve* (r :: r*) t = preserve* r* (preserve r t)

-- Theorem (Type Safety):
-- Any reduction chain with a well-typed initial expression has a final expression which is a value or has a final pair which is reducible.
safety : {k : ℕ} {e e' : Ex k} {s s' : Store k} {Γ : Ctx k} {T : Ty}
  → (r* : ⟨ e , s ─→* e' , s' ⟩) (t : Γ ⊢ e ⦂ T)
  → e' is-value + (e' , s') is-reducible
safety {s' = s'} r* t = progress (preserve* r* t) s'

-- Theorem (Uniqueness of Typing):
-- Any two typing judgements with the same context and expression have equal types.
uniqueness : {k : ℕ} {Γ : Ctx k} {T U : Ty} {e : Ex k}
  → (t : Γ ⊢ e ⦂ T) (u : Γ ⊢ e ⦂ U)
  → (T ≡ U)
uniqueness (ty-int _)      (ty-int _)      = refl int
uniqueness (ty-deref _)    (ty-deref _)    = refl int
uniqueness (ty-op+ _ _)    (ty-op+ _ _)    = refl int
uniqueness (ty-bool _)     (ty-bool _)     = refl bool
uniqueness (ty-op≥ _ _)    (ty-op≥ _ _)    = refl bool
uniqueness (ty-if _ t₁ _)  (ty-if _ u₁ _)  = uniqueness t₁ u₁
uniqueness ty-skip         ty-skip         = refl unit
uniqueness (ty-assign _ _) (ty-assign _ _) = refl unit
uniqueness (ty-while _ _)  (ty-while _ _)  = refl unit
uniqueness (ty-seq _ t₁)   (ty-seq _ u₁)   = uniqueness t₁ u₁

-- Theorem (Type Inference):
-- For any context and expression, the existence of a matching type is decidable.
infer : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k)
  → (Σ Ty (Γ ⊢ e ⦂_)) is-decidable
infer Γ (int! n)  = in₀ (int  , ty-int n)
infer Γ (bool! n) = in₀ (bool , ty-bool n)
infer Γ skip      = in₀ (unit , ty-skip)
infer Γ (e₀ op[ o+ ] e₁)
  with infer Γ e₀  | infer Γ e₁
... | in₁ nt₀       | _             = in₁ λ (_ , t) → nt₀ (int , invert-op+ t .πₗ .πᵣ)
... | in₀ _         | in₁ nt₁       = in₁ λ (_ , t) → nt₁ (int , invert-op+ t .πᵣ .πᵣ)
... | in₀ (T₀ , t₀) | in₀ (T₁ , t₁)
  with decide-eq-ty T₀ int | decide-eq-ty T₁ int
... | in₀ (refl .int) | in₀ (refl .int) = in₀ (int , ty-op+ t₀ t₁)
... | in₀ (refl .int) | in₁ T₁≠int      = in₁ λ (_ , t) → T₁≠int (uniqueness t₁ (invert-op+ t .πᵣ .πᵣ))
... | in₁ T₀≠int      | _               = in₁ λ (_ , t) → T₀≠int (uniqueness t₀ (invert-op+ t .πₗ .πᵣ))
infer Γ (e₀ op[ o≥ ] e₁)
  with infer Γ e₀  | infer Γ e₁
... | in₁ nt₀       | _             = in₁ λ (_ , t) → nt₀ (int , invert-op≥ t .πₗ .πᵣ)
... | in₀ _         | in₁ nt₁       = in₁ λ (_ , t) → nt₁ (int , invert-op≥ t .πᵣ .πᵣ)
... | in₀ (T₀ , t₀) | in₀ (T₁ , t₁)
  with decide-eq-ty T₀ int | decide-eq-ty T₁ int
... | in₀ (refl .int) | in₀ (refl .int) = in₀ (bool , ty-op≥ t₀ t₁)
... | in₀ (refl .int) | in₁ T₁≠int      = in₁ λ (_ , t) → T₁≠int (uniqueness t₁ (invert-op≥ t .πᵣ .πᵣ))
... | in₁ T₀≠int      | _               = in₁ λ (_ , t) → T₀≠int (uniqueness t₀ (invert-op≥ t .πₗ .πᵣ))
infer Γ (if e₀ then e₁ else e₂)
  with infer Γ e₀ | infer Γ e₁ | infer Γ e₂
... | in₁ nt₀       | _             | _             = in₁ λ (_ , t) → nt₀ (bool , (invert-if t .π₀ .πᵣ))
... | in₀ (T₀ , t₀) | in₁ nt₁       | _             = in₁ λ (T , t) → nt₁ (T    , (invert-if t .π₁ .πᵣ))
... | in₀ (T₀ , t₀) | in₀ x         | in₁ nt₂       = in₁ λ (T , t) → nt₂ (T    , (invert-if t .π₂ .πᵣ))
... | in₀ (T₀ , t₀) | in₀ (T₁ , t₁) | in₀ (T₂ , t₂)
  with decide-eq-ty T₀ bool | decide-eq-ty T₁ T₂
... | in₀ (refl .bool) | in₀ (refl .T₁) = in₀ (T₁ , ty-if t₀ t₁ t₂)
... | in₀ (refl .bool) | in₁ T₁≠T₂      = in₁ λ (_ , t) → T₁≠T₂ (uniqueness t₁ (invert-if t .π₁ .πᵣ) ∙ uniqueness (invert-if t .π₂ .πᵣ) t₂)
... | in₁ T₀≠bool      | _              = in₁ λ (_ , t) → T₀≠bool (uniqueness t₀ (invert-if t .π₀ .πᵣ))
infer Γ (l := e)
  with infer Γ e
... | in₁ nt = in₁ λ (T , t) → nt (int , invert-assign t .πᵣ .πᵣ)
... | in₀ (T₀ , t₀)
  with decide-eq-ty T₀ int | decide-eq-tyl (Γ # l) intref
... | in₁ T₀≠int      | _              = in₁ λ (T , t) → T₀≠int (uniqueness t₀ (invert-assign t .πᵣ .πᵣ))
... | in₀ (refl .int) | in₀ p          = in₀ (unit , ty-assign p t₀)
... | in₀ (refl .int) | in₁ Γ#l≠intref = in₁ λ (T , t) → Γ#l≠intref (invert-assign t .πₗ)
infer Γ (* l)
  with decide-eq-tyl (Γ # l) intref
... | in₀ p  = in₀ (int , ty-deref p)
... | in₁ np = in₁ λ (T , t) → np (invert-deref t)
infer Γ (e₀ ; e₁)
  with infer Γ e₀ | infer Γ e₁
... | in₁ nt₀       | _             = in₁ λ (_ , t) → nt₀ (unit , invert-seq t .πₗ .πᵣ)
... | in₀ _         | in₁ nt₁       = in₁ λ (T , t) → nt₁ (T    , invert-seq t .πᵣ .πᵣ)
... | in₀ (T₀ , t₀) | in₀ (T₁ , t₁)
  with decide-eq-ty T₀ unit
... | in₀ (refl .unit) = in₀ (T₁ , ty-seq t₀ t₁)
... | in₁ T₀≠unit      = in₁ λ (_ , t) → T₀≠unit (uniqueness t₀ (invert-seq t .πₗ .πᵣ))
infer Γ (while e₀ loop e₁)
  with infer Γ e₀ | infer Γ e₁
... | in₁ nt₀       | _             = in₁ λ (_ , t) → nt₀ (bool , invert-while t .πₗ .πᵣ)
... | in₀ _         | in₁ nt₁       = in₁ λ (_ , t) → nt₁ (unit , invert-while t .πᵣ .πᵣ)
... | in₀ (T₀ , t₀) | in₀ (T₁ , t₁)
  with decide-eq-ty T₀ bool | decide-eq-ty T₁ unit
... | in₀ (refl .bool) | in₀ (refl .unit) = in₀ (unit , ty-while t₀ t₁)
... | in₀ (refl .bool) | in₁ T₁≠unit      = in₁ λ (_ , t) → T₁≠unit (uniqueness t₁ (invert-while t .πᵣ .πᵣ))
... | in₁ T₀≠bool      | _                = in₁ λ (_ , t) → T₀≠bool (uniqueness t₀ (invert-while t .πₗ .πᵣ))

-- Theorem (Decidability of Typing Judgements):
-- Any typing judgement is decidable.
decide-typing : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (T : Ty)
  → (Γ ⊢ e ⦂ T) is-decidable
decide-typing Γ e T
  with infer Γ e
... | in₁ nt = in₁ λ t → nt (T , t)
... | in₀ (T' , t')
  with decide-eq-ty T T'
... | in₀ (refl .T') = in₀ t'
... | in₁ T≠T' = in₁ λ t → T≠T' (uniqueness t t')

-- Values are irreducible in any store.
value→irreducible : {k : ℕ} {e : Ex k}
  → (v : e is-value) (s : Store k)
  → ¬ ((e , s) is-reducible)
value→irreducible () s ((.(int! (n₀ +ℤ n₁)) , .s) , op+-n n₀ n₁ .s)
value→irreducible () s ((.(bool! (n₀ ≥Bℤ n₁)) , .s) , op≥-n n₀ n₁ .s)
value→irreducible () s ((.(_ op[ o ] e₁) , πᵣ₁) , op-r₀ r o e₁)
value→irreducible () s ((.(int! n₀ op[ o ] _) , πᵣ₁) , op-r₁ n₀ o r)
value→irreducible () s ((.(int! (s # l)) , .s) , deref l .s)
value→irreducible () s ((.skip , .(s / l ↦ n)) , assign-n l n .s)
value→irreducible () s ((.(l := _) , πᵣ₁) , assign-r l r)
value→irreducible () .(πᵣ es') (es' , seq-n .(πₗ es') .(πᵣ es'))
value→irreducible () s ((.(_ ; e₁) , πᵣ₁) , seq-r r e₁)
value→irreducible () s ((.(Bool-if n₀ e₁ e₂) , .s) , if-n n₀ e₁ e₂ .s)
value→irreducible () s ((.(if _ then e₁ else e₂) , πᵣ₁) , if-r r e₁ e₂)
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
  with evaluate (preserve r t) s' depth
... | some ((e'' , s'') , r*) = some ((e'' , s'') , r :: r*)
... | none = none

-- Type inference and evaluation witnesses.
ty? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k)
  → Maybe Ty
ty? Γ e with infer Γ e
... | in₀ (T , _) = some T
... | in₁ _       = none

ev? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (s : Store k) (depth : ℕ)
  → Maybe (Ex k × Store k)
ev? Γ e s depth
  with infer Γ e
... | in₁ _ = none
... | in₀ (_ , t)
  with evaluate t s depth
... | none = none
... | some (es' , _) = some es'

step? : {k : ℕ}
  → (Γ : Ctx k) (e : Ex k) (s : Store k)
  → Maybe (Ex k × Store k)
step? Γ e s
  with infer Γ e
... | in₁ _ = none
... | in₀ (_ , t)
  with progress t s
... | in₀ _ = none
... | in₁ (es' , _) = some es'