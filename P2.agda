module P2 where

open import lists
open import F2

-- Round IV

PredCtx : (γ : TyCtx) → Type₀
PredCtx = Ctx

PredPos : {γ : TyCtx} → PredCtx γ → Type₀
PredPos = CtxPos

PredVar : {γ : TyCtx} → PredCtx γ → Ty γ → Type₀
PredVar = Var

data Proposition : {γ : TyCtx} (Γ̂ : PredCtx γ) (Γ : Ctx γ) → Type₀

data Predicate : {γ : TyCtx} (Γ̂ : PredCtx γ) (Γ : Ctx γ) (A : Ty γ) → Type₀ where
  𝑃𝑉 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
    PredVar Γ̂ A → Predicate Γ̂ Γ A
  𝑃𝐿 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} →
    Proposition Γ̂ (Γ ⊹ Â) → Predicate Γ̂ Γ Â

data Proposition where
  _∈_ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
    Tm Γ A → Predicate Γ̂ Γ A → Proposition Γ̂ Γ
  _⇛_ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} →
    Proposition Γ̂ Γ → Proposition Γ̂ Γ → Proposition Γ̂ Γ
  ∀𝒳 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} →
    Proposition (Γ̂ ⊹ Â) Γ → Proposition Γ̂ Γ
  ∀x : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
    Proposition Γ̂ (Γ ⊹ A) → Proposition Γ̂ Γ
  ∀X : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {⋆ : ⊤} →
    Proposition (shiftCtx {⋆ = ⋆} 𝑧𝑝 Γ̂) (shiftCtx 𝑧𝑝 Γ) → Proposition Γ̂ Γ

shiftProp-n : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ}  {⋆ : ⊤}
  (𝑖 : TyPos γ) → Proposition Γ̂ Γ → Proposition (shiftCtx {⋆ = ⋆} 𝑖 Γ̂) (shiftCtx 𝑖 Γ)

shiftPred-n : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ}  {⋆ : ⊤}
  (𝑖 : TyPos γ) → Predicate Γ̂ Γ A → Predicate (shiftCtx {⋆ = ⋆} 𝑖 Γ̂) (shiftCtx 𝑖 Γ) (shiftTy 𝑖 A)
shiftPred-n 𝑖 (𝑃𝑉 v) = 𝑃𝑉 (shiftVar-γ 𝑖 v)
shiftPred-n 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-n 𝑖 𝐴)

shiftProp-n 𝑖 (t ∈ 𝒜) = shiftTm-γ 𝑖 t ∈ shiftPred-n 𝑖 𝒜
shiftProp-n 𝑖 (𝐴 ⇛ 𝐵) = shiftProp-n 𝑖 𝐴 ⇛ shiftProp-n 𝑖 𝐵
shiftProp-n 𝑖 (∀𝒳 𝐴) = ∀𝒳 (shiftProp-n 𝑖 𝐴)
shiftProp-n 𝑖 (∀x 𝐴) = ∀x (shiftProp-n 𝑖 𝐴)
shiftProp-n {Γ̂ = Γ̂} {Γ} 𝑖 (∀X 𝐴) = ∀X
  (tr (λ Γ → Proposition  (shiftCtx 𝑧𝑝 (shiftCtx 𝑖 Γ̂)) Γ) (shiftCtx² 𝑧𝑝 𝑖 Γ)
    (tr (λ Γ̂ → Proposition Γ̂ (shiftCtx (𝑠𝑝 𝑖) (shiftCtx 𝑧𝑝 Γ))) (shiftCtx² 𝑧𝑝 𝑖 Γ̂)
      (shiftProp-n (𝑠𝑝 𝑖) 𝐴)))

shiftProp-Γ̂ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ}
  (𝑖 : PredPos Γ̂) → Proposition Γ̂ Γ → Proposition (insert𝐶𝑡𝑥 𝑖 Â) Γ

shiftPred-Γ̂ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â A : Ty γ}
  (𝑖 : PredPos Γ̂) → Predicate Γ̂ Γ A → Predicate (insert𝐶𝑡𝑥 𝑖 Â) Γ A
shiftPred-Γ̂ 𝑖 (𝑃𝑉 v) = 𝑃𝑉 (shift𝑉𝑎𝑟 𝑖 v)
shiftPred-Γ̂ 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-Γ̂ 𝑖 𝐴)

shiftProp-Γ̂ 𝑖 (t ∈ 𝒜) = t ∈ shiftPred-Γ̂ 𝑖 𝒜
shiftProp-Γ̂ 𝑖 (𝐴 ⇛ 𝐵) = shiftProp-Γ̂ 𝑖 𝐴 ⇛ shiftProp-Γ̂ 𝑖 𝐵
shiftProp-Γ̂ 𝑖 (∀𝒳 𝐴) = ∀𝒳 (shiftProp-Γ̂ (𝑠𝑝 𝑖) 𝐴)
shiftProp-Γ̂ 𝑖 (∀x 𝐴) = ∀x (shiftProp-Γ̂ 𝑖 𝐴)
shiftProp-Γ̂ {Γ = Γ} 𝑖 (∀X 𝐴) =
  ∀X (tr (λ Δ → Proposition Δ (shiftCtx 𝑧𝑝 Γ)) (shiftInsert 𝑧𝑝 𝑖)
    (shiftProp-Γ̂ (shiftCtxPos-γ 𝑧𝑝 𝑖) 𝐴))

shiftProp-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ}
  (𝑖 : CtxPos Γ) → Proposition Γ̂ Γ → Proposition Γ̂ (insert𝐶𝑡𝑥 𝑖 A)

shiftPred-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A B : Ty γ}
  (𝑖 : CtxPos Γ) → Predicate Γ̂ Γ B → Predicate Γ̂ (insert𝐶𝑡𝑥 𝑖 A) B
shiftPred-Γ 𝑖 (𝑃𝑉 v) = 𝑃𝑉 v
shiftPred-Γ 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-Γ (𝑠𝑝 𝑖) 𝐴 )

shiftProp-Γ 𝑖 (t ∈ 𝒜) = shiftTm 𝑖 t ∈ shiftPred-Γ 𝑖 𝒜
shiftProp-Γ 𝑖 (𝐴 ⇛ 𝐵) = shiftProp-Γ 𝑖 𝐴 ⇛ shiftProp-Γ 𝑖 𝐵
shiftProp-Γ 𝑖 (∀𝒳 𝐴) = ∀𝒳 (shiftProp-Γ 𝑖 𝐴)
shiftProp-Γ 𝑖 (∀x 𝐴) = ∀x (shiftProp-Γ (𝑠𝑝 𝑖) 𝐴)
shiftProp-Γ {Γ̂ = Γ̂} 𝑖 (∀X 𝐴) =
  ∀X (tr (λ Δ → Proposition (shiftCtx 𝑧𝑝 Γ̂) Δ) (shiftInsert 𝑧𝑝 𝑖)
    (shiftProp-Γ (shiftCtxPos-γ 𝑧𝑝 𝑖) 𝐴))

subsPredInProp : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} →
  Proposition Γ̂ Γ → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Proposition (remove𝑉𝑎𝑟 v) Γ

subsPredVar : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â A : Ty γ} →
  PredVar Γ̂ A → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Predicate (remove𝑉𝑎𝑟 v) Γ A
subsPredVar 𝑧𝑣 𝑧𝑣 𝒜 = 𝒜
subsPredVar 𝑧𝑣 (𝑠𝑣 v) 𝒜 = 𝑃𝑉 𝑧𝑣
subsPredVar (𝑠𝑣 w) 𝑧𝑣 𝒜 = 𝑃𝑉 w
subsPredVar (𝑠𝑣 w) (𝑠𝑣 v) 𝒜 = shiftPred-Γ̂ 𝑧𝑝 (subsPredVar w v 𝒜)

subsPredInPred : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â A : Ty γ} →
  Predicate Γ̂ Γ A → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Predicate (remove𝑉𝑎𝑟 v) Γ A
subsPredInPred (𝑃𝑉 w) v 𝒜 = subsPredVar w v 𝒜
subsPredInPred (𝑃𝐿 𝐴) v 𝒜 = 𝑃𝐿 (subsPredInProp 𝐴 v (shiftPred-Γ 𝑧𝑝 𝒜))

subsPredInProp (t ∈ ℬ) v 𝒜 = t ∈ (subsPredInPred ℬ v 𝒜)
subsPredInProp (𝐴 ⇛ 𝐵) v 𝒜 = subsPredInProp 𝐴 v 𝒜 ⇛ subsPredInProp 𝐵 v 𝒜
subsPredInProp (∀𝒳 𝐴) v 𝒜 = ∀𝒳 (subsPredInProp 𝐴 (𝑠𝑣 v) 𝒜)
subsPredInProp (∀x 𝐴) v 𝒜 = ∀x (subsPredInProp 𝐴 v (shiftPred-Γ 𝑧𝑝 𝒜))
subsPredInProp {Γ = Γ} {Â} (∀X 𝐴) v 𝒜 =
  ∀X (tr (λ Γ̂ → Proposition Γ̂ (shiftCtx 𝑧𝑝 Γ)) (shiftRemove 𝑧𝑝 v ⁻¹)
    (subsPredInProp 𝐴 (shiftVar-γ 𝑧𝑝 v)
      (tr (λ Γ̂ → Predicate Γ̂ (shiftCtx 𝑧𝑝 Γ) (shiftTy 𝑧𝑝 Â)) (shiftPrefix 𝑧𝑝 v)
        (shiftPred-n 𝑧𝑝 𝒜))))

subsTmInProp : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
  Proposition Γ̂ Γ → (v : Var Γ A) → Tm (prefix𝑉𝑎𝑟 v) A  → Proposition Γ̂ (remove𝑉𝑎𝑟 v)

subsTmInPred : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A B : Ty γ} →
  Predicate Γ̂ Γ B → (v : Var Γ A) → Tm (prefix𝑉𝑎𝑟 v) A → Predicate Γ̂ (remove𝑉𝑎𝑟 v) B
subsTmInPred (𝑃𝑉 w) v t = 𝑃𝑉 w
subsTmInPred (𝑃𝐿 𝐴) v t = 𝑃𝐿 (subsTmInProp 𝐴 (𝑠𝑣 v) t)

subsTmInProp (s ∈ 𝒜) v t = subsTm s v t ∈ subsTmInPred 𝒜 v t
subsTmInProp (𝐴 ⇛ 𝐵) v t = subsTmInProp 𝐴 v t ⇛ subsTmInProp 𝐵 v t
subsTmInProp (∀𝒳 𝐴) v t = ∀𝒳 (subsTmInProp 𝐴 v t)
subsTmInProp (∀x 𝐴) v t = ∀x (subsTmInProp 𝐴 (𝑠𝑣 v) t)
subsTmInProp {Γ̂ = Γ̂} {Γ} {A} (∀X 𝐴) v t =
  ∀X (tr (λ Γ → Proposition (shiftCtx 𝑧𝑝 Γ̂) Γ) (shiftRemove 𝑧𝑝 v ⁻¹)
    (subsTmInProp 𝐴 (shiftVar-γ 𝑧𝑝 v)
      (tr (λ Γ → Tm Γ (shiftTy 𝑧𝑝 A)) (shiftPrefix 𝑧𝑝 v) (shiftTm-γ 𝑧𝑝 t))))

subsTyInProp : {γ : TyCtx} {⋆ : ⊤} {Γ̂ : PredCtx γ} {Γ : Ctx γ} →
  Proposition Γ̂ Γ → (v : TyVar γ ⋆) → (A : Ty (prefix𝑉𝑎𝑟 v)) →
  Proposition (subsCtx Γ̂ v A) (subsCtx Γ v A)

subsTyInPred : {γ : TyCtx} {⋆ : ⊤} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {B : Ty γ} →
  Predicate Γ̂ Γ B → (v : TyVar γ ⋆) → (A : Ty (prefix𝑉𝑎𝑟 v)) →
  Predicate (subsCtx Γ̂ v A) (subsCtx Γ v A) (subsTy B v A)
subsTyInPred (𝑃𝑉 w) v A = 𝑃𝑉 (subsVar-γ w v A)
subsTyInPred (𝑃𝐿 𝐴) v A = 𝑃𝐿 (subsTyInProp 𝐴 v A )

subsTyInProp (t ∈ 𝒜) v A = subsTm-γ t v A ∈ subsTyInPred 𝒜 v A
subsTyInProp (𝐴 ⇛ 𝐵) v A = subsTyInProp 𝐴 v A ⇛ subsTyInProp 𝐵 v A
subsTyInProp (∀𝒳 𝐴) v A = ∀𝒳 (subsTyInProp 𝐴 v A)
subsTyInProp (∀x 𝐴) v A = ∀x (subsTyInProp 𝐴 v A)
subsTyInProp {Γ̂ = Γ̂} {Γ} (∀X 𝐴) v A =
  ∀X (tr (λ Γ̂ → Proposition Γ̂ (shiftCtx 𝑧𝑝 (subsCtx Γ v A))) (shiftSubsCtx v 𝑧𝑝 Γ̂ A)
    (tr (λ Γ → Proposition (subsCtx (shiftCtx 𝑧𝑝 Γ̂) (𝑠𝑣 v) A) Γ) (shiftSubsCtx v 𝑧𝑝 Γ A)
      (subsTyInProp 𝐴 (𝑠𝑣 v) A)))

-- Round V

data OTm-Pred : {γ : TyCtx} (Γ̂ : PredCtx γ) (Γ : Ctx γ) (A : Ty γ) → Type₀

data OTm-Prop : {γ : TyCtx} (Γ̂ : PredCtx γ) (Γ : Ctx γ) → Type₀ where
  𝑂∈ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} → Predicate Γ̂ Γ A → OTm-Prop Γ̂ Γ
  _∈_ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
    Tm Γ A → OTm-Pred Γ̂ Γ A → OTm-Prop Γ̂ Γ
  _⇛₁_ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → OTm-Prop Γ̂ Γ → Proposition Γ̂ Γ → OTm-Prop Γ̂ Γ
  _⇛₂_ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → Proposition Γ̂ Γ → OTm-Prop Γ̂ Γ → OTm-Prop Γ̂ Γ
  ∀𝒳 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} → OTm-Prop (Γ̂ ⊹ Â) Γ → OTm-Prop Γ̂ Γ
  ∀x : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} → OTm-Prop Γ̂ (Γ ⊹ A) → OTm-Prop Γ̂ Γ
  ∀X : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {⋆ : ⊤} →
    OTm-Prop (shiftCtx {⋆ = ⋆} 𝑧𝑝 Γ̂) (shiftCtx 𝑧𝑝 Γ) → OTm-Prop Γ̂ Γ

data OTm-Pred where
  𝑃𝐿 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} →
    OTm-Prop Γ̂ (Γ ⊹ Â) → OTm-Pred Γ̂ Γ Â

OTm-Prop-γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → OTm-Prop Γ̂ Γ → TyCtx
OTm-Prop-γ {γ} (𝑂∈ x) = γ
OTm-Prop-γ (t ∈ 𝑃𝐿 env) = OTm-Prop-γ env
OTm-Prop-γ (env ⇛₁ 𝐵) = OTm-Prop-γ env
OTm-Prop-γ (𝐴 ⇛₂ env) = OTm-Prop-γ env
OTm-Prop-γ (∀𝒳 env) = OTm-Prop-γ env
OTm-Prop-γ (∀x env) = OTm-Prop-γ env
OTm-Prop-γ (∀X env) = OTm-Prop-γ env

OTm-Prop-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (env : OTm-Prop Γ̂ Γ) → Ctx (OTm-Prop-γ env)
OTm-Prop-Γ {Γ = Γ} (𝑂∈ 𝒜) = Γ
OTm-Prop-Γ (t ∈ 𝑃𝐿 env) = OTm-Prop-Γ env
OTm-Prop-Γ (env ⇛₁ 𝐵) = OTm-Prop-Γ env
OTm-Prop-Γ (𝐴 ⇛₂ env) = OTm-Prop-Γ env
OTm-Prop-Γ (∀𝒳 env) = OTm-Prop-Γ env
OTm-Prop-Γ (∀x env) = OTm-Prop-Γ env
OTm-Prop-Γ (∀X env) = OTm-Prop-Γ env

OTm-Prop-A : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (env : OTm-Prop Γ̂ Γ) → Ty (OTm-Prop-γ env)
OTm-Prop-A (𝑂∈ {A = A} 𝒜) = A
OTm-Prop-A (t ∈ 𝑃𝐿 env) = OTm-Prop-A env
OTm-Prop-A (env ⇛₁ 𝐵) = OTm-Prop-A env
OTm-Prop-A (𝐴 ⇛₂ env) = OTm-Prop-A env
OTm-Prop-A (∀𝒳 env) = OTm-Prop-A env
OTm-Prop-A (∀x env) = OTm-Prop-A env
OTm-Prop-A (∀X env) = OTm-Prop-A env

OTm-Prop-fill : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ}
  (env : OTm-Prop Γ̂ Γ) → Tm (OTm-Prop-Γ env) (OTm-Prop-A env) → Proposition Γ̂ Γ
OTm-Prop-fill (𝑂∈ 𝒜) t = t ∈ 𝒜
OTm-Prop-fill (s ∈ 𝑃𝐿 env) t = s ∈ 𝑃𝐿 (OTm-Prop-fill env t)
OTm-Prop-fill (env ⇛₁ 𝐵) t = OTm-Prop-fill env t ⇛ 𝐵
OTm-Prop-fill (𝐴 ⇛₂ env) t = 𝐴 ⇛ OTm-Prop-fill env t
OTm-Prop-fill (∀𝒳 env) t = ∀𝒳 (OTm-Prop-fill env t)
OTm-Prop-fill (∀x env) t = ∀x (OTm-Prop-fill env t)
OTm-Prop-fill (∀X env) t = ∀X (OTm-Prop-fill env t)

data RuleProp : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (𝐴 𝐵 : Proposition Γ̂ Γ) → Type₀ where
  β₃ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ}
    (t : Tm Γ A) (𝐴 : Proposition Γ̂ (Γ ⊹ A)) → RuleProp (t ∈ (𝑃𝐿 𝐴)) (subsTmInProp 𝐴 𝑧𝑣 t)

data Step : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (𝐴 𝐵 : Proposition Γ̂ Γ) → Type₀ where
  ⟨_⊚_⊚_⟩ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (env₁ : OTm-Prop Γ̂ Γ)
    (env₂ : OTm (OTm-Prop-Γ env₁) (OTm-Prop-A env₁)) {t s : Tm (OTm-Γ env₂) (OTm-A env₂)} →
    RuleTm t s →
      Step (OTm-Prop-fill env₁ (OTm-fill env₂ t)) (OTm-Prop-fill env₁ (OTm-fill env₂ s))
  ⟨_⊚_⊚_⟩⁻¹ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} (env₁ : OTm-Prop Γ̂ Γ)
    (env₂ : OTm (OTm-Prop-Γ env₁) (OTm-Prop-A env₁)) {t s : Tm (OTm-Γ env₂) (OTm-A env₂)} →
    RuleTm t s →
      Step (OTm-Prop-fill env₁ (OTm-fill env₂ s)) (OTm-Prop-fill env₁ (OTm-fill env₂ t))

-- Round VI

PropCtx : {γ : TyCtx} → PredCtx γ → Ctx γ → Type₀
PropCtx Γ̂ Γ = 𝐶𝑡𝑥 (Proposition Γ̂ Γ)

PropVar : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → PropCtx Γ̂ Γ → Proposition Γ̂ Γ → Type₀
PropVar {Γ̂ = Γ̂} {Γ}  = 𝑉𝑎𝑟 {ty = Proposition Γ̂ Γ}

PropPos : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → PropCtx Γ̂ Γ → Type₀
PropPos {Γ̂ = Γ̂} {Γ} = 𝑃𝑜𝑠 {ty = Proposition Γ̂ Γ}

shiftPropCtx-Γ̂ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ}
  (𝑖 : PredPos Γ̂) → PropCtx Γ̂ Γ → PropCtx (insert𝐶𝑡𝑥 𝑖 Â) Γ
shiftPropCtx-Γ̂ 𝑖 = map𝐶𝑡𝑥 (shiftProp-Γ̂ 𝑖)

shiftPropCtx-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ}
  (𝑖 : PredPos Γ) → PropCtx Γ̂ Γ → PropCtx Γ̂ (insert𝐶𝑡𝑥 𝑖 A)
shiftPropCtx-Γ 𝑖 = map𝐶𝑡𝑥 (shiftProp-Γ 𝑖)

shiftPropCtx-n : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {⋆ : ⊤}
  (𝑖 : TyPos γ) → PropCtx Γ̂ Γ → PropCtx (shiftCtx {⋆ = ⋆} 𝑖 Γ̂) (shiftCtx 𝑖 Γ)
shiftPropCtx-n 𝑖 = map𝐶𝑡𝑥 (shiftProp-n 𝑖)

data Deduction : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} →
                 PropCtx Γ̂ Γ → Proposition Γ̂ Γ → Type₀ where
  𝐷𝑉 : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {𝐴 : Proposition Γ̂ Γ} →
    PropVar α 𝐴 → Deduction α 𝐴
  →ᵢ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {𝐴 𝐵 : Proposition Γ̂ Γ} →
    Deduction (α ⊹ 𝐴) 𝐵 → Deduction α (𝐴 ⇛ 𝐵)
  →ₑ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {𝐴 𝐵 : Proposition Γ̂ Γ} →
    Deduction α (𝐴 ⇛ 𝐵) → Deduction α 𝐴 → Deduction α 𝐵
  ∀⁰ᵢ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {Â : Ty γ}
    {𝐴 : Proposition (Γ̂ ⊹ Â) Γ} →
    Deduction (shiftPropCtx-Γ̂ {Â = Â} 𝑧𝑝 α) 𝐴 → Deduction α (∀𝒳 𝐴)
  ∀¹ᵢ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {A : Ty γ}
    {𝐴 : Proposition Γ̂ (Γ ⊹ A)} →
    Deduction (shiftPropCtx-Γ {A = A} 𝑧𝑝 α) 𝐴 → Deduction α (∀x 𝐴)
  ∀²ᵢ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {⋆ : ⊤}
    {𝐴 : Proposition (shiftCtx {⋆ = ⋆} 𝑧𝑝 Γ̂) (shiftCtx 𝑧𝑝 Γ)} →
    Deduction (shiftPropCtx-n {⋆ = ⋆} 𝑧𝑝 α) 𝐴 → Deduction α (∀X 𝐴)
  ∀⁰ₑ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {Â : Ty γ}
    {𝐴 : Proposition (Γ̂ ⊹ Â) Γ} →
    Deduction α (∀𝒳 𝐴) → (𝒜 : Predicate Γ̂ Γ Â) → Deduction α (subsPredInProp 𝐴 𝑧𝑣 𝒜)
  ∀¹ₑ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {A : Ty γ}
    {𝐴 : Proposition Γ̂ (Γ ⊹ A)} →
    Deduction α (∀x 𝐴) → (t : Tm Γ A) → Deduction α (subsTmInProp 𝐴 𝑧𝑣 t)
  ∀²ₑ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {⋆ : ⊤}
    {𝐴 : Proposition (shiftCtx {⋆ = ⋆} 𝑧𝑝 Γ̂) (shiftCtx 𝑧𝑝 Γ)} →
    Deduction α (∀X 𝐴) → (A : Ty γ) →
    Deduction α
      (tr (λ Γ̂ → Proposition Γ̂ Γ) (subsShiftCtx 𝑧𝑣 Γ̂ A)
        (tr (λ Γ → Proposition (subsCtx (shiftCtx 𝑧𝑝 Γ̂) 𝑧𝑣 A) Γ) (subsShiftCtx 𝑧𝑣 Γ A)
          (subsTyInProp 𝐴 𝑧𝑣 A)))
  β : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {𝐴 𝐵 : Proposition Γ̂ Γ} →
    Deduction α 𝐴 → Step 𝐴 𝐵 → Deduction α 𝐵
