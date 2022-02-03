module P2 where

open import lists
open import F2

PredCtx : (n : TyCtx) → Type₀
PredCtx = Ctx

PredPos : {n : TyCtx} → PredCtx n → Type₀
PredPos = CtxPos

PredVar : {n : TyCtx} → PredCtx n → Ty n → Type₀
PredVar = Var

data Proposition : {n : TyCtx} (Γ̂ : PredCtx n) (Γ : Ctx n) → Type₀

data Predicate : {n : TyCtx} (Γ̂ : PredCtx n) (Γ : Ctx n) (A : Ty n) → Type₀ where
  𝑃𝑉 : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A : Ty n} →
    PredVar Γ̂ A → Predicate Γ̂ Γ A
  𝑃𝐿 : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â : Ty n} →
    Proposition Γ̂ (Γ ⊹ Â) → Predicate Γ̂ Γ Â

data Proposition where
  _∈_ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A : Ty n} →
    Tm Γ A → Predicate Γ̂ Γ A → Proposition Γ̂ Γ
  _⇛_ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} →
    Proposition Γ̂ Γ → Proposition Γ̂ Γ → Proposition Γ̂ Γ
  ∀𝒳 : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â : Ty n} →
    Proposition (Γ̂ ⊹ Â) Γ → Proposition Γ̂ Γ
  ∀x : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A : Ty n} →
    Proposition Γ̂ (Γ ⊹ A) → Proposition Γ̂ Γ
  ∀X : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} →
    Proposition (WCtx Γ̂) (WCtx Γ) → Proposition Γ̂ Γ

shiftProp-n : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n}
  (𝑖 : TyCtxPos n) → Proposition Γ̂ Γ → Proposition (shiftCtx 𝑖 Γ̂) (shiftCtx 𝑖 Γ)

shiftPred-n : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A : Ty n}
  (𝑖 : TyCtxPos n) → Predicate Γ̂ Γ A → Predicate (shiftCtx 𝑖 Γ̂) (shiftCtx 𝑖 Γ) (shiftTy 𝑖 A)
shiftPred-n 𝑖 (𝑃𝑉 v) = 𝑃𝑉 (shiftVar 𝑖 v)
shiftPred-n 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-n 𝑖 𝐴)

shiftProp-n 𝑖 (t ∈ 𝒜) = {!!} ∈ shiftPred-n 𝑖 𝒜
shiftProp-n 𝑖 (𝐴 ⇛ 𝐵) = {!!}
shiftProp-n 𝑖 (∀𝒳 𝐴) = {!!}
shiftProp-n 𝑖 (∀x 𝐴) = {!!}
shiftProp-n 𝑖 (∀X 𝐴) = {!!}

shiftProp-Γ̂ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â : Ty n}
  (𝑖 : PredPos Γ̂) → Proposition Γ̂ Γ → Proposition (insert𝐶𝑡𝑥 𝑖 Â) Γ

shiftPred-Γ̂ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â A : Ty n}
  (𝑖 : PredPos Γ̂) → Predicate Γ̂ Γ A → Predicate (insert𝐶𝑡𝑥 𝑖 Â) Γ A
shiftPred-Γ̂ 𝑖 (𝑃𝑉 v) = 𝑃𝑉 (shift𝑉𝑎𝑟 𝑖 v)
shiftPred-Γ̂ 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-Γ̂ 𝑖 𝐴)

shiftProp-Γ̂ 𝑖 (t ∈ 𝒜) = t ∈ shiftPred-Γ̂ 𝑖 𝒜
shiftProp-Γ̂ 𝑖 (𝐴 ⇛ 𝐵) = shiftProp-Γ̂ 𝑖 𝐴 ⇛ shiftProp-Γ̂ 𝑖 𝐵
shiftProp-Γ̂ 𝑖 (∀𝒳 𝐴) = ∀𝒳 (shiftProp-Γ̂ (𝑠𝑝 𝑖) 𝐴)
shiftProp-Γ̂ 𝑖 (∀x 𝐴) = ∀x (shiftProp-Γ̂ 𝑖 𝐴)
shiftProp-Γ̂ {Γ = Γ} 𝑖 (∀X 𝐴) =
  ∀X (tr (λ Δ → Proposition Δ (WCtx Γ)) (Winsert 𝑖) (shiftProp-Γ̂ (WCtxPos 𝑖) 𝐴))

shiftProp-Γ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A : Ty n}
  (𝑖 : CtxPos Γ) → Proposition Γ̂ Γ → Proposition Γ̂ (insert𝐶𝑡𝑥 𝑖 A)

shiftPred-Γ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {A B : Ty n}
  (𝑖 : CtxPos Γ) → Predicate Γ̂ Γ B → Predicate Γ̂ (insert𝐶𝑡𝑥 𝑖 A) B
shiftPred-Γ 𝑖 (𝑃𝑉 v) = 𝑃𝑉 v
shiftPred-Γ 𝑖 (𝑃𝐿 𝐴) = 𝑃𝐿 (shiftProp-Γ (𝑠𝑝 𝑖) 𝐴 )

shiftProp-Γ 𝑖 (t ∈ 𝒜) = shiftTm 𝑖 t ∈ shiftPred-Γ 𝑖 𝒜
shiftProp-Γ 𝑖 (𝐴 ⇛ 𝐵) = shiftProp-Γ 𝑖 𝐴 ⇛ shiftProp-Γ 𝑖 𝐵
shiftProp-Γ 𝑖 (∀𝒳 𝐴) = ∀𝒳 (shiftProp-Γ 𝑖 𝐴)
shiftProp-Γ 𝑖 (∀x 𝐴) = ∀x (shiftProp-Γ (𝑠𝑝 𝑖) 𝐴)
shiftProp-Γ {Γ̂ = Γ̂} 𝑖 (∀X 𝐴) =
  ∀X (tr (λ Δ → Proposition (WCtx Γ̂) Δ) (Winsert 𝑖) (shiftProp-Γ (WCtxPos 𝑖) 𝐴))

subsPredInProp : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â : Ty n} →
  Proposition Γ̂ Γ → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Proposition (remove𝑉𝑎𝑟 v) Γ

subsPredVar : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â A : Ty n} →
  PredVar Γ̂ A → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Predicate (remove𝑉𝑎𝑟 v) Γ A
subsPredVar 𝑧𝑣 𝑧𝑣 𝒜 = 𝒜
subsPredVar 𝑧𝑣 (𝑠𝑣 v) 𝒜 = 𝑃𝑉 𝑧𝑣
subsPredVar (𝑠𝑣 w) 𝑧𝑣 𝒜 = 𝑃𝑉 w
subsPredVar (𝑠𝑣 w) (𝑠𝑣 v) 𝒜 = shiftPred-Γ̂ 𝑧𝑝 (subsPredVar w v 𝒜)

subsPredInPred : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n} {Â A : Ty n} →
  Predicate Γ̂ Γ A → (v : PredVar Γ̂ Â) → Predicate (prefix𝑉𝑎𝑟 v) Γ Â → Predicate (remove𝑉𝑎𝑟 v) Γ A
subsPredInPred (𝑃𝑉 w) v 𝒜 = subsPredVar w v 𝒜
subsPredInPred (𝑃𝐿 𝐴) v 𝒜 = 𝑃𝐿 (subsPredInProp 𝐴 v (shiftPred-Γ 𝑧𝑝 𝒜))

subsPredInProp (t ∈ ℬ) v 𝒜 = t ∈ (subsPredInPred ℬ v 𝒜)
subsPredInProp (𝐴 ⇛ 𝐵) v 𝒜 = subsPredInProp 𝐴 v 𝒜 ⇛ subsPredInProp 𝐵 v 𝒜
subsPredInProp (∀𝒳 𝐴) v 𝒜 = ∀𝒳 (subsPredInProp 𝐴 (𝑠𝑣 v) 𝒜)
subsPredInProp (∀x 𝐴) v 𝒜 = ∀x (subsPredInProp 𝐴 v (shiftPred-Γ 𝑧𝑝 𝒜))
subsPredInProp (∀X 𝐴) v 𝒜 = ∀X {!subsPredInProp 𝐴 (WVar v)
--(shift𝑉𝑎𝑟 𝑧𝑝 v)!}

--PropCtx : {n : TyCtx} (Γ̂ : PredCtx n) (Γ : Ctx n)

--data Derivation

{-idTy : Ty 0
idTy = ∀⋆ (𝑉 𝑍 ⇒ 𝑉 𝑍)

_≡𝑇𝑚_ : {n : TyCtx} {Γ̂ : PredCtx n} {Γ : Ctx n}-}
