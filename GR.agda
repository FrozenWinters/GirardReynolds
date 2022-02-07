module GR where

open import lists
open import F2
open import P2

-- The Girard Projection

πGirard-Ctx : {γ : TyCtx} (Γ̂ : Ctx γ) → TyCtx
πGirard-Ctx = map𝐶𝑡𝑥 (λ Â → tt)

πGirard-Prop : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} →
  Proposition Γ̂ Γ → Ty (πGirard-Ctx Γ̂)
πGirard-Pred : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} →
  Predicate Γ̂ Γ A → Ty (πGirard-Ctx Γ̂)

πGirard-Pred (𝑃𝑉 v) = 𝑉 (tr𝑉𝑎𝑟 (λ Â → tt) v)
πGirard-Pred (𝑃𝐿 𝐴) = πGirard-Prop 𝐴

πGirard-Prop (t ∈ 𝒜) = πGirard-Pred 𝒜
πGirard-Prop (𝐴 ⇛ 𝐵) = πGirard-Prop 𝐴 ⇒ πGirard-Prop 𝐵
πGirard-Prop (∀𝒳 𝐴) = ∀⋆ (πGirard-Prop 𝐴)
πGirard-Prop (∀x 𝐴) = πGirard-Prop 𝐴
πGirard-Prop {Γ̂ = Γ̂} (∀X 𝐴) = tr Ty (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑧𝑝) Γ̂) (πGirard-Prop 𝐴)

πGirard-PropCtx : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} →
  PropCtx Γ̂ Γ → Ctx (πGirard-Ctx Γ̂)
πGirard-PropCtx = map𝐶𝑡𝑥 πGirard-Prop

πGirard-Prop-fill : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ}
  (env : OTm-Prop Γ̂ Γ) (t s : Tm (OTm-Prop-Γ env) (OTm-Prop-A env)) →
  πGirard-Prop (OTm-Prop-fill env t) ≡ πGirard-Prop (OTm-Prop-fill env s)
πGirard-Prop-fill (𝑂∈ 𝒜) t s = refl
πGirard-Prop-fill (u ∈ 𝑃𝐿 env) t s = πGirard-Prop-fill env t s
πGirard-Prop-fill (env ⇛₁ 𝐵) t s = ap (_⇒ πGirard-Prop 𝐵) (πGirard-Prop-fill env t s)
πGirard-Prop-fill (𝐴 ⇛₂ env) t s = ap (πGirard-Prop 𝐴 ⇒_) (πGirard-Prop-fill env t s)
πGirard-Prop-fill (∀𝒳 env) t s = ap ∀⋆ (πGirard-Prop-fill env t s)
πGirard-Prop-fill (∀x env) t s = πGirard-Prop-fill env t s
πGirard-Prop-fill {Γ̂ = Γ̂} (∀X env) t s =
  ap (tr Ty (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑧𝑝) Γ̂)) (πGirard-Prop-fill env t s)

πGirard-Prop-shift-Γ̂ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} (𝑖 : 𝑃𝑜𝑠 Γ̂)
  (𝐴 : Proposition Γ̂ Γ) →
  πGirard-Prop (shiftProp-Γ̂ {Â = Â} 𝑖 𝐴)
    ≡ tr Ty (trInsert𝐶𝑡𝑥 (λ Â → tt) 𝑖 ⁻¹) (shiftTy (tr𝑃𝑜𝑠 (λ Â → tt) 𝑖) (πGirard-Prop 𝐴))
πGirard-Prop-shift-Γ̂ 𝑖 (t ∈ 𝑃𝑉 v) = {!!}
πGirard-Prop-shift-Γ̂ 𝑖 (t ∈ 𝑃𝐿 𝐴) = πGirard-Prop-shift-Γ̂ 𝑖 𝐴
πGirard-Prop-shift-Γ̂ 𝑖 (𝐴 ⇛ 𝐵) =
  ap₂ _⇒_  (πGirard-Prop-shift-Γ̂ 𝑖 𝐴) (πGirard-Prop-shift-Γ̂ 𝑖 𝐵)
  ∙ tr⇒ (trInsert𝐶𝑡𝑥 (λ Â₁ → tt) 𝑖 ⁻¹) _ _ ⁻¹
πGirard-Prop-shift-Γ̂ 𝑖 (∀𝒳 𝐴) =
  ap ∀⋆ (πGirard-Prop-shift-Γ̂ (𝑠𝑝 𝑖) 𝐴)
  ∙ ap (λ x → ∀⋆ (tr Ty x (shiftTy (𝑠𝑝 (tr𝑃𝑜𝑠 (λ Â → tt) 𝑖)) (πGirard-Prop 𝐴))))
    (ap⁻¹ (_⊹ tt) (trInsert𝐶𝑡𝑥 (λ Â₂ → tt) 𝑖))
  ∙ tr∀⋆ (trInsert𝐶𝑡𝑥 (λ Â₂ → tt) 𝑖 ⁻¹) _ ⁻¹
πGirard-Prop-shift-Γ̂ 𝑖 (∀x 𝐴) = πGirard-Prop-shift-Γ̂ 𝑖  𝐴
πGirard-Prop-shift-Γ̂ 𝑖 (∀X 𝐴) = {!!}

πGirard-PropCtx-shift-Γ̂ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {Â : Ty γ} (𝑖 : 𝑃𝑜𝑠 Γ̂)
  (α : PropCtx Γ̂ Γ) →
  πGirard-PropCtx (shiftPropCtx-Γ̂ {Â = Â} 𝑖 α)
    ≡ tr Ctx (trInsert𝐶𝑡𝑥 (λ Â → tt) 𝑖 ⁻¹) (shiftCtx (tr𝑃𝑜𝑠 (λ Â → tt) 𝑖) (πGirard-PropCtx α))
πGirard-PropCtx-shift-Γ̂ 𝑖 ∅ = tr∅ (trInsert𝐶𝑡𝑥 (λ Â₁ → tt) 𝑖 ⁻¹) ⁻¹
πGirard-PropCtx-shift-Γ̂ 𝑖 (α ⊹ 𝐴) =
  ap₂ _⊹_ (πGirard-PropCtx-shift-Γ̂ 𝑖 α) (πGirard-Prop-shift-Γ̂ 𝑖 𝐴)
  ∙ tr⊹ (trInsert𝐶𝑡𝑥 (λ Â₁ → tt) 𝑖 ⁻¹) (shiftCtx (tr𝑃𝑜𝑠 (λ Â₁ → tt) 𝑖) (πGirard-PropCtx α))
   (shiftTy (tr𝑃𝑜𝑠 (λ Â₁ → tt) 𝑖) (πGirard-Prop 𝐴)) ⁻¹

πGirard-Prop-shift-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} (𝑖 : 𝑃𝑜𝑠 Γ)
  (𝐴 : Proposition Γ̂ Γ) →
  πGirard-Prop (shiftProp-Γ {A = A} 𝑖 𝐴) ≡ πGirard-Prop 𝐴
πGirard-Prop-shift-Γ 𝑖 (t ∈ 𝑃𝑉 v) = refl
πGirard-Prop-shift-Γ 𝑖 (t ∈ 𝑃𝐿 𝐴) = πGirard-Prop-shift-Γ (𝑠𝑝 𝑖) 𝐴
πGirard-Prop-shift-Γ 𝑖 (𝐴 ⇛ 𝐵) =
  ap₂ _⇒_ (πGirard-Prop-shift-Γ 𝑖 𝐴) (πGirard-Prop-shift-Γ 𝑖 𝐵)
πGirard-Prop-shift-Γ 𝑖 (∀𝒳 𝐴) = ap ∀⋆ (πGirard-Prop-shift-Γ 𝑖 𝐴)
πGirard-Prop-shift-Γ 𝑖 (∀x 𝐴) = πGirard-Prop-shift-Γ (𝑠𝑝 𝑖) 𝐴
πGirard-Prop-shift-Γ 𝑖 (∀X 𝐴) = {!πGirard-Prop-shift-Γ (tr𝑃𝑜𝑠 (shiftTy 𝑧𝑝) 𝑖) 𝐴!}

πGirard-PropCtx-shift-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} (𝑖 : 𝑃𝑜𝑠 Γ)
  (α : PropCtx Γ̂ Γ) →
  πGirard-PropCtx (shiftPropCtx-Γ {A = A} 𝑖 α) ≡ πGirard-PropCtx α
πGirard-PropCtx-shift-Γ 𝑖 ∅ = refl
πGirard-PropCtx-shift-Γ 𝑖 (α ⊹ 𝐴) =
  ap₂ _⊹_ (πGirard-PropCtx-shift-Γ 𝑖 α) (πGirard-Prop-shift-Γ 𝑖 𝐴)

πGirard-Prop-shift-γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {⋆ : ⊤} (𝑖 : 𝑃𝑜𝑠 γ)
  (𝐴 : Proposition Γ̂ Γ) →
  πGirard-Prop (shiftProp-n {⋆ = ⋆} 𝑖 𝐴)
    ≡ tr Ty (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑖) Γ̂ ⁻¹) (πGirard-Prop 𝐴)
πGirard-Prop-shift-γ 𝑖 (t ∈ 𝑃𝑉 v) = {!!}
πGirard-Prop-shift-γ 𝑖 (t ∈ 𝑃𝐿 𝐴) = {!!}
πGirard-Prop-shift-γ 𝑖 (𝐴 ⇛ 𝐵) = {!!}
πGirard-Prop-shift-γ 𝑖 (∀𝒳 𝐴) = {!!}
πGirard-Prop-shift-γ 𝑖 (∀x 𝐴) = {!!}
πGirard-Prop-shift-γ 𝑖 (∀X 𝐴) = {!!}

πGirard-PropCtx-shift-γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {⋆ : ⊤} (𝑖 : 𝑃𝑜𝑠 γ)
  (α : PropCtx Γ̂ Γ) →
  πGirard-PropCtx (shiftPropCtx-n {⋆ = ⋆} 𝑖 α)
    ≡ tr Ctx (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑖) Γ̂ ⁻¹) (πGirard-PropCtx α)
πGirard-PropCtx-shift-γ {Γ̂ = Γ̂} 𝑖 ∅ = tr∅ (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑖) Γ̂ ⁻¹) ⁻¹
πGirard-PropCtx-shift-γ {Γ̂ = Γ̂} 𝑖 (α ⊹ 𝐴) =
  ap₂ _⊹_ (πGirard-PropCtx-shift-γ 𝑖 α) (πGirard-Prop-shift-γ 𝑖 𝐴)
  ∙ tr⊹ (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑖) Γ̂ ⁻¹) (map𝐶𝑡𝑥 πGirard-Prop α) (πGirard-Prop 𝐴) ⁻¹

trSwap : {γ δ : TyCtx} (p : γ ≡ δ) {Γ : Ctx δ} {A : Ty γ} →
  Tm (tr Ctx (p ⁻¹) Γ) A → Tm Γ (tr Ty p A)
trSwap refl t = t

πGirard-Prop-Step : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {𝐴 𝐵 : Proposition Γ̂ Γ} →
  Step 𝐴 𝐵 → πGirard-Prop 𝐴 ≡  πGirard-Prop 𝐵
πGirard-Prop-Step ⟨ env₁ ⊚ env₂ ⊚ 𝑅 ⟩ =
  πGirard-Prop-fill env₁ (OTm-fill env₂ _) (OTm-fill env₂ _)
πGirard-Prop-Step ⟨ env₁ ⊚ env₂ ⊚ 𝑅 ⟩⁻¹ =
  πGirard-Prop-fill env₁ (OTm-fill env₂ _) (OTm-fill env₂ _)

πGirard : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {α : PropCtx Γ̂ Γ} {𝐴 : Proposition Γ̂ Γ} →
  Deduction α 𝐴 → Tm (πGirard-PropCtx α) (πGirard-Prop 𝐴)
πGirard (𝐷𝑉 v) = V (tr𝑉𝑎𝑟 πGirard-Prop v)
πGirard (→ᵢ 𝒟) = Lam (πGirard 𝒟)
πGirard (→ₑ 𝒟 ℰ) = App (πGirard 𝒟) (πGirard ℰ)
πGirard {α = α} {∀𝒳 𝐴} (∀⁰ᵢ 𝒟) =
  LAM (tr (λ Γ → Tm Γ (πGirard-Prop 𝐴)) (πGirard-PropCtx-shift-Γ̂ 𝑧𝑝 α) (πGirard 𝒟))
πGirard {α = α} {∀x 𝐴} (∀¹ᵢ 𝒟) =
  tr (λ Γ → Tm Γ (πGirard-Prop 𝐴)) (πGirard-PropCtx-shift-Γ 𝑧𝑝 α) (πGirard 𝒟)
πGirard {Γ̂ = Γ̂} {α = α} {∀X 𝐴} (∀²ᵢ 𝒟) =
  trSwap (map𝐶𝑡𝑥² (λ Â → tt) (shiftTy 𝑧𝑝) Γ̂)
    (tr (λ Γ → Tm Γ (πGirard-Prop 𝐴)) (πGirard-PropCtx-shift-γ 𝑧𝑝 α) (πGirard 𝒟))
πGirard (∀⁰ₑ 𝒟 𝒜) =
  {!APP (πGirard 𝒟) (πGirard-Pred 𝒜)!}
πGirard (∀¹ₑ 𝒟 t) = {!πGirard 𝒟!}
πGirard (∀²ₑ 𝒟 A) = {!πGirard 𝒟!}
πGirard {α = α} (β 𝒟 𝑅) =
  tr (λ A → Tm (πGirard-PropCtx α) A) (πGirard-Prop-Step 𝑅) (πGirard 𝒟)

-- The Reynolds Embedding

{-ιReynolds-VarTy : {γ : TyCtx} {⋆ : ⊤} (v : 𝑉𝑎𝑟 γ ⋆) → Ty γ
ιReynolds-VarTy v = 𝑉 v-}

{-ιReynolds-PredCtx : (γ : TyCtx) → PredCtx γ
ιReynolds-PredCtx γ = map𝑇𝑚𝑠𝐶𝑡𝑥 ιReynolds-VarTy (id𝑅𝑒𝑛 γ)-}

ιReynolds-PredCtx : (γ : TyCtx) → PredCtx γ
ιReynolds-PredCtx ∅ = ∅
ιReynolds-PredCtx (γ ⊹ ⋆) = shiftCtx 𝑧𝑝 (ιReynolds-PredCtx γ) ⊹ 𝑉 𝑧𝑣

ιReynolds-PredVar : {γ : TyCtx} {⋆ : ⊤}
  (v : 𝑉𝑎𝑟 γ ⋆) → PredVar (ιReynolds-PredCtx γ) (𝑉 v)
ιReynolds-PredVar 𝑧𝑣 = 𝑧𝑣
ιReynolds-PredVar (𝑠𝑣 v) = 𝑠𝑣 (tr𝑉𝑎𝑟 (shiftTy 𝑧𝑝) (ιReynolds-PredVar v))

ιReynolds-Ty : {γ : TyCtx} {Γ : Ctx γ} (A : Ty γ) → Predicate (ιReynolds-PredCtx γ) Γ A
ιReynolds-Ty (𝑉 v) = 𝑃𝑉 (ιReynolds-PredVar v)
ιReynolds-Ty (A ⇒ B) =
  𝑃𝐿 {Â = A ⇒ B} (∀x {A = A} ((V 𝑧𝑣 ∈ ιReynolds-Ty A) ⇛ (App (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣) ∈ ιReynolds-Ty B)))
ιReynolds-Ty {Γ = Γ} (∀⋆ A) =
  𝑃𝐿 {Â = ∀⋆ A} (∀X (∀𝒳 {Â = 𝑉 𝑧𝑣} (APP (V 𝑧𝑣) (𝑉 𝑧𝑣) ∈
    tr (λ B → Predicate _ (shiftCtx 𝑧𝑝 (Γ ⊹ ∀⋆ A)) B) (η-helper ∅ A ⁻¹) (ιReynolds-Ty A))))

tr∀𝒳-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ Δ : Ctx γ} {Â : Ty γ}
  (p : Γ ≡ Δ) (𝐴 : Proposition (Γ̂ ⊹ Â) Γ) →
  tr (Proposition Γ̂) p (∀𝒳 𝐴) ≡ ∀𝒳 (tr (Proposition (Γ̂ ⊹ Â)) p 𝐴)
tr∀𝒳-Γ refl 𝐴 = refl

tr∈-Γ : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ Δ : Ctx γ} {A : Ty γ}
  (p : Γ ≡ Δ) (t : Tm Γ A) (𝒜 : Predicate Γ̂ Γ A) →
  tr (Proposition Γ̂) p (t ∈ 𝒜) ≡ tr (λ Γ → Tm Γ A) p t ∈ tr (λ Γ → Predicate Γ̂ Γ A) p 𝒜
tr∈-Γ refl t 𝒜 = refl

ιReynolds-Ty-shiftΓ : {γ : TyCtx} {Γ : Ctx γ} {B : Ty γ} (𝑖 : 𝑃𝑜𝑠 Γ) (A : Ty γ) →
  shiftPred-Γ {A = B} 𝑖 (ιReynolds-Ty A) ≡ ιReynolds-Ty A
ιReynolds-Ty-shiftΓ 𝑖 (𝑉 v) = refl
ιReynolds-Ty-shiftΓ 𝑖 (A ⇒ B) =
  ap₂ (λ x y → 𝑃𝐿 (∀x ((V 𝑧𝑣 ∈ x) ⇛ (App (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣) ∈ y))))
    (ιReynolds-Ty-shiftΓ (𝑠𝑝 (𝑠𝑝 𝑖)) A) (ιReynolds-Ty-shiftΓ (𝑠𝑝 (𝑠𝑝 𝑖)) B)
ιReynolds-Ty-shiftΓ {γ} {Γ} {B} 𝑖 (∀⋆ A) =
  ap 𝑃𝐿 (ap ∀X (tr∀𝒳-Γ (shiftInsert 𝑧𝑝 (𝑠𝑝 𝑖)) _ ∙ ap ∀𝒳
    (tr∈-Γ (shiftInsert 𝑧𝑝 (𝑠𝑝 𝑖)) _ _ ∙ ap₂ _∈_
      {!!}
      {!!})))

ιReynolds-Ctx : {γ : TyCtx} (Γ : Ctx γ) → PropCtx (ιReynolds-PredCtx γ) Γ
ιReynolds-Ctx ∅ = ∅
ιReynolds-Ctx (Γ ⊹ A) = shiftPropCtx-Γ 𝑧𝑝 (ιReynolds-Ctx Γ) ⊹ (V 𝑧𝑣 ∈ ιReynolds-Ty A)

ιReynolds-Var : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ}
  (v : Var Γ A) → PropVar (ιReynolds-Ctx Γ) (V v ∈ ιReynolds-Ty A)
ιReynolds-Var 𝑧𝑣 = 𝑧𝑣
ιReynolds-Var {A = A} (𝑠𝑣 v) =
  𝑠𝑣 (tr (λ A → 𝑉𝑎𝑟 _ (V (𝑠𝑣 v) ∈ A)) (ιReynolds-Ty-shiftΓ 𝑧𝑝 A)
    (tr𝑉𝑎𝑟 (shiftProp-Γ 𝑧𝑝) (ιReynolds-Var v)))

ιReynolds : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ}
  (t : Tm Γ A) → Deduction (ιReynolds-Ctx Γ) (t ∈ ιReynolds-Ty A)
ιReynolds (V v) = 𝐷𝑉 (ιReynolds-Var v)
ιReynolds (Lam t) = {!!}
ιReynolds (App t s) = {!!}
ιReynolds (LAM t) = {!!}
ιReynolds (APP t A) = {!!}

{-# TERMINATING #-}
reduceProp : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} → Proposition Γ̂ Γ → Proposition Γ̂ Γ
reducePred : {γ : TyCtx} {Γ̂ : PredCtx γ} {Γ : Ctx γ} {A : Ty γ} → Predicate Γ̂ Γ A → Predicate Γ̂ Γ A

reducePred (𝑃𝑉 v) = 𝑃𝑉 v
reducePred (𝑃𝐿 𝐴) = 𝑃𝐿 (reduceProp 𝐴)

reduceProp (t ∈ 𝑃𝑉 v) = t ∈ 𝑃𝑉 v
reduceProp (t ∈ 𝑃𝐿 𝐴) = reduceProp (subsTmInProp 𝐴 𝑧𝑣 t)
reduceProp (𝐴 ⇛ 𝐵) = reduceProp 𝐴 ⇛ reduceProp 𝐵
reduceProp (∀𝒳 𝐴) = ∀𝒳 (reduceProp 𝐴)
reduceProp (∀x 𝐴) = ∀x (reduceProp 𝐴)
reduceProp (∀X 𝐴) = ∀X (reduceProp 𝐴)

{-test = reducePred (ιReynolds-Ty {Γ = ∅} (cℕ {∅}))

test' = ιReynolds-Ctx (∅ ⊹ (cℕ {∅}) ⊹ c⊥)-}

--ιReynolds-Tm : 
