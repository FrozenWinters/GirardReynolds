module F2 where

open import lists

--open import Data.Nat renaming (zero to Z; suc to S)

data ⊤ : Type₀ where
  tt : ⊤

-- Round I

TyCtx = 𝐶𝑡𝑥 ⊤
TyVar = 𝑉𝑎𝑟 {ty = ⊤}
TyPos = 𝑃𝑜𝑠 {ty = ⊤}

infixr 20 _⇒_
data Ty : TyCtx → Type₀ where
  𝑉 : {γ : TyCtx} {⋆ : ⊤} → TyVar γ ⋆ → Ty γ
  _⇒_ : {γ : TyCtx} → Ty γ → Ty γ → Ty γ
  ∀⋆ : {γ : TyCtx} {⋆ : ⊤} → Ty (γ ⊹ ⋆) → Ty γ

shiftTy : {γ : TyCtx} {⋆ : ⊤} (𝑖 : TyPos γ) → Ty γ → Ty (insert𝐶𝑡𝑥 𝑖 ⋆)
shiftTy 𝑖 (𝑉 v) = 𝑉 (shift𝑉𝑎𝑟 𝑖 v)
shiftTy 𝑖 (A ⇒ B) = shiftTy 𝑖 A ⇒ shiftTy 𝑖 B
shiftTy 𝑖 (∀⋆ A) = ∀⋆ (shiftTy (𝑠𝑝 𝑖) A)

subsTyVar : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤}
  (v : TyVar γ ⋆₁) → TyVar γ ⋆₂ → Ty (prefix𝑉𝑎𝑟 v) → Ty (remove𝑉𝑎𝑟 v)
subsTyVar 𝑧𝑣 𝑧𝑣 A = A
subsTyVar (𝑠𝑣 v) 𝑧𝑣 A = 𝑉 𝑧𝑣
subsTyVar 𝑧𝑣 (𝑠𝑣 w) A = 𝑉 w
subsTyVar (𝑠𝑣 v) (𝑠𝑣 w) A = shiftTy 𝑧𝑝 (subsTyVar v w A)

subsTy : {γ : TyCtx} {⋆ : ⊤} (v : TyVar γ ⋆) → Ty γ → Ty (prefix𝑉𝑎𝑟 v) → Ty (remove𝑉𝑎𝑟 v)
subsTy v (𝑉 w) A = subsTyVar v w A
subsTy v (B ⇒ C) A = subsTy v B A ⇒ subsTy v C A
subsTy v (∀⋆ B) A = ∀⋆ (subsTy (𝑠𝑣 v) B A)

-- Round II

Ctx : TyCtx → Type₀
Ctx γ = 𝐶𝑡𝑥 (Ty γ)

Var : {γ : TyCtx} → Ctx γ → Ty γ → Type₀
Var {γ} = 𝑉𝑎𝑟 {ty = Ty γ}

CtxPos : {γ : TyCtx} → Ctx γ → Type₀
CtxPos {γ} = 𝑃𝑜𝑠 {ty = Ty γ}

shiftCtx : {γ : TyCtx} {⋆ : ⊤} (𝑖 : TyPos γ) (Γ : Ctx γ) → Ctx (insert𝐶𝑡𝑥 𝑖 ⋆)
shiftCtx 𝑖 = map𝐶𝑡𝑥 (shiftTy 𝑖)

tr𝑉 : {γ δ : TyCtx} {⋆ : ⊤} (p : γ ≡ δ) (v : TyVar γ ⋆) →
  tr Ty p (𝑉 v) ≡ 𝑉 (tr (λ γ → TyVar γ ⋆) p v)
tr𝑉 refl v = refl

tr⇒ : {γ δ : TyCtx} (p : γ ≡ δ) (A B : Ty γ) →
  tr Ty p (A ⇒ B) ≡ tr Ty p A ⇒ tr Ty p B
tr⇒ refl A B = refl

tr∀⋆ : {γ δ : TyCtx} {⋆ : ⊤} (p : γ ≡ δ) (A : Ty (γ ⊹ ⋆)) →
  tr Ty p (∀⋆ A) ≡ ∀⋆ (tr Ty (ap (_⊹ ⋆) p) A)
tr∀⋆ refl A = refl

shiftTy² : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (𝑖 : TyPos γ) (𝑗 : TyPos (prefix𝑃𝑜𝑠 𝑖)) (A : Ty γ) →
  tr (λ γ → Ty γ) (insert𝐶𝑡𝑥² 𝑖 𝑗)
    (shiftTy {⋆ = ⋆₂} (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
  ≡ shiftTy {⋆ = ⋆₁} (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) A)
shiftTy² 𝑖 𝑗 (𝑉 {⋆ = ⋆} v) =
  tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (𝑉 (shift𝑉𝑎𝑟 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shift𝑉𝑎𝑟 𝑖 v)))
    ≡⟨ tr𝑉  (insert𝐶𝑡𝑥² 𝑖 𝑗) (shift𝑉𝑎𝑟 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shift𝑉𝑎𝑟 𝑖 v)) ⟩
  𝑉 (tr (λ γ → TyVar γ ⋆) (insert𝐶𝑡𝑥² 𝑖 𝑗) (shift𝑉𝑎𝑟 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shift𝑉𝑎𝑟 𝑖 v)))
    ≡⟨ ap 𝑉 (shift𝑉𝑎𝑟² 𝑖 𝑗 v) ⟩
  𝑉 (shift𝑉𝑎𝑟 (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shift𝑉𝑎𝑟 (𝑖 + 𝑗) v))
    ∎
shiftTy² 𝑖 𝑗 (A ⇒ B) =
  tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗)
    (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A) ⇒ shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 B))
    ≡⟨ tr⇒ (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
      (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 B)) ⟩
  tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
    ⇒ tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 B))
    ≡⟨ ap (tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A)) ⇒_) (shiftTy² 𝑖 𝑗 B) ⟩
  tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
    ⇒ shiftTy (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) B)
    ≡⟨ ap (_⇒ shiftTy (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) B)) (shiftTy² 𝑖 𝑗 A) ⟩
  shiftTy (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) A) ⇒ shiftTy (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) B)
    ∎
shiftTy² 𝑖 𝑗 (∀⋆ {⋆ = ⋆} A) =
  tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (∀⋆ (shiftTy (𝑠𝑝 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗))) (shiftTy (𝑠𝑝 𝑖) A)))
    ≡⟨ tr∀⋆ (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (𝑠𝑝 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗))) (shiftTy (𝑠𝑝 𝑖) A)) ⟩
  ∀⋆ (tr Ty (ap (_⊹ ⋆) (insert𝐶𝑡𝑥² 𝑖 𝑗)) (shiftTy (𝑠𝑝 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗))) (shiftTy (𝑠𝑝 𝑖) A)))
    ≡⟨ ap ∀⋆ (shiftTy² (𝑠𝑝 𝑖) 𝑗 A) ⟩
  ∀⋆ (shiftTy (𝑠𝑝 (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖)) (shiftTy (𝑠𝑝 (𝑖 + 𝑗)) A))
    ∎

tr∅ : {γ δ : TyCtx} (p : γ ≡ δ) → tr (𝐶𝑡𝑥 ∘ Ty) p ∅ ≡ ∅
tr∅ refl = refl

tr⊹ : {γ δ : TyCtx} (p : γ ≡ δ) (Γ : Ctx γ) (A : Ty γ) →
  tr (𝐶𝑡𝑥 ∘ Ty) p (Γ ⊹ A) ≡ tr (𝐶𝑡𝑥 ∘ Ty) p Γ ⊹ tr Ty p A
tr⊹ refl Γ A = refl

shiftCtx² : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (𝑖 : TyPos γ) (𝑗 : TyPos (prefix𝑃𝑜𝑠 𝑖)) (Γ : Ctx γ) →
  tr (λ γ → Ctx γ) (insert𝐶𝑡𝑥² 𝑖 𝑗)
    (shiftCtx {⋆ = ⋆₂} (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftCtx 𝑖 Γ))
  ≡ shiftCtx {⋆ = ⋆₁} (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftCtx (𝑖 + 𝑗) Γ)
shiftCtx² 𝑖 𝑗 ∅ = tr∅ (insert𝐶𝑡𝑥² 𝑖 𝑗)
shiftCtx² 𝑖 𝑗 (Γ ⊹ A) =
  tr Ctx (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftCtx (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftCtx 𝑖 (Γ ⊹ A)))
    ≡⟨ tr⊹ (insert𝐶𝑡𝑥² 𝑖 𝑗) (map𝐶𝑡𝑥 (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗))) (map𝐶𝑡𝑥 (shiftTy 𝑖) Γ))
      (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A)) ⟩
  tr (𝐶𝑡𝑥 ∘ Ty) (insert𝐶𝑡𝑥² 𝑖 𝑗) (map𝐶𝑡𝑥 (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗))) (map𝐶𝑡𝑥 (shiftTy 𝑖) Γ))
    ⊹ tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
    ≡⟨ ap (_⊹ tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))) (shiftCtx² 𝑖 𝑗 Γ) ⟩
  shiftCtx (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftCtx (𝑖 + 𝑗) Γ)
    ⊹ tr Ty (insert𝐶𝑡𝑥² 𝑖 𝑗) (shiftTy (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗)) (shiftTy 𝑖 A))
    ≡⟨ ap (shiftCtx (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftCtx (𝑖 + 𝑗) Γ) ⊹_) (shiftTy² 𝑖 𝑗 A) ⟩
  shiftCtx (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftCtx (𝑖 + 𝑗) Γ)
    ⊹ shiftTy (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖) (shiftTy (𝑖 + 𝑗) A)
    ∎

shiftPrefixTy : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) →
  Ty (prefix𝑉𝑎𝑟 v) → Ty (prefix𝑉𝑎𝑟 (shift𝑉𝑎𝑟 𝑖 v {⋆₂}))
shiftPrefixTy v 𝑧𝑝 A = A
shiftPrefixTy 𝑧𝑣 (𝑠𝑝 𝑖) A = shiftTy 𝑖 A
shiftPrefixTy (𝑠𝑣 v) (𝑠𝑝 𝑖) A = shiftPrefixTy v 𝑖 A

trShiftTy : {γ δ : TyCtx} {⋆ : ⊤} (p : γ ≡ δ) (A : Ty γ) →
  tr Ty (ap (_⊹ ⋆) p) (shiftTy 𝑧𝑝 A) ≡ shiftTy 𝑧𝑝 (tr Ty p A)
trShiftTy refl A = refl

tr𝑉𝑧𝑣 : {γ δ : TyCtx} {⋆ : ⊤} (p : γ ≡ δ) →
  tr Ty (ap (_⊹ ⋆) p) (𝑉 𝑧𝑣) ≡ 𝑉 𝑧𝑣
tr𝑉𝑧𝑣 refl = refl

shiftSubsTyVar : {γ : TyCtx} {⋆₁ ⋆₂ ⋆₃ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) (w : TyVar γ ⋆₃)
  (B : Ty (prefix𝑉𝑎𝑟 v)) →
  tr (λ δ → Ty δ) (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 (𝑉 w)) (shiftPrefixTy v 𝑖 B))
    ≡ shiftTy {⋆ = ⋆₂} (removed𝑃𝑜𝑠 v 𝑖) (subsTy v (𝑉 w) B)
shiftSubsTyVar v 𝑧𝑝 w B = refl
shiftSubsTyVar 𝑧𝑣 (𝑠𝑝 𝑖) 𝑧𝑣 B = refl
shiftSubsTyVar (𝑠𝑣 v) (𝑠𝑝 𝑖) 𝑧𝑣 B = tr𝑉𝑧𝑣 (insert-remove v 𝑖)
shiftSubsTyVar 𝑧𝑣 (𝑠𝑝 𝑖) (𝑠𝑣 w) B = refl
shiftSubsTyVar {γ = γ ⊹ ⋆} (𝑠𝑣 v) (𝑠𝑝 𝑖) (𝑠𝑣 w) B =
  tr Ty (ap (_⊹ ⋆) (insert-remove v 𝑖))
    (shiftTy 𝑧𝑝 (subsTyVar (shift𝑉𝑎𝑟 𝑖 v) (shift𝑉𝑎𝑟 𝑖 w) (shiftPrefixTy v 𝑖 B)))
    ≡⟨ trShiftTy (insert-remove v 𝑖)
      (subsTyVar (shift𝑉𝑎𝑟 𝑖 v) (shift𝑉𝑎𝑟 𝑖 w) (shiftPrefixTy v 𝑖 B)) ⟩
  shiftTy 𝑧𝑝
    (tr Ty (insert-remove v 𝑖) (subsTyVar (shift𝑉𝑎𝑟 𝑖 v) (shift𝑉𝑎𝑟 𝑖 w) (shiftPrefixTy v 𝑖 B)))
    ≡⟨ ap (shiftTy 𝑧𝑝) (shiftSubsTyVar v 𝑖 w B) ⟩
  shiftTy 𝑧𝑝 (shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTyVar v w B))
    ≡⟨ (shiftTy² 𝑧𝑝 (removed𝑃𝑜𝑠 v 𝑖) (subsTyVar v w B) ⁻¹) ⟩
  shiftTy (𝑠𝑝 (removed𝑃𝑜𝑠 v 𝑖)) (shiftTy 𝑧𝑝 (subsTyVar v w B))
    ∎

shiftSubsTy : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) (A : Ty γ)
  (B : Ty (prefix𝑉𝑎𝑟 v)) →
  tr (λ δ → Ty δ) (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 A) (shiftPrefixTy v 𝑖 B))
    ≡ shiftTy {⋆ = ⋆₂} (removed𝑃𝑜𝑠 v 𝑖) (subsTy v A B)
shiftSubsTy v 𝑖 (𝑉 w) A = shiftSubsTyVar v 𝑖 w A
shiftSubsTy v 𝑖 (B ⇒ C) A =
  tr Ty (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 B) (shiftPrefixTy v 𝑖 A)
    ⇒ subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 C) (shiftPrefixTy v 𝑖 A))
    ≡⟨ tr⇒ (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 B) (shiftPrefixTy v 𝑖 A))
      (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 C) (shiftPrefixTy v 𝑖 A)) ⟩
  tr Ty (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 B) (shiftPrefixTy v 𝑖 A))
    ⇒ tr Ty (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 C) (shiftPrefixTy v 𝑖 A))
    ≡⟨ ap (tr Ty (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 B) (shiftPrefixTy v 𝑖 A)) ⇒_)
      (shiftSubsTy v 𝑖 C A) ⟩
  tr Ty (insert-remove v 𝑖) (subsTy (shift𝑉𝑎𝑟 𝑖 v) (shiftTy 𝑖 B) (shiftPrefixTy v 𝑖 A))
    ⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy v C A)
    ≡⟨ ap (_⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy v C A)) (shiftSubsTy v 𝑖 B A) ⟩
  shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy v B A) ⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy v C A)
    ∎
shiftSubsTy v 𝑖 (∀⋆ {⋆ = ⋆} B) A =
  tr Ty (insert-remove v 𝑖)
    (∀⋆ (subsTy (𝑠𝑣 (shift𝑉𝑎𝑟 𝑖 v)) (shiftTy (𝑠𝑝 𝑖) B) (shiftPrefixTy v 𝑖 A)))
    ≡⟨ tr∀⋆ (insert-remove v 𝑖)
      (subsTy (𝑠𝑣 (shift𝑉𝑎𝑟 𝑖 v)) (shiftTy (𝑠𝑝 𝑖) B) (shiftPrefixTy v 𝑖 A)) ⟩
  ∀⋆ (tr Ty (insert-remove (𝑠𝑣 v) (𝑠𝑝 𝑖))
       (subsTy (shift𝑉𝑎𝑟 (𝑠𝑝 𝑖) (𝑠𝑣 v)) (shiftTy (𝑠𝑝 𝑖) B) (shiftPrefixTy (𝑠𝑣 {B = ⋆} v) (𝑠𝑝 𝑖) A)))
    ≡⟨ ap ∀⋆ (shiftSubsTy (𝑠𝑣 v) (𝑠𝑝 𝑖) B A) ⟩
  ∀⋆ (shiftTy (𝑠𝑝 (removed𝑃𝑜𝑠 v 𝑖)) (subsTy (𝑠𝑣 v) B A))
    ∎

shiftVar-γ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty γ}
  (𝑖 : TyPos γ) → Var Γ A → Var (shiftCtx {⋆ = ⋆} 𝑖 Γ) (shiftTy 𝑖 A)
shiftVar-γ 𝑖 v = tr𝑉𝑎𝑟 (shiftTy 𝑖) v

shiftCtxPos-γ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ}
  (𝑗 : TyPos γ) (𝑖 : CtxPos Γ) → CtxPos (shiftCtx {⋆ = ⋆} 𝑗 Γ)
shiftCtxPos-γ 𝑗 𝑖 = tr𝑃𝑜𝑠 (shiftTy 𝑗) 𝑖

shiftInsert : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty γ} (𝑗 : TyPos γ) (𝑖 : CtxPos Γ) →
  insert𝐶𝑡𝑥 (shiftCtxPos-γ {⋆ = ⋆} 𝑗 𝑖) (shiftTy 𝑗 A) ≡ shiftCtx 𝑗 (insert𝐶𝑡𝑥 𝑖 A)
shiftInsert 𝑗 𝑧𝑝 = refl
shiftInsert {Γ = Γ ⊹ A} 𝑗 (𝑠𝑝 𝑖) = ap (_⊹  shiftTy 𝑗 A) (shiftInsert 𝑗 𝑖)

data Tm : {γ : TyCtx} → Ctx γ → Ty γ → Type₀ where
  V : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} →
    Var Γ A → Tm Γ A
  Lam : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
    Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
    Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  LAM : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty (γ ⊹ ⋆)} →
    Tm (shiftCtx 𝑧𝑝 Γ) A → Tm Γ (∀⋆ A)
  APP : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty (γ ⊹ ⋆)} →
    Tm Γ (∀⋆ A) → (B : Ty γ) → Tm Γ (subsTy 𝑧𝑣 A B)

shiftTm : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} (𝑖 : CtxPos Γ) → Tm Γ B → Tm (insert𝐶𝑡𝑥 𝑖 A) B
shiftTm 𝑖 (V v) = V (shift𝑉𝑎𝑟 𝑖 v)
shiftTm 𝑖 (Lam t) = Lam (shiftTm (𝑠𝑝 𝑖) t)
shiftTm 𝑖 (App t s) = App (shiftTm 𝑖 t) (shiftTm 𝑖 s)
shiftTm {B = ∀⋆ A} 𝑖 (LAM t) =
  LAM (tr (λ Δ → Tm Δ A) (shiftInsert 𝑧𝑝 𝑖) (shiftTm (shiftCtxPos-γ 𝑧𝑝 𝑖) t))
shiftTm 𝑖 (APP t A) = APP (shiftTm 𝑖 t) A

shiftTm-γ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty γ}
  (𝑖 : TyPos γ) → Tm Γ A → Tm (shiftCtx {⋆ = ⋆} 𝑖 Γ) (shiftTy 𝑖 A)
shiftTm-γ 𝑖 (V v) = V (shiftVar-γ 𝑖 v)
shiftTm-γ 𝑖 (Lam t) = Lam (shiftTm-γ 𝑖 t)
shiftTm-γ 𝑖 (App t s) = App (shiftTm-γ 𝑖 t) (shiftTm-γ 𝑖 s)
shiftTm-γ 𝑖 (LAM {Γ = Γ} {A} t) =
  LAM (tr (λ Γ → Tm Γ (shiftTy (𝑠𝑝 𝑖) A)) (shiftCtx² 𝑧𝑝 𝑖 Γ) (shiftTm-γ (𝑠𝑝 𝑖) t))
shiftTm-γ {⋆ = ⋆₁} 𝑖 (APP {⋆ = ⋆₂}{Γ = Γ} {B} t A) =
  tr (λ A → Tm (shiftCtx 𝑖 Γ) A) (shiftSubsTy 𝑧𝑣 (𝑠𝑝 𝑖) B A) (APP (shiftTm-γ 𝑖 t) (shiftTy 𝑖 A))

-- Some tests

cℕ : {Γ : TyCtx} → Ty Γ
cℕ = ∀⋆ {⋆ = tt} ((𝑉 𝑧𝑣 ⇒ 𝑉 𝑧𝑣) ⇒ 𝑉 𝑧𝑣 ⇒ 𝑉 𝑧𝑣)

c⊥ : {Γ : TyCtx} → Ty Γ
c⊥ = ∀⋆ {⋆ = tt} (𝑉 𝑧𝑣)

test1 : Tm {∅} ∅ cℕ
test1 = LAM (Lam (Lam (App (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣))))

test2 = APP test1 c⊥
