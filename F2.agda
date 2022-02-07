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

subsTyVar : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} →
  TyVar γ ⋆₁ → (v : TyVar γ ⋆₂) → Ty (prefix𝑉𝑎𝑟 v) → Ty (remove𝑉𝑎𝑟 v)
subsTyVar = subs𝑉𝑎𝑟 𝑉 shiftTy

subsTy : {γ : TyCtx} {⋆ : ⊤} → Ty γ → (v : TyVar γ ⋆) → Ty (prefix𝑉𝑎𝑟 v) → Ty (remove𝑉𝑎𝑟 v)
subsTy (𝑉 w) v A = subsTyVar w v A
subsTy (B ⇒ C) v A = subsTy B v A ⇒ subsTy C v A
subsTy (∀⋆ B) v A = ∀⋆ (subsTy B (𝑠𝑣 v) A)

-- Round II

Ctx : TyCtx → Type₀
Ctx γ = 𝐶𝑡𝑥 (Ty γ)

Var : {γ : TyCtx} → Ctx γ → Ty γ → Type₀
Var {γ} = 𝑉𝑎𝑟 {ty = Ty γ}

CtxPos : {γ : TyCtx} → Ctx γ → Type₀
CtxPos {γ} = 𝑃𝑜𝑠 {ty = Ty γ}

shiftCtx : {γ : TyCtx} {⋆ : ⊤} (𝑖 : TyPos γ) (Γ : Ctx γ) → Ctx (insert𝐶𝑡𝑥 𝑖 ⋆)
shiftCtx 𝑖 = map𝐶𝑡𝑥 (shiftTy 𝑖)

subsCtx : {γ : TyCtx} {⋆ : ⊤} → Ctx γ → (v : TyVar γ ⋆) → Ty (prefix𝑉𝑎𝑟 v) → Ctx (remove𝑉𝑎𝑟 v)
subsCtx Γ 𝑖 A = map𝐶𝑡𝑥 (λ B → subsTy B 𝑖 A) Γ 

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

tr𝑉𝑠𝑣 : {γ δ : TyCtx} {⋆₁ ⋆₂ : ⊤} (p : γ ≡ δ) (v : TyVar γ ⋆₁) →
  tr Ty (ap (_⊹ ⋆₂) p) (𝑉 (𝑠𝑣 v)) ≡ 𝑉 (𝑠𝑣 (tr (λ γ → TyVar γ ⋆₁) p v))
tr𝑉𝑠𝑣 refl v = refl

shiftSubsTyVar : {γ : TyCtx} {⋆₁ ⋆₂ ⋆₃ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) (w : TyVar γ ⋆₃)
  (B : Ty (prefix𝑉𝑎𝑟 v)) →
  tr (λ δ → Ty δ) (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 (𝑉 w)) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ≡ shiftTy {⋆ = ⋆₂} (removed𝑃𝑜𝑠 v 𝑖) (subsTy (𝑉 w) v B)
shiftSubsTyVar v 𝑧𝑝 w B = refl
shiftSubsTyVar 𝑧𝑣 (𝑠𝑝 𝑖) 𝑧𝑣 B = refl
shiftSubsTyVar (𝑠𝑣 v) (𝑠𝑝 𝑖) 𝑧𝑣 B = tr𝑉𝑧𝑣 (insert-remove v 𝑖)
shiftSubsTyVar 𝑧𝑣 (𝑠𝑝 𝑖) (𝑠𝑣 w) B = refl
shiftSubsTyVar {γ = γ ⊹ ⋆} (𝑠𝑣 v) (𝑠𝑝 𝑖) (𝑠𝑣 w) B =
  tr Ty (ap (_⊹ ⋆) (insert-remove v 𝑖))
    (shiftTy 𝑧𝑝 (subsTyVar (shift𝑉𝑎𝑟 𝑖 w) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B)))
    ≡⟨ trShiftTy (insert-remove v 𝑖)
      (subsTyVar (shift𝑉𝑎𝑟 𝑖 w) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B)) ⟩
  shiftTy 𝑧𝑝
    (tr Ty (insert-remove v 𝑖) (subsTyVar (shift𝑉𝑎𝑟 𝑖 w) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B)))
    ≡⟨ ap (shiftTy 𝑧𝑝) (shiftSubsTyVar v 𝑖 w B) ⟩
  shiftTy 𝑧𝑝 (shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTyVar w v B))
    ≡⟨ (shiftTy² 𝑧𝑝 (removed𝑃𝑜𝑠 v 𝑖) (subsTyVar w v B) ⁻¹) ⟩
  shiftTy (𝑠𝑝 (removed𝑃𝑜𝑠 v 𝑖)) (shiftTy 𝑧𝑝 (subsTyVar w v B))
    ∎

shiftSubsTy : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) (A : Ty γ)
  (B : Ty (prefix𝑉𝑎𝑟 v)) →
  tr (λ δ → Ty δ) (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 A) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ≡ shiftTy {⋆ = ⋆₂} (removed𝑃𝑜𝑠 v 𝑖) (subsTy A v B)
shiftSubsTy v 𝑖 (𝑉 w) A = shiftSubsTyVar v 𝑖 w A
shiftSubsTy v 𝑖 (B ⇒ C) A =
  tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 B) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A)
    ⇒ subsTy (shiftTy 𝑖 C) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A))
    ≡⟨ tr⇒ (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 B) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A))
      (subsTy (shiftTy 𝑖 C) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A)) ⟩
  tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 B) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A))
    ⇒ tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 C) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A))
    ≡⟨ ap (tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 B) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A)) ⇒_)
      (shiftSubsTy v 𝑖 C A) ⟩
  tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 B) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 A))
    ⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy C v A)
    ≡⟨ ap (_⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy C v A)) (shiftSubsTy v 𝑖 B A) ⟩
  shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy B v A) ⇒ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy C v A)
    ∎
shiftSubsTy v 𝑖 (∀⋆ {⋆ = ⋆} B) A =
  tr Ty (insert-remove v 𝑖)
    (∀⋆ (subsTy (shiftTy (𝑠𝑝 𝑖) B) (𝑠𝑣 (shift𝑉𝑎𝑟 𝑖 v)) (shiftPrefixTy v 𝑖 A)))
    ≡⟨ tr∀⋆ (insert-remove v 𝑖)
      (subsTy (shiftTy (𝑠𝑝 𝑖) B) (𝑠𝑣 (shift𝑉𝑎𝑟 𝑖 v)) (shiftPrefixTy v 𝑖 A)) ⟩
  ∀⋆ (tr Ty (insert-remove (𝑠𝑣 v) (𝑠𝑝 𝑖))
       (subsTy (shiftTy (𝑠𝑝 𝑖) B) (shift𝑉𝑎𝑟 (𝑠𝑝 𝑖) (𝑠𝑣 v)) (shiftPrefixTy (𝑠𝑣 {B = ⋆} v) (𝑠𝑝 𝑖) A)))
    ≡⟨ ap ∀⋆ (shiftSubsTy (𝑠𝑣 v) (𝑠𝑝 𝑖) B A) ⟩
  ∀⋆ (shiftTy (𝑠𝑝 (removed𝑃𝑜𝑠 v 𝑖)) (subsTy B (𝑠𝑣 v) A))
    ∎

shiftSubsCtx : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (𝑖 : TyPos γ) (Γ : Ctx γ)
  (B : Ty (prefix𝑉𝑎𝑟 v)) →
  tr (λ δ → Ctx δ) (insert-remove v 𝑖) (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ≡ shiftCtx {⋆ = ⋆₂} (removed𝑃𝑜𝑠 v 𝑖) (subsCtx Γ v B)
shiftSubsCtx v 𝑖 ∅ B = tr∅ (insert-remove v 𝑖)
shiftSubsCtx v 𝑖 (Γ ⊹ A) B =
  tr Ctx (insert-remove v 𝑖)
    (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B)
      ⊹ subsTy (shiftTy 𝑖 A) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ≡⟨ tr⊹ (insert-remove v 𝑖) (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
      (subsTy (shiftTy 𝑖 A) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B)) ⟩
  tr Ctx (insert-remove v 𝑖) (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ⊹ tr Ty (insert-remove v 𝑖) (subsTy (shiftTy 𝑖 A) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ≡⟨ ap (tr Ctx (insert-remove v 𝑖) (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
      ⊹_) (shiftSubsTy v 𝑖 A B) ⟩
  tr Ctx (insert-remove v 𝑖) (subsCtx (shiftCtx 𝑖 Γ) (shift𝑉𝑎𝑟 𝑖 v) (shiftPrefixTy v 𝑖 B))
    ⊹ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy A v B)
    ≡⟨ ap (_⊹ shiftTy (removed𝑃𝑜𝑠 v 𝑖) (subsTy A v B)) (shiftSubsCtx v 𝑖 Γ B) ⟩
  shiftCtx (removed𝑃𝑜𝑠 v 𝑖) (subsCtx (Γ ⊹ A) v B)
    ∎

removePrefixTy : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (w : TyVar (remove𝑉𝑎𝑟 v) ⋆₂) →
  Ty (prefix𝑉𝑎𝑟 v) → Ty (prefix𝑉𝑎𝑟 w) → Ty (prefix𝑉𝑎𝑟 (swapRemove𝑉𝑎𝑟 v w))
removePrefixTy 𝑧𝑣 w A B = subsTy A w B
removePrefixTy (𝑠𝑣 v) 𝑧𝑣 A B = A
removePrefixTy (𝑠𝑣 v) (𝑠𝑣 w) A B = removePrefixTy v w A B

reinsertPrefixTy : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (v : TyVar γ ⋆₁) (w : TyVar (remove𝑉𝑎𝑟 v) ⋆₂) →
  Ty (prefix𝑉𝑎𝑟 v) → Ty (prefix𝑉𝑎𝑟 w) → Ty (prefix𝑉𝑎𝑟 (reinsert𝑉𝑎𝑟 v w))
reinsertPrefixTy 𝑧𝑣 w A B = B
reinsertPrefixTy (𝑠𝑣 v) 𝑧𝑣 A B = tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) B)
reinsertPrefixTy (𝑠𝑣 v) (𝑠𝑣 w) A B = reinsertPrefixTy v w A B

subsShiftVar : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤}
  (v : TyVar γ ⋆₁) (w : TyVar (remove𝑉𝑎𝑟 v) ⋆₂) (B : Ty (prefix𝑉𝑎𝑟 v)) →
  subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) (𝑉 w))) v B ≡ 𝑉 w
subsShiftVar 𝑧𝑣 w B = refl
subsShiftVar (𝑠𝑣 v) 𝑧𝑣 B = ap (λ x → subsTy x (𝑠𝑣 v) B) (tr𝑉𝑧𝑣 (insert-removal v))
subsShiftVar {γ = γ ⊹ ⋆} {⋆₂ = ⋆₂} (𝑠𝑣 v) (𝑠𝑣 w) B =
  subsTy (tr Ty (ap (_⊹ ⋆) (insert-removal v)) (𝑉 (𝑠𝑣 (shift𝑉𝑎𝑟 (removal𝑃𝑜𝑠 v) w)))) (𝑠𝑣 v) B
    ≡⟨ ap (λ x → subsTy x (𝑠𝑣 v) B) (tr𝑉𝑠𝑣 (insert-removal v) (shift𝑉𝑎𝑟 (removal𝑃𝑜𝑠 v) w)) ⟩
  shiftTy 𝑧𝑝 (subsTy (𝑉 (tr (λ γ₁ → 𝑉𝑎𝑟 γ₁ ⋆₂) (insert-removal v) (shift𝑉𝑎𝑟 (removal𝑃𝑜𝑠 v) w))) v B)
    ≡⟨ ap (λ x → shiftTy 𝑧𝑝 (subsTy x v B))
      (tr𝑉 (insert-removal v) (shift𝑉𝑎𝑟 (removal𝑃𝑜𝑠 v) w) ⁻¹) ⟩
  shiftTy 𝑧𝑝 (subsTy (tr Ty (insert-removal v) (𝑉 (shift𝑉𝑎𝑟 (removal𝑃𝑜𝑠 v) w))) v B)
    ≡⟨ ap (shiftTy 𝑧𝑝) (subsShiftVar v w B) ⟩
  𝑉 (𝑠𝑣 w)
    ∎

subsShiftTy : {γ : TyCtx} {⋆ : ⊤} (v : TyVar γ ⋆) (A : Ty (remove𝑉𝑎𝑟 v)) (B : Ty (prefix𝑉𝑎𝑟 v)) →
  subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A)) v B ≡ A
subsShiftTy v (𝑉 w) B = subsShiftVar v w B
subsShiftTy v (A₁ ⇒ A₂) B =
  subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₁ ⇒ shiftTy (removal𝑃𝑜𝑠 v) A₂)) v B
    ≡⟨ ap (λ x → subsTy x v B)
      (tr⇒ (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₁) (shiftTy (removal𝑃𝑜𝑠 v) A₂)) ⟩
  subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₁)) v B
    ⇒ subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₂)) v B
    ≡⟨ ap (subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₁)) v B ⇒_)
      (subsShiftTy v A₂ B) ⟩
  subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) A₁)) v B ⇒ A₂
    ≡⟨ ap (_⇒ A₂) (subsShiftTy v A₁ B) ⟩
  A₁ ⇒ A₂
    ∎
subsShiftTy v (∀⋆ {⋆ = ⋆} A) B =
  subsTy (tr Ty (insert-removal v) (∀⋆ (shiftTy (𝑠𝑝 (removal𝑃𝑜𝑠 v)) A))) v B
    ≡⟨ ap (λ x → subsTy x v B) (tr∀⋆ (insert-removal v) (shiftTy (𝑠𝑝 (removal𝑃𝑜𝑠 v)) A)) ⟩
  ∀⋆ (subsTy (tr Ty (ap (_⊹ ⋆) (insert-removal v)) (shiftTy (𝑠𝑝 (removal𝑃𝑜𝑠 v)) A)) (𝑠𝑣 v) B)
    ≡⟨ ap ∀⋆ (subsShiftTy (𝑠𝑣 v) A B) ⟩
  ∀⋆ A
    ∎

subsShiftCtx : {γ : TyCtx} {⋆ : ⊤} (v : TyVar γ ⋆) (Γ : Ctx (remove𝑉𝑎𝑟 v)) (A : Ty (prefix𝑉𝑎𝑟 v)) →
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) Γ)) v A ≡ Γ
subsShiftCtx v ∅ A = ap (λ x → subsCtx x v A) (tr∅ (insert-removal v))
subsShiftCtx v (Γ ⊹ B) A =
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) (Γ ⊹ B))) v A
    ≡⟨ ap (λ x → subsCtx x v A) (tr⊹ (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) Γ)
      (shiftTy (removal𝑃𝑜𝑠 v) B)) ⟩
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) Γ)) v A
    ⊹ subsTy (tr Ty (insert-removal v) (shiftTy (removal𝑃𝑜𝑠 v) B)) v A
    ≡⟨ ap (subsCtx (tr Ctx (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) Γ)) v A ⊹_)
      (subsShiftTy v B A) ⟩
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removal𝑃𝑜𝑠 v) Γ)) v A ⊹ B
    ≡⟨ ap (_⊹ B) (subsShiftCtx v Γ A) ⟩
  Γ ⊹ B
    ∎

subsVar² : {γ : TyCtx} {⋆ ⋆₁ ⋆₂ : ⊤} (u : TyVar γ ⋆) (v : TyVar γ ⋆₁)
  (w : TyVar (remove𝑉𝑎𝑟 v) ⋆₂) (B : Ty (prefix𝑉𝑎𝑟 v)) (C : Ty (prefix𝑉𝑎𝑟 w)) →
  tr Ty (remove-swap v w) (subsTy (subsTy (𝑉 u) (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
    (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
    ≡ subsTy (subsTy (𝑉 u) v B) w C
subsVar² 𝑧𝑣 𝑧𝑣 w B C = refl
subsVar² (𝑠𝑣 u) 𝑧𝑣 w B C = subsShiftTy 𝑧𝑣 (subsTyVar u w C) (subsTy B w C)
subsVar² 𝑧𝑣 (𝑠𝑣 v) 𝑧𝑣 B C = subsShiftTy v C B
subsVar² 𝑧𝑣 (𝑠𝑣 v) (𝑠𝑣 w) B C = tr𝑉𝑧𝑣 (remove-swap v w)
subsVar² (𝑠𝑣 u) (𝑠𝑣 v) 𝑧𝑣 B C = subsShiftTy 𝑧𝑣 (subsTyVar u v B) C ⁻¹
subsVar² {γ = γ ⊹ ⋆} (𝑠𝑣 u) (𝑠𝑣 v) (𝑠𝑣 w) B C =
  tr Ty (ap (_⊹ ⋆) (remove-swap v w)) (subsTy (shiftTy 𝑧𝑝 (subs𝑉𝑎𝑟 𝑉 shiftTy u (reinsert𝑉𝑎𝑟 v w)
    (reinsertPrefixTy v w B C))) (𝑠𝑣 (swapRemove𝑉𝑎𝑟 v w)) (removePrefixTy v w B C))
    ≡⟨ ap (tr Ty (ap (_⊹ ⋆) (remove-swap v w))) (shiftSubsTy (swapRemove𝑉𝑎𝑟 v w) 𝑧𝑝
      (subsTy (𝑉 u) (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C)) (removePrefixTy v w B C)) ⟩
  tr Ty (ap (_⊹ ⋆) (remove-swap v w)) (shiftTy 𝑧𝑝 (subsTy (subsTyVar u (reinsert𝑉𝑎𝑟 v w)
    (reinsertPrefixTy v w B C)) (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)))
    ≡⟨ trShiftTy (remove-swap v w) (subsTy (subsTyVar u (reinsert𝑉𝑎𝑟 v w)
      (reinsertPrefixTy v w B C)) (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)) ⟩
  shiftTy 𝑧𝑝 (tr Ty (remove-swap v w) (subsTy (subsTyVar u (reinsert𝑉𝑎𝑟 v w)
    (reinsertPrefixTy v w B C)) (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)))
    ≡⟨ ap (shiftTy 𝑧𝑝) (subsVar² u v w B C) ⟩
  shiftTy 𝑧𝑝 (subsTy (subsTyVar u v B) w C)
    ≡⟨ shiftSubsTy w 𝑧𝑝 (subsTyVar u v B) C ⁻¹ ⟩
  subsTy (shiftTy 𝑧𝑝 (subsTyVar u v B)) (𝑠𝑣 w) C
    ∎

subsTy² : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (A : Ty γ) (v : TyVar γ ⋆₁) (w : TyVar (remove𝑉𝑎𝑟 v) ⋆₂)
  (B : Ty (prefix𝑉𝑎𝑟 v)) (C : Ty (prefix𝑉𝑎𝑟 w)) →
  tr Ty (remove-swap v w) (subsTy (subsTy A (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
    (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
    ≡ subsTy (subsTy A v B) w C
subsTy² (𝑉 u) v w B C = subsVar² u v w B C
subsTy² (A₁ ⇒ A₂) v w B C =
  tr Ty (remove-swap v w) (subsTy (subsTy A₁ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
    (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)
      ⇒ subsTy (subsTy A₂ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
        (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
    ≡⟨ tr⇒ (remove-swap v w)
      (subsTy (subsTy A₁ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
        (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
      (subsTy (subsTy A₂ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
        (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)) ⟩
  tr Ty (remove-swap v w) (subsTy (subsTy A₁ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
    (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
    ⇒ tr Ty (remove-swap v w) (subsTy (subsTy A₂ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
      (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C))
    ≡⟨ ap (tr Ty (remove-swap v w) (subsTy (subsTy A₁ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
      (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)) ⇒_) (subsTy² A₂ v w B C) ⟩
  tr Ty (remove-swap v w) (subsTy (subsTy A₁ (reinsert𝑉𝑎𝑟 v w) (reinsertPrefixTy v w B C))
    (swapRemove𝑉𝑎𝑟 v w) (removePrefixTy v w B C)) ⇒ subsTy (subsTy A₂ v B) w C
    ≡⟨ ap (_⇒ subsTy (subsTy A₂ v B) w C) (subsTy² A₁ v w B C) ⟩
  subsTy (subsTy A₁ v B) w C ⇒ subsTy (subsTy A₂ v B) w C
    ∎
subsTy² (∀⋆ {⋆ = ⋆} A) v w B C =
  tr Ty (remove-swap v w) (∀⋆ (subsTy (subsTy A (𝑠𝑣 (reinsert𝑉𝑎𝑟 v w))
    (reinsertPrefixTy v w B C)) (𝑠𝑣 (swapRemove𝑉𝑎𝑟 v w)) (removePrefixTy v w B C)))
    ≡⟨ tr∀⋆ (remove-swap v w) (subsTy (subsTy A (𝑠𝑣 (reinsert𝑉𝑎𝑟 v w))
      (reinsertPrefixTy v w B C)) (𝑠𝑣 (swapRemove𝑉𝑎𝑟 v w)) (removePrefixTy v w B C)) ⟩
  ∀⋆ (tr Ty (ap (_⊹ ⋆) (remove-swap v w)) (subsTy (subsTy A (𝑠𝑣 (reinsert𝑉𝑎𝑟 v w))
    (reinsertPrefixTy v w B C)) (𝑠𝑣 (swapRemove𝑉𝑎𝑟 v w)) (removePrefixTy v w B C)))
    ≡⟨ ap ∀⋆ (subsTy² A (𝑠𝑣 v) (𝑠𝑣 w) B C) ⟩
  ∀⋆ (subsTy (subsTy A (𝑠𝑣 v) B) (𝑠𝑣 w) C)
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

shiftRemove : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty γ} (𝑖 : TyPos γ) (v : Var Γ A) →
  shiftCtx {⋆ = ⋆} 𝑖 (remove𝑉𝑎𝑟 v) ≡ remove𝑉𝑎𝑟 (shiftVar-γ 𝑖 v)
shiftRemove 𝑖 𝑧𝑣 = refl
shiftRemove {Γ = Γ ⊹ A} 𝑖 (𝑠𝑣 v) = ap (_⊹ shiftTy 𝑖 A) (shiftRemove 𝑖 v)

shiftPrefix : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty γ} (𝑖 : TyPos γ) (v : Var Γ A) →
  shiftCtx {⋆ = ⋆} 𝑖 (prefix𝑉𝑎𝑟 v) ≡ prefix𝑉𝑎𝑟 (shiftVar-γ 𝑖 v)
shiftPrefix 𝑖 𝑧𝑣 = refl
shiftPrefix 𝑖 (𝑠𝑣 v) = shiftPrefix 𝑖 v

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
    Tm Γ (∀⋆ A) → (B : Ty γ) → Tm Γ (subsTy A 𝑧𝑣 B)

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

subsVar : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
  Var Γ B → (v : Var Γ A) → Tm (prefix𝑉𝑎𝑟 v) A → Tm (remove𝑉𝑎𝑟 v) B
subsVar = subs𝑉𝑎𝑟 V shiftTm

subsTm : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
  Tm Γ B → (v : Var Γ A) → Tm (prefix𝑉𝑎𝑟 v) A → Tm (remove𝑉𝑎𝑟 v) B
subsTm (V w) v s = subsVar w v s
subsTm (Lam t) v s = Lam (subsTm t (𝑠𝑣 v) s)
subsTm (App t₁ t₂) v s = App (subsTm t₁ v s) (subsTm t₂ v s)
subsTm {A = B} (LAM {A = A} t) v s =
  LAM (tr (λ Γ → Tm Γ A) (shiftRemove 𝑧𝑝 v ⁻¹)
    (subsTm t (shiftVar-γ 𝑧𝑝 v)
      (tr (λ Γ → Tm Γ (shiftTy 𝑧𝑝 B)) (shiftPrefix 𝑧𝑝 v) (shiftTm-γ 𝑧𝑝 s))))
subsTm (APP t A) v s = APP (subsTm t v s) A

subsVar-γ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {B : Ty γ} →
  Var Γ B → (v : TyVar γ ⋆) (A : Ty (prefix𝑉𝑎𝑟 v)) → Var (subsCtx Γ v A) (subsTy B v A)
subsVar-γ w v A = tr𝑉𝑎𝑟 (λ B → subsTy B v A) w 

subsTm-γ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {B : Ty γ} →
  Tm Γ B → (v : TyVar γ ⋆) (A : Ty (prefix𝑉𝑎𝑟 v)) → Tm (subsCtx Γ v A) (subsTy B v A)
subsTm-γ (V w) v A = V (subsVar-γ w v A)
subsTm-γ (Lam t) v A = Lam (subsTm-γ t v A)
subsTm-γ (App t s) v A = App (subsTm-γ t v A) (subsTm-γ s v A)
subsTm-γ (LAM {Γ = Γ} {B} t) v A =
  LAM (tr (λ Γ → Tm Γ (subsTy B (𝑠𝑣 v) A)) (shiftSubsCtx v 𝑧𝑝 Γ A) (subsTm-γ t (𝑠𝑣 v) A))
subsTm-γ (APP {Γ = Γ} {C} t B) v A =
  tr (λ C → Tm (subsCtx Γ v A) C) (subsTy² C 𝑧𝑣 v B A)
   (APP (subsTm-γ t v A) (subsTy B v A))

-- Round III

η-helperVar : {γ : TyCtx} {⋆₁ ⋆₂ : ⊤} (δ : TyCtx) (v : TyVar ((γ ⊹ ⋆₁) ⊹⊹ δ) ⋆₂) →
  tr Ty (remove++ 𝑧𝑣 δ) (subsTyVar (tr (λ γ₁ → TyVar γ₁ ⋆₂) (insert++ (𝑠𝑝 𝑧𝑝) δ)
    (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))) ≡ 𝑉 v
η-helperVar ∅ 𝑧𝑣 = refl
η-helperVar ∅ (𝑠𝑣 v) = refl
η-helperVar (δ ⊹ ⋆) 𝑧𝑣 =
  tr Ty (remove++ 𝑧𝑣 (δ ⊹ ⋆)) (subsTyVar (tr (λ γ₁ → TyVar γ₁ ⋆)
    (ap (_⊹ ⋆) (insert++ (𝑠𝑝 𝑧𝑝) δ)) 𝑧𝑣) (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ)) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap (λ x → tr Ty (remove++ 𝑧𝑣 (δ ⊹ ⋆)) (subsTyVar x (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ))
      (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))) (tr𝑧𝑣 (insert++ (𝑠𝑝 𝑧𝑝) δ)) ⟩
  tr Ty (ap (_⊹ ⋆) (remove++ 𝑧𝑣 δ)) (𝑉 𝑧𝑣)
    ≡⟨ tr𝑉𝑧𝑣 (remove++ 𝑧𝑣 δ) ⟩
  𝑉 𝑧𝑣
    ∎
η-helperVar (δ ⊹ ⋆) (𝑠𝑣 v) =
  tr Ty (remove++ 𝑧𝑣 (δ ⊹ ⋆)) (subsTyVar (tr (λ γ₁ → TyVar γ₁ _) (ap (_⊹ ⋆) (insert++ (𝑠𝑝 𝑧𝑝) δ))
    (𝑠𝑣 (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v))) (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ)) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap (λ x → tr Ty (remove++ 𝑧𝑣 (δ ⊹ ⋆)) (subsTyVar x (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ))
      (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))) (tr𝑠𝑣 (insert++ (𝑠𝑝 𝑧𝑝) δ) (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) ⟩
  tr Ty (ap (_⊹ ⋆) (remove++ 𝑧𝑣 δ)) (shiftTy 𝑧𝑝 (subsTyVar (tr (λ Σ → 𝑉𝑎𝑟 Σ _) (insert++ (𝑠𝑝 𝑧𝑝) δ)
    (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
    ≡⟨ trShiftTy (remove++ 𝑧𝑣 δ) (subsTyVar (tr (λ Σ → 𝑉𝑎𝑟 Σ _) (insert++ (𝑠𝑝 𝑧𝑝) δ)
      (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))) ⟩
  shiftTy 𝑧𝑝 (tr Ty (remove++ 𝑧𝑣 δ) (subsTyVar (tr (λ Σ → 𝑉𝑎𝑟 Σ _) (insert++ (𝑠𝑝 𝑧𝑝) δ)
    (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
    ≡⟨ ap (shiftTy 𝑧𝑝) (η-helperVar δ v) ⟩
  𝑉 (𝑠𝑣 v)
    ∎

η-helper : {γ : TyCtx} {⋆ : ⊤} (δ : TyCtx) (A : Ty ((γ ⊹ ⋆) ⊹⊹ δ)) →
  tr Ty (remove++ 𝑧𝑣 δ)
    (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy {⋆ = ⋆} (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A)) (𝑧𝑣 ++𝑉𝑎𝑟 δ)
      (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))) ≡ A
η-helper δ (𝑉 v) =
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (𝑉 (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap (λ x → tr Ty (remove++ 𝑧𝑣 δ) (subsTy x (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
      (tr𝑉 (insert++ (𝑠𝑝 𝑧𝑝) δ) (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) ⟩
  tr Ty (remove++ 𝑧𝑣 δ) (subsTyVar (tr (λ γ₁ → TyVar γ₁ _) (insert++ (𝑠𝑝 𝑧𝑝) δ)
    (shift𝑉𝑎𝑟 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) v)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ η-helperVar δ v ⟩
  𝑉 v
    ∎
η-helper δ (A ⇒ B) =
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A
    ⇒
  shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) B)) (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap (λ x → tr Ty (remove++ 𝑧𝑣 δ) (subsTy x (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
      (tr⇒ (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) B)) ⟩
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))
    ⇒
  subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) B))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ tr⇒ (remove++ 𝑧𝑣 δ)
      (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A))
        (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
      (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) B))
        (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))) ⟩
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) A))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ⇒
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ) B))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap₂ _⇒_ (η-helper δ A) (η-helper δ B) ⟩
  A ⇒ B
    ∎
η-helper δ (∀⋆ {⋆ = ⋆} A) =
  tr Ty (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) δ) (∀⋆ (shiftTy (𝑠𝑝 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ)) A)))
    (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣)))
    ≡⟨ ap (λ x → tr Ty (remove++ 𝑧𝑣 δ) (subsTy x (𝑧𝑣 ++𝑉𝑎𝑟 δ) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
      (tr∀⋆ (insert++ (𝑠𝑝 𝑧𝑝) δ) (shiftTy (𝑠𝑝 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ)) A)) ⟩
  tr Ty (remove++ 𝑧𝑣 δ) (∀⋆ (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) (δ ⊹ ⋆ ))
    (shiftTy (𝑠𝑝 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ)) A)) (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ)) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
    ≡⟨ tr∀⋆ (remove++ 𝑧𝑣 δ) (subsTy (tr Ty (insert++ (𝑠𝑝 𝑧𝑝) (δ ⊹ ⋆ ))
      (shiftTy (𝑠𝑝 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ)) A)) (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ)) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))) ⟩
  ∀⋆ (tr Ty (remove++ 𝑧𝑣 (δ ⊹ ⋆)) (subsTy (tr Ty  (insert++ (𝑠𝑝 𝑧𝑝) (δ ⊹ ⋆))
    (shiftTy (𝑠𝑝 (𝑠𝑝 𝑧𝑝 ++𝑃𝑜𝑠 δ)) A)) (𝑠𝑣 (𝑧𝑣 ++𝑉𝑎𝑟 δ)) (tr Ty (prefix++ 𝑧𝑣 δ ⁻¹) (𝑉 𝑧𝑣))))
    ≡⟨ ap ∀⋆ (η-helper (δ ⊹ ⋆) A) ⟩
  ∀⋆ A
    ∎

data RuleTm : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} (t s : Tm Γ A) → Type₀ where
  β₁ : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} (t : Tm (Γ ⊹ A) B) (s : Tm Γ A) →
    RuleTm (App (Lam t) s) (subsTm t 𝑧𝑣 s)
  β₂ : {γ : TyCtx} {Γ : Ctx γ} {⋆ : ⊤} {A : Ty γ}
    (t : Tm (shiftCtx {⋆ = ⋆} 𝑧𝑝 Γ) (shiftTy 𝑧𝑝 A)) (B : Ty γ) →
    RuleTm (APP (LAM t) B)
      (tr (λ Γ → Tm Γ (subsTy (shiftTy 𝑧𝑝 A) 𝑧𝑣 B)) (subsShiftCtx 𝑧𝑣 Γ B) (subsTm-γ t 𝑧𝑣 B))
  η₁ : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} (t : Tm Γ (A ⇒ B)) →
    RuleTm t (Lam (App (shiftTm 𝑧𝑝 t) (V 𝑧𝑣)))
  η₂ : {γ : TyCtx} {⋆ : ⊤} {Γ : Ctx γ} {A : Ty (γ ⊹ ⋆)} (t : Tm Γ (∀⋆ A)) →
    RuleTm t (tr (λ A → Tm Γ A) (ap ∀⋆ (η-helper ∅ A)) (LAM (APP (shiftTm-γ 𝑧𝑝 t) (𝑉 𝑧𝑣))))

data OTm : {γ : TyCtx} (Γ : Ctx γ) (A : Ty γ) → Type₀ where
 𝑂 : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} → OTm Γ A
 𝐿 : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} → OTm (Γ ⊹ A) B → OTm Γ (A ⇒ B)
 𝐴₁ : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
   OTm Γ (A ⇒ B) → Tm Γ A → OTm Γ B
 𝐴₂ : {γ : TyCtx} {Γ : Ctx γ} {A B : Ty γ} →
   Tm Γ (A ⇒ B) → OTm Γ A → OTm Γ B
 𝑇𝐿 : {γ : TyCtx} {Γ : Ctx γ} {⋆ : ⊤} {A : Ty (γ ⊹ ⋆)} →
   OTm (shiftCtx 𝑧𝑝 Γ) A → OTm Γ (∀⋆ A)
 𝑇𝐴 : {γ : TyCtx} {Γ : Ctx γ} {⋆ : ⊤} {A : Ty (γ ⊹ ⋆)} →
   OTm Γ (∀⋆ A) → (B : Ty γ) → OTm Γ (subsTy A 𝑧𝑣 B)

OTm-γ : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} → OTm Γ A → TyCtx
OTm-γ {γ} 𝑂 = γ
OTm-γ (𝐿 env) = OTm-γ env
OTm-γ (𝐴₁ env s) = OTm-γ env
OTm-γ (𝐴₂ t env) = OTm-γ env
OTm-γ (𝑇𝐿 env) = OTm-γ env
OTm-γ (𝑇𝐴 env B) = OTm-γ env

OTm-Γ : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} (env : OTm Γ A) → Ctx (OTm-γ env)
OTm-Γ {Γ = Γ} 𝑂 = Γ
OTm-Γ (𝐿 env) = OTm-Γ env
OTm-Γ (𝐴₁ env x) = OTm-Γ env
OTm-Γ (𝐴₂ x env) = OTm-Γ env
OTm-Γ (𝑇𝐿 env) = OTm-Γ env
OTm-Γ (𝑇𝐴 env B) = OTm-Γ env

OTm-A : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ} (env : OTm Γ A) → Ty (OTm-γ env)
OTm-A {A = A} 𝑂 = A
OTm-A (𝐿 env) = OTm-A env
OTm-A (𝐴₁ env x) = OTm-A env
OTm-A (𝐴₂ x env) = OTm-A env
OTm-A (𝑇𝐿 env) = OTm-A env
OTm-A (𝑇𝐴 env B) = OTm-A env

OTm-fill : {γ : TyCtx} {Γ : Ctx γ} {A : Ty γ}
  (env : OTm Γ A) → Tm (OTm-Γ env) (OTm-A env) → Tm Γ A
OTm-fill 𝑂 t = t
OTm-fill (𝐿 env) t = Lam (OTm-fill env t)
OTm-fill (𝐴₁ env s) t = App (OTm-fill env t) s
OTm-fill (𝐴₂ t env) s = App t (OTm-fill env s)
OTm-fill (𝑇𝐿 env) t = LAM (OTm-fill env t)
OTm-fill (𝑇𝐴 env B) t = APP (OTm-fill env t) B

-- Some tests

cℕ : {Γ : TyCtx} → Ty Γ
cℕ = ∀⋆ {⋆ = tt} ((𝑉 𝑧𝑣 ⇒ 𝑉 𝑧𝑣) ⇒ 𝑉 𝑧𝑣 ⇒ 𝑉 𝑧𝑣)

c⊥ : {Γ : TyCtx} → Ty Γ
c⊥ = ∀⋆ {⋆ = tt} (𝑉 𝑧𝑣)

test1 : Tm {∅} ∅ cℕ
test1 = LAM (Lam (Lam (App (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣))))

test2 = APP test1 c⊥
