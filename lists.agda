module lists where

{-open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public-}

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Relation.Binary.PropositionalEquality
  renaming (cong to ap ; sym to _⁻¹ ; trans to _∙_ ; subst to tr) hiding ([_]) public
open ≡-Reasoning public
open import Function public

Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ

Type₀ : Type (lsuc lzero)
Type₀ = Type lzero

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

infixl 20 _⊹_
data 𝐶𝑡𝑥 (ty : Type ℓ) : Type ℓ where
  ∅ : 𝐶𝑡𝑥 ty
  _⊹_ : 𝐶𝑡𝑥 ty → ty → 𝐶𝑡𝑥 ty

map𝐶𝑡𝑥 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) (Γ : 𝐶𝑡𝑥 ty₁) → 𝐶𝑡𝑥 ty₂
map𝐶𝑡𝑥 f ∅ = ∅
map𝐶𝑡𝑥 f (Γ ⊹ A) = map𝐶𝑡𝑥 f Γ ⊹ f A

data 𝑉𝑎𝑟 {ty : Type ℓ} : (Γ : 𝐶𝑡𝑥 ty) (A : ty) → Type ℓ where
  𝑧𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 (Γ ⊹ A) A
  𝑠𝑣 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} → 𝑉𝑎𝑟 Γ A → 𝑉𝑎𝑟 (Γ ⊹ B) A

prefix𝑉𝑎𝑟 : {ty : Type ℓ} {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 Γ A → 𝐶𝑡𝑥 ty
prefix𝑉𝑎𝑟 {Γ = Γ ⊹ A} 𝑧𝑣 = Γ
prefix𝑉𝑎𝑟 (𝑠𝑣 v) = prefix𝑉𝑎𝑟 v

remove𝑉𝑎𝑟 : {ty : Type ℓ} {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑉𝑎𝑟 Γ A → 𝐶𝑡𝑥 ty
remove𝑉𝑎𝑟 {Γ = Γ ⊹ A} 𝑧𝑣 = Γ
remove𝑉𝑎𝑟 {Γ = Γ ⊹ A} (𝑠𝑣 v) = remove𝑉𝑎𝑟 v ⊹ A

tr𝑉𝑎𝑟 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ : 𝐶𝑡𝑥 ty₁} {A : ty₁}
  → 𝑉𝑎𝑟 Γ A → 𝑉𝑎𝑟 (map𝐶𝑡𝑥 f Γ) (f A)
tr𝑉𝑎𝑟 f 𝑧𝑣 = 𝑧𝑣
tr𝑉𝑎𝑟 f (𝑠𝑣 v) = 𝑠𝑣 (tr𝑉𝑎𝑟 f v)

data 𝑃𝑜𝑠 {ty : Type ℓ} : (Γ : 𝐶𝑡𝑥 ty) → Type ℓ where
  𝑧𝑝 : {Γ : 𝐶𝑡𝑥 ty} → 𝑃𝑜𝑠 Γ
  𝑠𝑝 : {Γ : 𝐶𝑡𝑥 ty} {A : ty} → 𝑃𝑜𝑠 Γ → 𝑃𝑜𝑠 (Γ ⊹ A)

module _ {ty : Type ℓ} where
  prefix𝑃𝑜𝑠 : {Γ : 𝐶𝑡𝑥 ty} (𝑖 : 𝑃𝑜𝑠 Γ) → 𝐶𝑡𝑥 ty
  prefix𝑃𝑜𝑠 {Γ = Γ} 𝑧𝑝 = Γ
  prefix𝑃𝑜𝑠 (𝑠𝑝 𝑖) = prefix𝑃𝑜𝑠 𝑖

  _+_ : {Γ : 𝐶𝑡𝑥 ty} (𝑖 : 𝑃𝑜𝑠 Γ) → 𝑃𝑜𝑠 (prefix𝑃𝑜𝑠 𝑖) → 𝑃𝑜𝑠 Γ
  𝑧𝑝 + 𝑗 = 𝑗
  𝑠𝑝 𝑖 + 𝑗 = 𝑠𝑝 (𝑖 + 𝑗)

  insert𝐶𝑡𝑥 : {Γ : 𝐶𝑡𝑥 ty} → 𝑃𝑜𝑠 Γ → ty → 𝐶𝑡𝑥 ty
  insert𝐶𝑡𝑥 {Γ = Γ} 𝑧𝑝 A = Γ ⊹ A
  insert𝐶𝑡𝑥 {Γ = Γ ⊹ B} (𝑠𝑝 p) A = insert𝐶𝑡𝑥 p A ⊹ B

  shift𝑉𝑎𝑟 : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} (𝑖 : 𝑃𝑜𝑠 Γ) (v : 𝑉𝑎𝑟 Γ B) → 𝑉𝑎𝑟 (insert𝐶𝑡𝑥 𝑖 A) B
  shift𝑉𝑎𝑟 𝑧𝑝 v = 𝑠𝑣 v
  shift𝑉𝑎𝑟 (𝑠𝑝 𝑖) 𝑧𝑣 = 𝑧𝑣
  shift𝑉𝑎𝑟 (𝑠𝑝 𝑖) (𝑠𝑣 v) = 𝑠𝑣 (shift𝑉𝑎𝑟 𝑖 v)

  -- If 𝑖 ≡ 𝑗, then this will point to the right of A
  shift𝑃𝑜𝑠₁ : {Γ : 𝐶𝑡𝑥 ty} (𝑗 𝑖 : 𝑃𝑜𝑠 Γ) (A : ty) → 𝑃𝑜𝑠 (insert𝐶𝑡𝑥 𝑗 A)
  shift𝑃𝑜𝑠₁ 𝑗 𝑧𝑝 A = 𝑧𝑝
  shift𝑃𝑜𝑠₁ {Γ ⊹ B} 𝑧𝑝 (𝑠𝑝 𝑖) A = 𝑠𝑝 (shift𝑃𝑜𝑠₁ 𝑧𝑝 𝑖 B)
  shift𝑃𝑜𝑠₁ (𝑠𝑝 𝑗) (𝑠𝑝 𝑖) A = 𝑠𝑝 (shift𝑃𝑜𝑠₁ 𝑗 𝑖 A)

  -- If 𝑖 ≡ 𝑗, then this will point to the left of A
  shift𝑃𝑜𝑠₂ : {Γ : 𝐶𝑡𝑥 ty} (𝑗 𝑖 : 𝑃𝑜𝑠 Γ) (A : ty) → 𝑃𝑜𝑠 (insert𝐶𝑡𝑥 𝑗 A)
  shift𝑃𝑜𝑠₂ 𝑧𝑝 𝑖 A = 𝑠𝑝 𝑖
  shift𝑃𝑜𝑠₂ (𝑠𝑝 𝑗) 𝑧𝑝 A = 𝑧𝑝
  shift𝑃𝑜𝑠₂ (𝑠𝑝 𝑗) (𝑠𝑝 𝑖) A = 𝑠𝑝 (shift𝑃𝑜𝑠₂ 𝑗 𝑖 A)

  insert𝐶𝑡𝑥² : {Γ : 𝐶𝑡𝑥 ty} {A B : ty} (𝑖 : 𝑃𝑜𝑠 Γ) (𝑗 : 𝑃𝑜𝑠 (prefix𝑃𝑜𝑠 𝑖)) →
    insert𝐶𝑡𝑥 (shift𝑃𝑜𝑠₂ 𝑖 (𝑖 + 𝑗) A) B ≡ insert𝐶𝑡𝑥 (shift𝑃𝑜𝑠₁ (𝑖 + 𝑗) 𝑖 B) A
  insert𝐶𝑡𝑥² 𝑧𝑝 𝑗 = refl
  insert𝐶𝑡𝑥² {Γ ⊹ A} {B} {C} (𝑠𝑝 𝑖) 𝑗 = ap (_⊹ A) (insert𝐶𝑡𝑥² {Γ} {B} {C} 𝑖 𝑗)

tr𝑃𝑜𝑠 : {ty₁ : Type ℓ₁} {ty₂ : Type ℓ₂} (f : ty₁ → ty₂) {Γ : 𝐶𝑡𝑥 ty₁}
  → 𝑃𝑜𝑠 Γ → 𝑃𝑜𝑠 (map𝐶𝑡𝑥 f Γ)
tr𝑃𝑜𝑠 f 𝑧𝑝 = 𝑧𝑝
tr𝑃𝑜𝑠 f (𝑠𝑝 p) = 𝑠𝑝 (tr𝑃𝑜𝑠 f p)

{-shiftPos : {ty : Type ℓ} {Γ : 𝐶𝑡𝑥 ty} {A : ty} (𝑖 𝑗 : 𝑃𝑜𝑠 Γ) → 𝑃𝑜𝑠 (insertCtx Γ A 𝑖)
shiftPos 𝑖 𝑍 = 𝑍
shiftPos 𝑍 (𝑆 𝑗) = 𝑆 (shiftPos 𝑍 𝑗)
shiftPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (shiftPos 𝑖 𝑗)

incPos : {Γ : Ctx} {A : Ty} (𝑖 𝑗 : CtxPos Γ) → CtxPos (insertCtx Γ A 𝑖)
incPos 𝑍 𝑗 = 𝑆 𝑗
incPos (𝑆 𝑖) 𝑍 = 𝑆 𝑍
incPos (𝑆 𝑖) (𝑆 𝑗) = 𝑆 (incPos 𝑖 𝑗)-}
