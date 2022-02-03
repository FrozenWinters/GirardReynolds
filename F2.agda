module F2 where

open import lists

open import Data.Nat renaming (zero to Z; suc to S)

data Fin : ℕ → Type₀ where
  𝑍 : {n : ℕ} → Fin (S n)
  𝑆 : {n : ℕ} → Fin n → Fin (S n)

TyCtx = ℕ

TyVar : (n : TyCtx) → Type₀
TyVar n = Fin n

remove : (n : TyCtx) → TyVar n → TyCtx
remove (S n) 𝑍 = n
remove (S n) (𝑆 v) = S (remove n v)

TyCtxPos : (n : TyCtx) → Type₀
TyCtxPos n = Fin (S n)

shiftTyVar : {n : TyCtx} → TyVar n → TyCtxPos n → TyVar (S n)
shiftTyVar v 𝑍 = 𝑆 v
shiftTyVar 𝑍 (𝑆 𝑖) = 𝑍
shiftTyVar (𝑆 v) (𝑆 𝑖) = 𝑆 (shiftTyVar v 𝑖)

prefix : (n : TyCtx) → TyVar n → TyCtx
prefix (S n) 𝑍 = n
prefix (S n) (𝑆 v) = prefix n v

infixr 20 _⇒_
data Ty : TyCtx → Type₀ where
  𝑉 : {n : TyCtx} → TyVar n → Ty n
  _⇒_ : {n : TyCtx} → Ty n → Ty n → Ty n
  ∀⋆ : {n : TyCtx} → Ty (S n) → Ty n

shift : {n : TyCtx} → Ty n → TyCtxPos n → Ty (S n)
shift (𝑉 w) 𝑖 = 𝑉 (shiftTyVar w 𝑖)
shift (A ⇒ B) 𝑖 = shift A 𝑖 ⇒ shift B 𝑖
shift (∀⋆ A) 𝑖 = ∀⋆ (shift A (𝑆 𝑖))

subsVar : {n : TyCtx} → TyVar n → (v : TyVar n) → Ty (prefix n v) → Ty (remove n v)
subsVar 𝑍 𝑍 A = A
subsVar 𝑍 (𝑆 v) A = 𝑉 𝑍
subsVar (𝑆 w) 𝑍 A = 𝑉 w
subsVar (𝑆 w) (𝑆 v) A = shift (subsVar w v A) 𝑍

subs : {n : TyCtx} → Ty n → (v : TyVar n) → Ty (prefix n v) → Ty (remove n v)
subs (𝑉 w) v A = subsVar w v A
subs (B ⇒ C) v A = subs B v A ⇒ subs C v A
subs (∀⋆ B) v A = ∀⋆ (subs B (𝑆 v) A)

Ctx : TyCtx → Type₀
Ctx n = 𝐶𝑡𝑥 (Ty n)

Var : {n : TyCtx} → Ctx n → Ty n → Type₀
Var Γ = 𝑉𝑎𝑟 Γ

shiftTy : {n : TyCtx} (𝑖 : TyCtxPos n) (A : Ty n) → Ty (S n)
shiftTy 𝑖 A = shift A 𝑖

--shiftTy² : {n : TyCtx} (𝑖 : TyCtxPos n) (𝑗 : 

shiftCtx : {n : TyCtx} (𝑖 : TyCtxPos n) (Γ : Ctx n) → Ctx (S n)
shiftCtx 𝑖 = map𝐶𝑡𝑥 (shiftTy 𝑖)

shiftVar : {n : TyCtx} {Γ : Ctx n} {A : Ty n}
  (𝑖 : TyCtxPos n) (v : Var Γ A) → Var (shiftCtx 𝑖 Γ) (shiftTy 𝑖 A)
shiftVar 𝑖 v = tr𝑉𝑎𝑟 (shiftTy 𝑖) v

CtxPos : {n : TyCtx} → Ctx n → Type₀
CtxPos Γ = 𝑃𝑜𝑠 Γ

shiftCtxPos : {n : TyCtx} {Γ : Ctx n} (𝑗 : TyCtxPos n) (𝑖 : CtxPos Γ) → CtxPos (shiftCtx 𝑗 Γ)
shiftCtxPos 𝑗 𝑖 = tr𝑃𝑜𝑠 (shiftTy 𝑗) 𝑖

shiftInsert : {n : TyCtx} {Γ : Ctx n} {A : Ty n} (𝑗 : TyCtxPos n) (𝑖 : CtxPos Γ) →
  insert𝐶𝑡𝑥 (shiftCtxPos 𝑗 𝑖) (shift A 𝑗) ≡ shiftCtx 𝑗 (insert𝐶𝑡𝑥 𝑖 A)
shiftInsert 𝑗 𝑧𝑝 = refl
shiftInsert {Γ = Γ ⊹ A} 𝑗 (𝑠𝑝 𝑖) = ap (_⊹  shift A 𝑗) (shiftInsert 𝑗 𝑖)

data Tm : {n : TyCtx} → Ctx n → Ty n → Type₀ where
  V : {n : TyCtx} {Γ : Ctx n} {A : Ty n} → Var Γ A → Tm Γ A
  Lam : {n : TyCtx} {Γ : Ctx n} {A B : Ty n} → Tm (Γ ⊹ A) B → Tm Γ (A ⇒ B)
  App : {n : TyCtx} {Γ : Ctx n} {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  LAM : {n : TyCtx} {Γ : Ctx n} {A : Ty (S n)} → Tm (shiftCtx 𝑍 Γ) A → Tm Γ (∀⋆ A)
  APP : {n : TyCtx} {Γ : Ctx n} {A : Ty (S n)} → Tm Γ (∀⋆ A) → (B : Ty n) → Tm Γ (subs A 𝑍 B)

shiftTm : {n : TyCtx} {Γ : Ctx n} {A B : Ty n} (𝑖 : CtxPos Γ) → Tm Γ B → Tm (insert𝐶𝑡𝑥 𝑖 A) B
shiftTm 𝑖 (V v) = V (shift𝑉𝑎𝑟 𝑖 v)
shiftTm 𝑖 (Lam t) = Lam (shiftTm (𝑠𝑝 𝑖) t)
shiftTm 𝑖 (App t s) = App (shiftTm 𝑖 t) (shiftTm 𝑖 s)
shiftTm {B = ∀⋆ A} 𝑖 (LAM t) =
  LAM (tr (λ Δ → Tm Δ A) (shiftInsert 𝑍 𝑖) (shiftTm (shiftCtxPos 𝑍 𝑖) t))
shiftTm 𝑖 (APP t A) = APP (shiftTm 𝑖 t) A

shiftTm-n : {n : TyCtx} {Γ : Ctx n} {A : Ty n}
  (𝑖 : TyCtxPos n) → Tm Γ A → Tm (shiftCtx 𝑖 Γ) (shiftTy 𝑖 A)
shiftTm-n 𝑖 (V v) = V (shiftVar 𝑖 v)
shiftTm-n 𝑖 (Lam t) = Lam (shiftTm-n 𝑖 t)
shiftTm-n 𝑖 (App t s) = App (shiftTm-n 𝑖 t) (shiftTm-n 𝑖 s)
shiftTm-n 𝑖 (LAM t) = LAM {!shiftTm-n (𝑆 𝑖) t!}
shiftTm-n 𝑖 (APP t A) = {!!}

-- Some tests

cℕ : {Γ : TyCtx} → Ty Γ
cℕ = ∀⋆ ((𝑉 𝑍 ⇒ 𝑉 𝑍) ⇒ 𝑉 𝑍 ⇒ 𝑉 𝑍)

c⊥ : {Γ : TyCtx} → Ty Γ
c⊥ = ∀⋆ (𝑉 𝑍)

test1 : Tm {0} ∅ cℕ
test1 = LAM (Lam (Lam (App (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣))))

test2 = APP test1 c⊥
