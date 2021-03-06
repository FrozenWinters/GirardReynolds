module F2 where

open import lists

--open import Data.Nat renaming (zero to Z; suc to S)

data β€ : Typeβ where
  tt : β€

-- Round I

TyCtx = πΆπ‘π₯ β€
TyVar = πππ {ty = β€}
TyPos = πππ  {ty = β€}

infixr 20 _β_
data Ty : TyCtx β Typeβ where
  π : {Ξ³ : TyCtx} {β : β€} β TyVar Ξ³ β β Ty Ξ³
  _β_ : {Ξ³ : TyCtx} β Ty Ξ³ β Ty Ξ³ β Ty Ξ³
  ββ : {Ξ³ : TyCtx} {β : β€} β Ty (Ξ³ βΉ β) β Ty Ξ³

shiftTy : {Ξ³ : TyCtx} {β : β€} (π : TyPos Ξ³) β Ty Ξ³ β Ty (insertπΆπ‘π₯ π β)
shiftTy π (π v) = π (shiftπππ π v)
shiftTy π (A β B) = shiftTy π A β shiftTy π B
shiftTy π (ββ A) = ββ (shiftTy (π π π) A)

subsTyVar : {Ξ³ : TyCtx} {ββ ββ : β€} β
  TyVar Ξ³ ββ β (v : TyVar Ξ³ ββ) β Ty (prefixπππ v) β Ty (removeπππ v)
subsTyVar = subsπππ π shiftTy

subsTy : {Ξ³ : TyCtx} {β : β€} β Ty Ξ³ β (v : TyVar Ξ³ β) β Ty (prefixπππ v) β Ty (removeπππ v)
subsTy (π w) v A = subsTyVar w v A
subsTy (B β C) v A = subsTy B v A β subsTy C v A
subsTy (ββ B) v A = ββ (subsTy B (π π£ v) A)

-- Round II

Ctx : TyCtx β Typeβ
Ctx Ξ³ = πΆπ‘π₯ (Ty Ξ³)

Var : {Ξ³ : TyCtx} β Ctx Ξ³ β Ty Ξ³ β Typeβ
Var {Ξ³} = πππ {ty = Ty Ξ³}

CtxPos : {Ξ³ : TyCtx} β Ctx Ξ³ β Typeβ
CtxPos {Ξ³} = πππ  {ty = Ty Ξ³}

shiftCtx : {Ξ³ : TyCtx} {β : β€} (π : TyPos Ξ³) (Ξ : Ctx Ξ³) β Ctx (insertπΆπ‘π₯ π β)
shiftCtx π = mapπΆπ‘π₯ (shiftTy π)

subsCtx : {Ξ³ : TyCtx} {β : β€} β Ctx Ξ³ β (v : TyVar Ξ³ β) β Ty (prefixπππ v) β Ctx (removeπππ v)
subsCtx Ξ π A = mapπΆπ‘π₯ (Ξ» B β subsTy B π A) Ξ 

trπ : {Ξ³ Ξ΄ : TyCtx} {β : β€} (p : Ξ³ β‘ Ξ΄) (v : TyVar Ξ³ β) β
  tr Ty p (π v) β‘ π (tr (Ξ» Ξ³ β TyVar Ξ³ β) p v)
trπ refl v = refl

trβ : {Ξ³ Ξ΄ : TyCtx} (p : Ξ³ β‘ Ξ΄) (A B : Ty Ξ³) β
  tr Ty p (A β B) β‘ tr Ty p A β tr Ty p B
trβ refl A B = refl

trββ : {Ξ³ Ξ΄ : TyCtx} {β : β€} (p : Ξ³ β‘ Ξ΄) (A : Ty (Ξ³ βΉ β)) β
  tr Ty p (ββ A) β‘ ββ (tr Ty (ap (_βΉ β) p) A)
trββ refl A = refl

shiftTyΒ² : {Ξ³ : TyCtx} {ββ ββ : β€} (π : TyPos Ξ³) (π : TyPos (prefixπππ  π)) (A : Ty Ξ³) β
  tr (Ξ» Ξ³ β Ty Ξ³) (insertπΆπ‘π₯Β² π π)
    (shiftTy {β = ββ} (shiftπππ β π (π + π)) (shiftTy π A))
  β‘ shiftTy {β = ββ} (shiftπππ β (π + π) π) (shiftTy (π + π) A)
shiftTyΒ² π π (π {β = β} v) =
  tr Ty (insertπΆπ‘π₯Β² π π) (π (shiftπππ (shiftπππ β π (π + π)) (shiftπππ π v)))
    β‘β¨ trπ  (insertπΆπ‘π₯Β² π π) (shiftπππ (shiftπππ β π (π + π)) (shiftπππ π v)) β©
  π (tr (Ξ» Ξ³ β TyVar Ξ³ β) (insertπΆπ‘π₯Β² π π) (shiftπππ (shiftπππ β π (π + π)) (shiftπππ π v)))
    β‘β¨ ap π (shiftπππΒ² π π v) β©
  π (shiftπππ (shiftπππ β (π + π) π) (shiftπππ (π + π) v))
    β
shiftTyΒ² π π (A β B) =
  tr Ty (insertπΆπ‘π₯Β² π π)
    (shiftTy (shiftπππ β π (π + π)) (shiftTy π A) β shiftTy (shiftπππ β π (π + π)) (shiftTy π B))
    β‘β¨ trβ (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))
      (shiftTy (shiftπππ β π (π + π)) (shiftTy π B)) β©
  tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))
    β tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π B))
    β‘β¨ ap (tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A)) β_) (shiftTyΒ² π π B) β©
  tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))
    β shiftTy (shiftπππ β (π + π) π) (shiftTy (π + π) B)
    β‘β¨ ap (_β shiftTy (shiftπππ β (π + π) π) (shiftTy (π + π) B)) (shiftTyΒ² π π A) β©
  shiftTy (shiftπππ β (π + π) π) (shiftTy (π + π) A) β shiftTy (shiftπππ β (π + π) π) (shiftTy (π + π) B)
    β
shiftTyΒ² π π (ββ {β = β} A) =
  tr Ty (insertπΆπ‘π₯Β² π π) (ββ (shiftTy (π π (shiftπππ β π (π + π))) (shiftTy (π π π) A)))
    β‘β¨ trββ (insertπΆπ‘π₯Β² π π) (shiftTy (π π (shiftπππ β π (π + π))) (shiftTy (π π π) A)) β©
  ββ (tr Ty (ap (_βΉ β) (insertπΆπ‘π₯Β² π π)) (shiftTy (π π (shiftπππ β π (π + π))) (shiftTy (π π π) A)))
    β‘β¨ ap ββ (shiftTyΒ² (π π π) π A) β©
  ββ (shiftTy (π π (shiftπππ β (π + π) π)) (shiftTy (π π (π + π)) A))
    β

trβ : {Ξ³ Ξ΄ : TyCtx} (p : Ξ³ β‘ Ξ΄) β tr (πΆπ‘π₯ β Ty) p β β‘ β
trβ refl = refl

trβΉ : {Ξ³ Ξ΄ : TyCtx} (p : Ξ³ β‘ Ξ΄) (Ξ : Ctx Ξ³) (A : Ty Ξ³) β
  tr (πΆπ‘π₯ β Ty) p (Ξ βΉ A) β‘ tr (πΆπ‘π₯ β Ty) p Ξ βΉ tr Ty p A
trβΉ refl Ξ A = refl

shiftCtxΒ² : {Ξ³ : TyCtx} {ββ ββ : β€} (π : TyPos Ξ³) (π : TyPos (prefixπππ  π)) (Ξ : Ctx Ξ³) β
  tr (Ξ» Ξ³ β Ctx Ξ³) (insertπΆπ‘π₯Β² π π)
    (shiftCtx {β = ββ} (shiftπππ β π (π + π)) (shiftCtx π Ξ))
  β‘ shiftCtx {β = ββ} (shiftπππ β (π + π) π) (shiftCtx (π + π) Ξ)
shiftCtxΒ² π π β = trβ (insertπΆπ‘π₯Β² π π)
shiftCtxΒ² π π (Ξ βΉ A) =
  tr Ctx (insertπΆπ‘π₯Β² π π) (shiftCtx (shiftπππ β π (π + π)) (shiftCtx π (Ξ βΉ A)))
    β‘β¨ trβΉ (insertπΆπ‘π₯Β² π π) (mapπΆπ‘π₯ (shiftTy (shiftπππ β π (π + π))) (mapπΆπ‘π₯ (shiftTy π) Ξ))
      (shiftTy (shiftπππ β π (π + π)) (shiftTy π A)) β©
  tr (πΆπ‘π₯ β Ty) (insertπΆπ‘π₯Β² π π) (mapπΆπ‘π₯ (shiftTy (shiftπππ β π (π + π))) (mapπΆπ‘π₯ (shiftTy π) Ξ))
    βΉ tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))
    β‘β¨ ap (_βΉ tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))) (shiftCtxΒ² π π Ξ) β©
  shiftCtx (shiftπππ β (π + π) π) (shiftCtx (π + π) Ξ)
    βΉ tr Ty (insertπΆπ‘π₯Β² π π) (shiftTy (shiftπππ β π (π + π)) (shiftTy π A))
    β‘β¨ ap (shiftCtx (shiftπππ β (π + π) π) (shiftCtx (π + π) Ξ) βΉ_) (shiftTyΒ² π π A) β©
  shiftCtx (shiftπππ β (π + π) π) (shiftCtx (π + π) Ξ)
    βΉ shiftTy (shiftπππ β (π + π) π) (shiftTy (π + π) A)
    β

shiftPrefixTy : {Ξ³ : TyCtx} {ββ ββ : β€} (v : TyVar Ξ³ ββ) (π : TyPos Ξ³) β
  Ty (prefixπππ v) β Ty (prefixπππ (shiftπππ π v {ββ}))
shiftPrefixTy v π§π A = A
shiftPrefixTy π§π£ (π π π) A = shiftTy π A
shiftPrefixTy (π π£ v) (π π π) A = shiftPrefixTy v π A

trShiftTy : {Ξ³ Ξ΄ : TyCtx} {β : β€} (p : Ξ³ β‘ Ξ΄) (A : Ty Ξ³) β
  tr Ty (ap (_βΉ β) p) (shiftTy π§π A) β‘ shiftTy π§π (tr Ty p A)
trShiftTy refl A = refl

trππ§π£ : {Ξ³ Ξ΄ : TyCtx} {β : β€} (p : Ξ³ β‘ Ξ΄) β
  tr Ty (ap (_βΉ β) p) (π π§π£) β‘ π π§π£
trππ§π£ refl = refl

trππ π£ : {Ξ³ Ξ΄ : TyCtx} {ββ ββ : β€} (p : Ξ³ β‘ Ξ΄) (v : TyVar Ξ³ ββ) β
  tr Ty (ap (_βΉ ββ) p) (π (π π£ v)) β‘ π (π π£ (tr (Ξ» Ξ³ β TyVar Ξ³ ββ) p v))
trππ π£ refl v = refl

shiftSubsTyVar : {Ξ³ : TyCtx} {ββ ββ ββ : β€} (v : TyVar Ξ³ ββ) (π : TyPos Ξ³) (w : TyVar Ξ³ ββ)
  (B : Ty (prefixπππ v)) β
  tr (Ξ» Ξ΄ β Ty Ξ΄) (insert-remove v π) (subsTy (shiftTy π (π w)) (shiftπππ π v) (shiftPrefixTy v π B))
    β‘ shiftTy {β = ββ} (removedπππ  v π) (subsTy (π w) v B)
shiftSubsTyVar v π§π w B = refl
shiftSubsTyVar π§π£ (π π π) π§π£ B = refl
shiftSubsTyVar (π π£ v) (π π π) π§π£ B = trππ§π£ (insert-remove v π)
shiftSubsTyVar π§π£ (π π π) (π π£ w) B = refl
shiftSubsTyVar {Ξ³ = Ξ³ βΉ β} (π π£ v) (π π π) (π π£ w) B =
  tr Ty (ap (_βΉ β) (insert-remove v π))
    (shiftTy π§π (subsTyVar (shiftπππ π w) (shiftπππ π v) (shiftPrefixTy v π B)))
    β‘β¨ trShiftTy (insert-remove v π)
      (subsTyVar (shiftπππ π w) (shiftπππ π v) (shiftPrefixTy v π B)) β©
  shiftTy π§π
    (tr Ty (insert-remove v π) (subsTyVar (shiftπππ π w) (shiftπππ π v) (shiftPrefixTy v π B)))
    β‘β¨ ap (shiftTy π§π) (shiftSubsTyVar v π w B) β©
  shiftTy π§π (shiftTy (removedπππ  v π) (subsTyVar w v B))
    β‘β¨ (shiftTyΒ² π§π (removedπππ  v π) (subsTyVar w v B) β»ΒΉ) β©
  shiftTy (π π (removedπππ  v π)) (shiftTy π§π (subsTyVar w v B))
    β

shiftSubsTy : {Ξ³ : TyCtx} {ββ ββ : β€} (v : TyVar Ξ³ ββ) (π : TyPos Ξ³) (A : Ty Ξ³)
  (B : Ty (prefixπππ v)) β
  tr (Ξ» Ξ΄ β Ty Ξ΄) (insert-remove v π) (subsTy (shiftTy π A) (shiftπππ π v) (shiftPrefixTy v π B))
    β‘ shiftTy {β = ββ} (removedπππ  v π) (subsTy A v B)
shiftSubsTy v π (π w) A = shiftSubsTyVar v π w A
shiftSubsTy v π (B β C) A =
  tr Ty (insert-remove v π) (subsTy (shiftTy π B) (shiftπππ π v) (shiftPrefixTy v π A)
    β subsTy (shiftTy π C) (shiftπππ π v) (shiftPrefixTy v π A))
    β‘β¨ trβ (insert-remove v π) (subsTy (shiftTy π B) (shiftπππ π v) (shiftPrefixTy v π A))
      (subsTy (shiftTy π C) (shiftπππ π v) (shiftPrefixTy v π A)) β©
  tr Ty (insert-remove v π) (subsTy (shiftTy π B) (shiftπππ π v) (shiftPrefixTy v π A))
    β tr Ty (insert-remove v π) (subsTy (shiftTy π C) (shiftπππ π v) (shiftPrefixTy v π A))
    β‘β¨ ap (tr Ty (insert-remove v π) (subsTy (shiftTy π B) (shiftπππ π v) (shiftPrefixTy v π A)) β_)
      (shiftSubsTy v π C A) β©
  tr Ty (insert-remove v π) (subsTy (shiftTy π B) (shiftπππ π v) (shiftPrefixTy v π A))
    β shiftTy (removedπππ  v π) (subsTy C v A)
    β‘β¨ ap (_β shiftTy (removedπππ  v π) (subsTy C v A)) (shiftSubsTy v π B A) β©
  shiftTy (removedπππ  v π) (subsTy B v A) β shiftTy (removedπππ  v π) (subsTy C v A)
    β
shiftSubsTy v π (ββ {β = β} B) A =
  tr Ty (insert-remove v π)
    (ββ (subsTy (shiftTy (π π π) B) (π π£ (shiftπππ π v)) (shiftPrefixTy v π A)))
    β‘β¨ trββ (insert-remove v π)
      (subsTy (shiftTy (π π π) B) (π π£ (shiftπππ π v)) (shiftPrefixTy v π A)) β©
  ββ (tr Ty (insert-remove (π π£ v) (π π π))
       (subsTy (shiftTy (π π π) B) (shiftπππ (π π π) (π π£ v)) (shiftPrefixTy (π π£ {B = β} v) (π π π) A)))
    β‘β¨ ap ββ (shiftSubsTy (π π£ v) (π π π) B A) β©
  ββ (shiftTy (π π (removedπππ  v π)) (subsTy B (π π£ v) A))
    β

shiftSubsCtx : {Ξ³ : TyCtx} {ββ ββ : β€} (v : TyVar Ξ³ ββ) (π : TyPos Ξ³) (Ξ : Ctx Ξ³)
  (B : Ty (prefixπππ v)) β
  tr (Ξ» Ξ΄ β Ctx Ξ΄) (insert-remove v π) (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B))
    β‘ shiftCtx {β = ββ} (removedπππ  v π) (subsCtx Ξ v B)
shiftSubsCtx v π β B = trβ (insert-remove v π)
shiftSubsCtx v π (Ξ βΉ A) B =
  tr Ctx (insert-remove v π)
    (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B)
      βΉ subsTy (shiftTy π A) (shiftπππ π v) (shiftPrefixTy v π B))
    β‘β¨ trβΉ (insert-remove v π) (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B))
      (subsTy (shiftTy π A) (shiftπππ π v) (shiftPrefixTy v π B)) β©
  tr Ctx (insert-remove v π) (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B))
    βΉ tr Ty (insert-remove v π) (subsTy (shiftTy π A) (shiftπππ π v) (shiftPrefixTy v π B))
    β‘β¨ ap (tr Ctx (insert-remove v π) (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B))
      βΉ_) (shiftSubsTy v π A B) β©
  tr Ctx (insert-remove v π) (subsCtx (shiftCtx π Ξ) (shiftπππ π v) (shiftPrefixTy v π B))
    βΉ shiftTy (removedπππ  v π) (subsTy A v B)
    β‘β¨ ap (_βΉ shiftTy (removedπππ  v π) (subsTy A v B)) (shiftSubsCtx v π Ξ B) β©
  shiftCtx (removedπππ  v π) (subsCtx (Ξ βΉ A) v B)
    β

removePrefixTy : {Ξ³ : TyCtx} {ββ ββ : β€} (v : TyVar Ξ³ ββ) (w : TyVar (removeπππ v) ββ) β
  Ty (prefixπππ v) β Ty (prefixπππ w) β Ty (prefixπππ (swapRemoveπππ v w))
removePrefixTy π§π£ w A B = subsTy A w B
removePrefixTy (π π£ v) π§π£ A B = A
removePrefixTy (π π£ v) (π π£ w) A B = removePrefixTy v w A B

reinsertPrefixTy : {Ξ³ : TyCtx} {ββ ββ : β€} (v : TyVar Ξ³ ββ) (w : TyVar (removeπππ v) ββ) β
  Ty (prefixπππ v) β Ty (prefixπππ w) β Ty (prefixπππ (reinsertπππ v w))
reinsertPrefixTy π§π£ w A B = B
reinsertPrefixTy (π π£ v) π§π£ A B = tr Ty (insert-removal v) (shiftTy (removalπππ  v) B)
reinsertPrefixTy (π π£ v) (π π£ w) A B = reinsertPrefixTy v w A B

subsShiftVar : {Ξ³ : TyCtx} {ββ ββ : β€}
  (v : TyVar Ξ³ ββ) (w : TyVar (removeπππ v) ββ) (B : Ty (prefixπππ v)) β
  subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) (π w))) v B β‘ π w
subsShiftVar π§π£ w B = refl
subsShiftVar (π π£ v) π§π£ B = ap (Ξ» x β subsTy x (π π£ v) B) (trππ§π£ (insert-removal v))
subsShiftVar {Ξ³ = Ξ³ βΉ β} {ββ = ββ} (π π£ v) (π π£ w) B =
  subsTy (tr Ty (ap (_βΉ β) (insert-removal v)) (π (π π£ (shiftπππ (removalπππ  v) w)))) (π π£ v) B
    β‘β¨ ap (Ξ» x β subsTy x (π π£ v) B) (trππ π£ (insert-removal v) (shiftπππ (removalπππ  v) w)) β©
  shiftTy π§π (subsTy (π (tr (Ξ» Ξ³β β πππ Ξ³β ββ) (insert-removal v) (shiftπππ (removalπππ  v) w))) v B)
    β‘β¨ ap (Ξ» x β shiftTy π§π (subsTy x v B))
      (trπ (insert-removal v) (shiftπππ (removalπππ  v) w) β»ΒΉ) β©
  shiftTy π§π (subsTy (tr Ty (insert-removal v) (π (shiftπππ (removalπππ  v) w))) v B)
    β‘β¨ ap (shiftTy π§π) (subsShiftVar v w B) β©
  π (π π£ w)
    β

subsShiftTy : {Ξ³ : TyCtx} {β : β€} (v : TyVar Ξ³ β) (A : Ty (removeπππ v)) (B : Ty (prefixπππ v)) β
  subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) A)) v B β‘ A
subsShiftTy v (π w) B = subsShiftVar v w B
subsShiftTy v (Aβ β Aβ) B =
  subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) Aβ β shiftTy (removalπππ  v) Aβ)) v B
    β‘β¨ ap (Ξ» x β subsTy x v B)
      (trβ (insert-removal v) (shiftTy (removalπππ  v) Aβ) (shiftTy (removalπππ  v) Aβ)) β©
  subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) Aβ)) v B
    β subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) Aβ)) v B
    β‘β¨ ap (subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) Aβ)) v B β_)
      (subsShiftTy v Aβ B) β©
  subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) Aβ)) v B β Aβ
    β‘β¨ ap (_β Aβ) (subsShiftTy v Aβ B) β©
  Aβ β Aβ
    β
subsShiftTy v (ββ {β = β} A) B =
  subsTy (tr Ty (insert-removal v) (ββ (shiftTy (π π (removalπππ  v)) A))) v B
    β‘β¨ ap (Ξ» x β subsTy x v B) (trββ (insert-removal v) (shiftTy (π π (removalπππ  v)) A)) β©
  ββ (subsTy (tr Ty (ap (_βΉ β) (insert-removal v)) (shiftTy (π π (removalπππ  v)) A)) (π π£ v) B)
    β‘β¨ ap ββ (subsShiftTy (π π£ v) A B) β©
  ββ A
    β

subsShiftCtx : {Ξ³ : TyCtx} {β : β€} (v : TyVar Ξ³ β) (Ξ : Ctx (removeπππ v)) (A : Ty (prefixπππ v)) β
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removalπππ  v) Ξ)) v A β‘ Ξ
subsShiftCtx v β A = ap (Ξ» x β subsCtx x v A) (trβ (insert-removal v))
subsShiftCtx v (Ξ βΉ B) A =
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removalπππ  v) (Ξ βΉ B))) v A
    β‘β¨ ap (Ξ» x β subsCtx x v A) (trβΉ (insert-removal v) (shiftCtx (removalπππ  v) Ξ)
      (shiftTy (removalπππ  v) B)) β©
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removalπππ  v) Ξ)) v A
    βΉ subsTy (tr Ty (insert-removal v) (shiftTy (removalπππ  v) B)) v A
    β‘β¨ ap (subsCtx (tr Ctx (insert-removal v) (shiftCtx (removalπππ  v) Ξ)) v A βΉ_)
      (subsShiftTy v B A) β©
  subsCtx (tr Ctx (insert-removal v) (shiftCtx (removalπππ  v) Ξ)) v A βΉ B
    β‘β¨ ap (_βΉ B) (subsShiftCtx v Ξ A) β©
  Ξ βΉ B
    β

subsVarΒ² : {Ξ³ : TyCtx} {β ββ ββ : β€} (u : TyVar Ξ³ β) (v : TyVar Ξ³ ββ)
  (w : TyVar (removeπππ v) ββ) (B : Ty (prefixπππ v)) (C : Ty (prefixπππ w)) β
  tr Ty (remove-swap v w) (subsTy (subsTy (π u) (reinsertπππ v w) (reinsertPrefixTy v w B C))
    (swapRemoveπππ v w) (removePrefixTy v w B C))
    β‘ subsTy (subsTy (π u) v B) w C
subsVarΒ² π§π£ π§π£ w B C = refl
subsVarΒ² (π π£ u) π§π£ w B C = subsShiftTy π§π£ (subsTyVar u w C) (subsTy B w C)
subsVarΒ² π§π£ (π π£ v) π§π£ B C = subsShiftTy v C B
subsVarΒ² π§π£ (π π£ v) (π π£ w) B C = trππ§π£ (remove-swap v w)
subsVarΒ² (π π£ u) (π π£ v) π§π£ B C = subsShiftTy π§π£ (subsTyVar u v B) C β»ΒΉ
subsVarΒ² {Ξ³ = Ξ³ βΉ β} (π π£ u) (π π£ v) (π π£ w) B C =
  tr Ty (ap (_βΉ β) (remove-swap v w)) (subsTy (shiftTy π§π (subsπππ π shiftTy u (reinsertπππ v w)
    (reinsertPrefixTy v w B C))) (π π£ (swapRemoveπππ v w)) (removePrefixTy v w B C))
    β‘β¨ ap (tr Ty (ap (_βΉ β) (remove-swap v w))) (shiftSubsTy (swapRemoveπππ v w) π§π
      (subsTy (π u) (reinsertπππ v w) (reinsertPrefixTy v w B C)) (removePrefixTy v w B C)) β©
  tr Ty (ap (_βΉ β) (remove-swap v w)) (shiftTy π§π (subsTy (subsTyVar u (reinsertπππ v w)
    (reinsertPrefixTy v w B C)) (swapRemoveπππ v w) (removePrefixTy v w B C)))
    β‘β¨ trShiftTy (remove-swap v w) (subsTy (subsTyVar u (reinsertπππ v w)
      (reinsertPrefixTy v w B C)) (swapRemoveπππ v w) (removePrefixTy v w B C)) β©
  shiftTy π§π (tr Ty (remove-swap v w) (subsTy (subsTyVar u (reinsertπππ v w)
    (reinsertPrefixTy v w B C)) (swapRemoveπππ v w) (removePrefixTy v w B C)))
    β‘β¨ ap (shiftTy π§π) (subsVarΒ² u v w B C) β©
  shiftTy π§π (subsTy (subsTyVar u v B) w C)
    β‘β¨ shiftSubsTy w π§π (subsTyVar u v B) C β»ΒΉ β©
  subsTy (shiftTy π§π (subsTyVar u v B)) (π π£ w) C
    β

subsTyΒ² : {Ξ³ : TyCtx} {ββ ββ : β€} (A : Ty Ξ³) (v : TyVar Ξ³ ββ) (w : TyVar (removeπππ v) ββ)
  (B : Ty (prefixπππ v)) (C : Ty (prefixπππ w)) β
  tr Ty (remove-swap v w) (subsTy (subsTy A (reinsertπππ v w) (reinsertPrefixTy v w B C))
    (swapRemoveπππ v w) (removePrefixTy v w B C))
    β‘ subsTy (subsTy A v B) w C
subsTyΒ² (π u) v w B C = subsVarΒ² u v w B C
subsTyΒ² (Aβ β Aβ) v w B C =
  tr Ty (remove-swap v w) (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
    (swapRemoveπππ v w) (removePrefixTy v w B C)
      β subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
        (swapRemoveπππ v w) (removePrefixTy v w B C))
    β‘β¨ trβ (remove-swap v w)
      (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
        (swapRemoveπππ v w) (removePrefixTy v w B C))
      (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
        (swapRemoveπππ v w) (removePrefixTy v w B C)) β©
  tr Ty (remove-swap v w) (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
    (swapRemoveπππ v w) (removePrefixTy v w B C))
    β tr Ty (remove-swap v w) (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
      (swapRemoveπππ v w) (removePrefixTy v w B C))
    β‘β¨ ap (tr Ty (remove-swap v w) (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
      (swapRemoveπππ v w) (removePrefixTy v w B C)) β_) (subsTyΒ² Aβ v w B C) β©
  tr Ty (remove-swap v w) (subsTy (subsTy Aβ (reinsertπππ v w) (reinsertPrefixTy v w B C))
    (swapRemoveπππ v w) (removePrefixTy v w B C)) β subsTy (subsTy Aβ v B) w C
    β‘β¨ ap (_β subsTy (subsTy Aβ v B) w C) (subsTyΒ² Aβ v w B C) β©
  subsTy (subsTy Aβ v B) w C β subsTy (subsTy Aβ v B) w C
    β
subsTyΒ² (ββ {β = β} A) v w B C =
  tr Ty (remove-swap v w) (ββ (subsTy (subsTy A (π π£ (reinsertπππ v w))
    (reinsertPrefixTy v w B C)) (π π£ (swapRemoveπππ v w)) (removePrefixTy v w B C)))
    β‘β¨ trββ (remove-swap v w) (subsTy (subsTy A (π π£ (reinsertπππ v w))
      (reinsertPrefixTy v w B C)) (π π£ (swapRemoveπππ v w)) (removePrefixTy v w B C)) β©
  ββ (tr Ty (ap (_βΉ β) (remove-swap v w)) (subsTy (subsTy A (π π£ (reinsertπππ v w))
    (reinsertPrefixTy v w B C)) (π π£ (swapRemoveπππ v w)) (removePrefixTy v w B C)))
    β‘β¨ ap ββ (subsTyΒ² A (π π£ v) (π π£ w) B C) β©
  ββ (subsTy (subsTy A (π π£ v) B) (π π£ w) C)
    β

shiftVar-Ξ³ : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty Ξ³}
  (π : TyPos Ξ³) β Var Ξ A β Var (shiftCtx {β = β} π Ξ) (shiftTy π A)
shiftVar-Ξ³ π v = trπππ (shiftTy π) v

shiftCtxPos-Ξ³ : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³}
  (π : TyPos Ξ³) (π : CtxPos Ξ) β CtxPos (shiftCtx {β = β} π Ξ)
shiftCtxPos-Ξ³ π π = trπππ  (shiftTy π) π

shiftInsert : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (π : TyPos Ξ³) (π : CtxPos Ξ) β
  insertπΆπ‘π₯ (shiftCtxPos-Ξ³ {β = β} π π) (shiftTy π A) β‘ shiftCtx π (insertπΆπ‘π₯ π A)
shiftInsert π π§π = refl
shiftInsert {Ξ = Ξ βΉ A} π (π π π) = ap (_βΉ  shiftTy π A) (shiftInsert π π)

shiftRemove : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (π : TyPos Ξ³) (v : Var Ξ A) β
  shiftCtx {β = β} π (removeπππ v) β‘ removeπππ (shiftVar-Ξ³ π v)
shiftRemove π π§π£ = refl
shiftRemove {Ξ = Ξ βΉ A} π (π π£ v) = ap (_βΉ shiftTy π A) (shiftRemove π v)

shiftPrefix : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (π : TyPos Ξ³) (v : Var Ξ A) β
  shiftCtx {β = β} π (prefixπππ v) β‘ prefixπππ (shiftVar-Ξ³ π v)
shiftPrefix π π§π£ = refl
shiftPrefix π (π π£ v) = shiftPrefix π v

data Tm : {Ξ³ : TyCtx} β Ctx Ξ³ β Ty Ξ³ β Typeβ where
  V : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} β
    Var Ξ A β Tm Ξ A
  Lam : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
    Tm (Ξ βΉ A) B β Tm Ξ (A β B)
  App : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
    Tm Ξ (A β B) β Tm Ξ A β Tm Ξ B
  LAM : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty (Ξ³ βΉ β)} β
    Tm (shiftCtx π§π Ξ) A β Tm Ξ (ββ A)
  APP : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty (Ξ³ βΉ β)} β
    Tm Ξ (ββ A) β (B : Ty Ξ³) β Tm Ξ (subsTy A π§π£ B)

shiftTm : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} (π : CtxPos Ξ) β Tm Ξ B β Tm (insertπΆπ‘π₯ π A) B
shiftTm π (V v) = V (shiftπππ π v)
shiftTm π (Lam t) = Lam (shiftTm (π π π) t)
shiftTm π (App t s) = App (shiftTm π t) (shiftTm π s)
shiftTm {B = ββ A} π (LAM t) =
  LAM (tr (Ξ» Ξ β Tm Ξ A) (shiftInsert π§π π) (shiftTm (shiftCtxPos-Ξ³ π§π π) t))
shiftTm π (APP t A) = APP (shiftTm π t) A

shiftTm-Ξ³ : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty Ξ³}
  (π : TyPos Ξ³) β Tm Ξ A β Tm (shiftCtx {β = β} π Ξ) (shiftTy π A)
shiftTm-Ξ³ π (V v) = V (shiftVar-Ξ³ π v)
shiftTm-Ξ³ π (Lam t) = Lam (shiftTm-Ξ³ π t)
shiftTm-Ξ³ π (App t s) = App (shiftTm-Ξ³ π t) (shiftTm-Ξ³ π s)
shiftTm-Ξ³ π (LAM {Ξ = Ξ} {A} t) =
  LAM (tr (Ξ» Ξ β Tm Ξ (shiftTy (π π π) A)) (shiftCtxΒ² π§π π Ξ) (shiftTm-Ξ³ (π π π) t))
shiftTm-Ξ³ {β = ββ} π (APP {β = ββ}{Ξ = Ξ} {B} t A) =
  tr (Ξ» A β Tm (shiftCtx π Ξ) A) (shiftSubsTy π§π£ (π π π) B A) (APP (shiftTm-Ξ³ π t) (shiftTy π A))

subsVar : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
  Var Ξ B β (v : Var Ξ A) β Tm (prefixπππ v) A β Tm (removeπππ v) B
subsVar = subsπππ V shiftTm

subsTm : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
  Tm Ξ B β (v : Var Ξ A) β Tm (prefixπππ v) A β Tm (removeπππ v) B
subsTm (V w) v s = subsVar w v s
subsTm (Lam t) v s = Lam (subsTm t (π π£ v) s)
subsTm (App tβ tβ) v s = App (subsTm tβ v s) (subsTm tβ v s)
subsTm {A = B} (LAM {A = A} t) v s =
  LAM (tr (Ξ» Ξ β Tm Ξ A) (shiftRemove π§π v β»ΒΉ)
    (subsTm t (shiftVar-Ξ³ π§π v)
      (tr (Ξ» Ξ β Tm Ξ (shiftTy π§π B)) (shiftPrefix π§π v) (shiftTm-Ξ³ π§π s))))
subsTm (APP t A) v s = APP (subsTm t v s) A

subsVar-Ξ³ : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {B : Ty Ξ³} β
  Var Ξ B β (v : TyVar Ξ³ β) (A : Ty (prefixπππ v)) β Var (subsCtx Ξ v A) (subsTy B v A)
subsVar-Ξ³ w v A = trπππ (Ξ» B β subsTy B v A) w 

subsTm-Ξ³ : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {B : Ty Ξ³} β
  Tm Ξ B β (v : TyVar Ξ³ β) (A : Ty (prefixπππ v)) β Tm (subsCtx Ξ v A) (subsTy B v A)
subsTm-Ξ³ (V w) v A = V (subsVar-Ξ³ w v A)
subsTm-Ξ³ (Lam t) v A = Lam (subsTm-Ξ³ t v A)
subsTm-Ξ³ (App t s) v A = App (subsTm-Ξ³ t v A) (subsTm-Ξ³ s v A)
subsTm-Ξ³ (LAM {Ξ = Ξ} {B} t) v A =
  LAM (tr (Ξ» Ξ β Tm Ξ (subsTy B (π π£ v) A)) (shiftSubsCtx v π§π Ξ A) (subsTm-Ξ³ t (π π£ v) A))
subsTm-Ξ³ (APP {Ξ = Ξ} {C} t B) v A =
  tr (Ξ» C β Tm (subsCtx Ξ v A) C) (subsTyΒ² C π§π£ v B A)
   (APP (subsTm-Ξ³ t v A) (subsTy B v A))

-- Round III

Ξ·-helperVar : {Ξ³ : TyCtx} {ββ ββ : β€} (Ξ΄ : TyCtx) (v : TyVar ((Ξ³ βΉ ββ) βΉβΉ Ξ΄) ββ) β
  tr Ty (remove++ π§π£ Ξ΄) (subsTyVar (tr (Ξ» Ξ³β β TyVar Ξ³β ββ) (insert++ (π π π§π) Ξ΄)
    (shiftπππ (π π π§π ++πππ  Ξ΄) v)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))) β‘ π v
Ξ·-helperVar β π§π£ = refl
Ξ·-helperVar β (π π£ v) = refl
Ξ·-helperVar (Ξ΄ βΉ β) π§π£ =
  tr Ty (remove++ π§π£ (Ξ΄ βΉ β)) (subsTyVar (tr (Ξ» Ξ³β β TyVar Ξ³β β)
    (ap (_βΉ β) (insert++ (π π π§π) Ξ΄)) π§π£) (π π£ (π§π£ ++πππ Ξ΄)) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ ap (Ξ» x β tr Ty (remove++ π§π£ (Ξ΄ βΉ β)) (subsTyVar x (π π£ (π§π£ ++πππ Ξ΄))
      (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))) (trπ§π£ (insert++ (π π π§π) Ξ΄)) β©
  tr Ty (ap (_βΉ β) (remove++ π§π£ Ξ΄)) (π π§π£)
    β‘β¨ trππ§π£ (remove++ π§π£ Ξ΄) β©
  π π§π£
    β
Ξ·-helperVar (Ξ΄ βΉ β) (π π£ v) =
  tr Ty (remove++ π§π£ (Ξ΄ βΉ β)) (subsTyVar (tr (Ξ» Ξ³β β TyVar Ξ³β _) (ap (_βΉ β) (insert++ (π π π§π) Ξ΄))
    (π π£ (shiftπππ (π π π§π ++πππ  Ξ΄) v))) (π π£ (π§π£ ++πππ Ξ΄)) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ ap (Ξ» x β tr Ty (remove++ π§π£ (Ξ΄ βΉ β)) (subsTyVar x (π π£ (π§π£ ++πππ Ξ΄))
      (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))) (trπ π£ (insert++ (π π π§π) Ξ΄) (shiftπππ (π π π§π ++πππ  Ξ΄) v)) β©
  tr Ty (ap (_βΉ β) (remove++ π§π£ Ξ΄)) (shiftTy π§π (subsTyVar (tr (Ξ» Ξ£ β πππ Ξ£ _) (insert++ (π π π§π) Ξ΄)
    (shiftπππ (π π π§π ++πππ  Ξ΄) v)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
    β‘β¨ trShiftTy (remove++ π§π£ Ξ΄) (subsTyVar (tr (Ξ» Ξ£ β πππ Ξ£ _) (insert++ (π π π§π) Ξ΄)
      (shiftπππ (π π π§π ++πππ  Ξ΄) v)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))) β©
  shiftTy π§π (tr Ty (remove++ π§π£ Ξ΄) (subsTyVar (tr (Ξ» Ξ£ β πππ Ξ£ _) (insert++ (π π π§π) Ξ΄)
    (shiftπππ (π π π§π ++πππ  Ξ΄) v)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
    β‘β¨ ap (shiftTy π§π) (Ξ·-helperVar Ξ΄ v) β©
  π (π π£ v)
    β

Ξ·-helper : {Ξ³ : TyCtx} {β : β€} (Ξ΄ : TyCtx) (A : Ty ((Ξ³ βΉ β) βΉβΉ Ξ΄)) β
  tr Ty (remove++ π§π£ Ξ΄)
    (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy {β = β} (π π π§π ++πππ  Ξ΄) A)) (π§π£ ++πππ Ξ΄)
      (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))) β‘ A
Ξ·-helper Ξ΄ (π v) =
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (π (shiftπππ (π π π§π ++πππ  Ξ΄) v)))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ ap (Ξ» x β tr Ty (remove++ π§π£ Ξ΄) (subsTy x (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
      (trπ (insert++ (π π π§π) Ξ΄) (shiftπππ (π π π§π ++πππ  Ξ΄) v)) β©
  tr Ty (remove++ π§π£ Ξ΄) (subsTyVar (tr (Ξ» Ξ³β β TyVar Ξ³β _) (insert++ (π π π§π) Ξ΄)
    (shiftπππ (π π π§π ++πππ  Ξ΄) v)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ Ξ·-helperVar Ξ΄ v β©
  π v
    β
Ξ·-helper Ξ΄ (A β B) =
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) A
    β
  shiftTy (π π π§π ++πππ  Ξ΄) B)) (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ ap (Ξ» x β tr Ty (remove++ π§π£ Ξ΄) (subsTy x (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
      (trβ (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) A) (shiftTy (π π π§π ++πππ  Ξ΄) B)) β©
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) A))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))
    β
  subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) B))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ trβ (remove++ π§π£ Ξ΄)
      (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) A))
        (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
      (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) B))
        (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))) β©
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) A))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (shiftTy (π π π§π ++πππ  Ξ΄) B))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ apβ _β_ (Ξ·-helper Ξ΄ A) (Ξ·-helper Ξ΄ B) β©
  A β B
    β
Ξ·-helper Ξ΄ (ββ {β = β} A) =
  tr Ty (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) Ξ΄) (ββ (shiftTy (π π (π π π§π ++πππ  Ξ΄)) A)))
    (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£)))
    β‘β¨ ap (Ξ» x β tr Ty (remove++ π§π£ Ξ΄) (subsTy x (π§π£ ++πππ Ξ΄) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
      (trββ (insert++ (π π π§π) Ξ΄) (shiftTy (π π (π π π§π ++πππ  Ξ΄)) A)) β©
  tr Ty (remove++ π§π£ Ξ΄) (ββ (subsTy (tr Ty (insert++ (π π π§π) (Ξ΄ βΉ β ))
    (shiftTy (π π (π π π§π ++πππ  Ξ΄)) A)) (π π£ (π§π£ ++πππ Ξ΄)) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
    β‘β¨ trββ (remove++ π§π£ Ξ΄) (subsTy (tr Ty (insert++ (π π π§π) (Ξ΄ βΉ β ))
      (shiftTy (π π (π π π§π ++πππ  Ξ΄)) A)) (π π£ (π§π£ ++πππ Ξ΄)) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))) β©
  ββ (tr Ty (remove++ π§π£ (Ξ΄ βΉ β)) (subsTy (tr Ty  (insert++ (π π π§π) (Ξ΄ βΉ β))
    (shiftTy (π π (π π π§π ++πππ  Ξ΄)) A)) (π π£ (π§π£ ++πππ Ξ΄)) (tr Ty (prefix++ π§π£ Ξ΄ β»ΒΉ) (π π§π£))))
    β‘β¨ ap ββ (Ξ·-helper (Ξ΄ βΉ β) A) β©
  ββ A
    β

data RuleTm : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (t s : Tm Ξ A) β Typeβ where
  Ξ²β : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} (t : Tm (Ξ βΉ A) B) (s : Tm Ξ A) β
    RuleTm (App (Lam t) s) (subsTm t π§π£ s)
  Ξ²β : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {β : β€} {A : Ty Ξ³}
    (t : Tm (shiftCtx {β = β} π§π Ξ) (shiftTy π§π A)) (B : Ty Ξ³) β
    RuleTm (APP (LAM t) B)
      (tr (Ξ» Ξ β Tm Ξ (subsTy (shiftTy π§π A) π§π£ B)) (subsShiftCtx π§π£ Ξ B) (subsTm-Ξ³ t π§π£ B))
  Ξ·β : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} (t : Tm Ξ (A β B)) β
    RuleTm t (Lam (App (shiftTm π§π t) (V π§π£)))
  Ξ·β : {Ξ³ : TyCtx} {β : β€} {Ξ : Ctx Ξ³} {A : Ty (Ξ³ βΉ β)} (t : Tm Ξ (ββ A)) β
    RuleTm t (tr (Ξ» A β Tm Ξ A) (ap ββ (Ξ·-helper β A)) (LAM (APP (shiftTm-Ξ³ π§π t) (π π§π£))))

data OTm : {Ξ³ : TyCtx} (Ξ : Ctx Ξ³) (A : Ty Ξ³) β Typeβ where
 π : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} β OTm Ξ A
 πΏ : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β OTm (Ξ βΉ A) B β OTm Ξ (A β B)
 π΄β : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
   OTm Ξ (A β B) β Tm Ξ A β OTm Ξ B
 π΄β : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A B : Ty Ξ³} β
   Tm Ξ (A β B) β OTm Ξ A β OTm Ξ B
 ππΏ : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {β : β€} {A : Ty (Ξ³ βΉ β)} β
   OTm (shiftCtx π§π Ξ) A β OTm Ξ (ββ A)
 ππ΄ : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {β : β€} {A : Ty (Ξ³ βΉ β)} β
   OTm Ξ (ββ A) β (B : Ty Ξ³) β OTm Ξ (subsTy A π§π£ B)

OTm-Ξ³ : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} β OTm Ξ A β TyCtx
OTm-Ξ³ {Ξ³} π = Ξ³
OTm-Ξ³ (πΏ env) = OTm-Ξ³ env
OTm-Ξ³ (π΄β env s) = OTm-Ξ³ env
OTm-Ξ³ (π΄β t env) = OTm-Ξ³ env
OTm-Ξ³ (ππΏ env) = OTm-Ξ³ env
OTm-Ξ³ (ππ΄ env B) = OTm-Ξ³ env

OTm-Ξ : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (env : OTm Ξ A) β Ctx (OTm-Ξ³ env)
OTm-Ξ {Ξ = Ξ} π = Ξ
OTm-Ξ (πΏ env) = OTm-Ξ env
OTm-Ξ (π΄β env x) = OTm-Ξ env
OTm-Ξ (π΄β x env) = OTm-Ξ env
OTm-Ξ (ππΏ env) = OTm-Ξ env
OTm-Ξ (ππ΄ env B) = OTm-Ξ env

OTm-A : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³} (env : OTm Ξ A) β Ty (OTm-Ξ³ env)
OTm-A {A = A} π = A
OTm-A (πΏ env) = OTm-A env
OTm-A (π΄β env x) = OTm-A env
OTm-A (π΄β x env) = OTm-A env
OTm-A (ππΏ env) = OTm-A env
OTm-A (ππ΄ env B) = OTm-A env

OTm-fill : {Ξ³ : TyCtx} {Ξ : Ctx Ξ³} {A : Ty Ξ³}
  (env : OTm Ξ A) β Tm (OTm-Ξ env) (OTm-A env) β Tm Ξ A
OTm-fill π t = t
OTm-fill (πΏ env) t = Lam (OTm-fill env t)
OTm-fill (π΄β env s) t = App (OTm-fill env t) s
OTm-fill (π΄β t env) s = App t (OTm-fill env s)
OTm-fill (ππΏ env) t = LAM (OTm-fill env t)
OTm-fill (ππ΄ env B) t = APP (OTm-fill env t) B

-- Some tests

cβ : {Ξ : TyCtx} β Ty Ξ
cβ = ββ {β = tt} ((π π§π£ β π π§π£) β π π§π£ β π π§π£)

cβ₯ : {Ξ : TyCtx} β Ty Ξ
cβ₯ = ββ {β = tt} (π π§π£)

test1 : Tm {β} β cβ
test1 = LAM (Lam (Lam (App (V (π π£ π§π£)) (V π§π£))))

test2 = APP test1 cβ₯
