module Category.Examples where

open import Agda.Primitive
open import Data.Product
open import Function
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Category as Category_

set : (ℓ : _) → Category (lsuc ℓ) ℓ ℓ
set ℓ = record
    { _⇨_ = λ A B → A → B;
      isCategory = record
          { isEquivalence = ≡.isEquivalence;
            ∘-cong = ≡.cong₂ _∘′_;
            ident = refl , refl;
            assoc = refl } }

private constIsFunctor : ∀ {a b ℓ a' b' ℓ'} (K : Category a b ℓ) (K' : Category a' b' ℓ') (A : Category.Dot K') → IsFunctor K K' (const A) (const (Category.id K'))
constIsFunctor K K' A = record
  { cong = const r
  ; ident = r
  ; distrib = λ {A B C u v} → p A B C u v }
  where
    open Category K' using (_≈_)
    open import Relation.Binary.Core
    open import Relation.Binary.PropositionalEquality
    r = IsEquivalence.refl (Category.isEquivalence K')
    p : ∀ A B C u v → const (Category.id K') (Category._∘_ K u v) ≈ Category._∘_ K' (const (Category.id K') u) (const (Category.id K') v)
    p _ _ _ _ _ = IsEquivalence.sym (Category.isEquivalence K') ∘ proj₁ $ Category.ident K' {_} {_} {Category.id K'}

constFunctor : ∀ {a b ℓ a' b' ℓ'} (K : Category a b ℓ) (K' : Category a' b' ℓ') → Category.Dot K' → Functor K K'
constFunctor K K' A = record { isFunctor = constIsFunctor K K' A }

private idIsFunctor : ∀ {a b ℓ} (K : Category a b ℓ) → IsFunctor K K id id
idIsFunctor K = record
  { cong = id
  ; ident = IsEquivalence.refl (Category.isEquivalence K)
  ; distrib = IsEquivalence.refl (Category.isEquivalence K) }
  where
    open import Relation.Binary.PropositionalEquality

idFunctor : ∀ {a b ℓ} (K : Category a b ℓ) → Functor K K
idFunctor K = record { isFunctor = idIsFunctor K }

{-
IsNaturalTransformation : {a b ℓ a' b' ℓ' : _} {K : Category a b ℓ} {K' : Category a' b' ℓ'} (F G : Functor K K') → ({A : Category.Dot K} → Category._⇨_ K' (Functor.F F A) (Functor.F G A)) → Set _
IsNaturalTransformation {_} {_} {_} {_} {_} {_} {K} {K'} F G ν = {A B : _} (f : Category._⇨_ K A B) → Category._≈_ K' (ν {B} ∘ Functor.f F f) (Functor.f G f ∘ ν {A})

functor : {a b ℓ a' b' ℓ' : _} → Category a b ℓ → Category a' b' ℓ' → Category _ _ _
functor K K' = record
  { Dot = Functor K K'
  ; _⇨_ = λ F G → {A : Category.Dot K} → Category._⇨_ K' (Functor.F F A) (Functor.F G A)
  ; isCategory = record
      { } }
-}
