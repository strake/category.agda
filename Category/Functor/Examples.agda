module Category.Functor.Examples where

open import Agda.Primitive
open import Category
open import Category.Examples
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

×-IsFunctorₗ : {ℓ : _} (C : Set ℓ) → IsFunctor (set ℓ) (set ℓ) (flip _×_ C) (λ { f (a , b) → (f a , b) })
×-IsFunctorₗ _ = record { cong = λ { refl → refl }; ident = refl; distrib = refl }

×-Functorₗ : {ℓ : _} (C : Set ℓ) → Functor (set ℓ) (set ℓ)
×-Functorₗ C = record { isFunctor = ×-IsFunctorₗ C }

×-IsFunctorᵣ : {ℓ : _} (C : Set ℓ) → IsFunctor (set ℓ) (set ℓ) (_×_ C) (λ { f (a , b) → (a , f b) })
×-IsFunctorᵣ _ = record { cong = λ { refl → refl }; ident = refl; distrib = refl }

×-Functorᵣ : {ℓ : _} (C : Set ℓ) → Functor (set ℓ) (set ℓ)
×-Functorᵣ C = record { isFunctor = ×-IsFunctorᵣ C }

×-IsFunctor'ᵣ : {ℓ : _} (C : Set ℓ) → IsFunctor (set ℓ) (set ℓ) (_×_ C) (λ { f (a , b) → (a , f b) })
×-IsFunctor'ᵣ _ = record { cong = λ { refl → refl }; ident = refl; distrib = refl }

×-Functor'ᵣ : {ℓ : _} (C : Set ℓ) → Functor (set ℓ) (set ℓ)
×-Functor'ᵣ C = record { isFunctor = ×-IsFunctorᵣ C }
