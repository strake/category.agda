module Category.Profunctor where

open import Agda.Primitive
open import Category
open import Category.Product
open import Data.Product

Profunctor : ∀ {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂ a b ℓ} (K₁ : Category a₁ b₁ ℓ₁) (K₂ : Category a₂ b₂ ℓ₂) (K : Category a b ℓ) → Set (lsuc (a₁ ⊔ b₁ ⊔ ℓ₁ ⊔ a₂ ⊔ b₂ ⊔ ℓ₂ ⊔ a ⊔ b ⊔ ℓ))
Profunctor K₁ K₂ K = Functor (K₁ ×c Category.dual K₂) K

record IsRelated {a b ℓ a' b' ℓ'} {K : Category a b ℓ} {K' : Category a' b' ℓ'} (F : Endofunctor K) (P : Profunctor K K K') : Set (a ⊔ b ⊔ ℓ ⊔ a' ⊔ b' ⊔ ℓ') where
    field
        relate : ∀ {A B} → Category._⇨_ K' (Functor.F P (A , B)) (Functor.F P (Functor.F F A , Functor.F F B))
