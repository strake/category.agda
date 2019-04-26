module Category.Slice where

open import Agda.Primitive
open import Data.Product
open import Function using (_on_)
open import Relation.Binary
open import Relation.Binary.Core
import Relation.Binary.EqReasoning as EqR

open import Category as Category_

_/_ : {a b ℓ : _} → (K : Category a b ℓ) → Category.Dot K → Category _ _ _
K / C = record
    { Dot = SliceDot;
      _⇨_ = _/⇨/_;
      id  = λ {f} → id {domain (proj₂ f)} , IsEquivalence.sym isEquivalence (proj₂ ident);
      _∘_ = _/∘/_;
      _≈_ = _≈_ on proj₁;
      isCategory = record { isEquivalence = isSliceEquivalence; ∘-cong = ∘-cong; ident = ident; assoc = assoc } }
  where open Category K

        SliceDot : Set _
        SliceDot = ∃ λ (A : Dot) → A ⇨ C

        _/⇨/_ : SliceDot → SliceDot → Set _
        (_ , f) /⇨/ (_ , g) = ∃ (λ h → f ≈ g ∘ h)

        _/∘/_ : {φ χ ψ : SliceDot} → (χ /⇨/ ψ) → (φ /⇨/ χ) → (φ /⇨/ ψ)
        _/∘/_ {(_ , φ)} {(_ , χ)} {(_ , ψ)} (f , χ≈ψ∘f) (g , φ≈χ∘g) =
            f ∘ g , (begin φ ≈⟨ φ≈χ∘g ⟩              χ ∘ g
                             ≈⟨ ∘-cong χ≈ψ∘f refl' ⟩ (ψ ∘ f) ∘ g
                             ≈⟨ assoc ⟩              ψ ∘ (f ∘ g) ∎)
          where open EqR homSetoid
                open IsEquivalence (Setoid.isEquivalence homSetoid) renaming (refl to refl')

        isSliceEquivalence : {A B : SliceDot} → IsEquivalence {_} {_} {A /⇨/ B} (_≈_ on proj₁)
        isSliceEquivalence = record { refl = refl'; sym = sym; trans = trans }
          where open IsEquivalence isEquivalence renaming (refl to refl')
