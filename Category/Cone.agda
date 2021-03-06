module Category.Cone where

open import Agda.Primitive
open import Data.Product
open import Function using (_on_)
open import Relation.Binary.Core using (IsEquivalence)

open import Category as Category_

record Cone {a b ℓ a' b' ℓ'} {J : Category a' b' ℓ'} {C : Category a b ℓ} (d : Functor J C) : Set (a ⊔ b ⊔ a' ⊔ b' ⊔ ℓ) where
    open Category C
    open Functor d

    field apex : Dot
          apicalEdge : (j : Category.Dot J) → apex ⇨ F j
          isCone : (i j : Category.Dot J) → (α : Category._⇨_ J i j) → f α ∘ apicalEdge i ≈ apicalEdge j

cone : {a b ℓ a' b' ℓ' : _} → {J : Category a' b' ℓ'} → {C : Category a b ℓ} → Functor J C → Category _ _ _
cone {_} {_} {_} {_} {_} {_} {J} {C} d = record
    { Dot = Cone d;
      _⇨_ = λ A B → ∃ λ (v : Cone.apex A ⇨ Cone.apex B) → (j : Category.Dot J) → Cone.apicalEdge A j ≈ Cone.apicalEdge B j ∘ v;
      id  = id , λ j → IsEquivalence.sym isEquivalence (proj₂ ident);
      _∘_ = λ { (u , f) (v , g) → u ∘ v , λ j → let trans = IsEquivalence.trans isEquivalence
                                                in trans (trans (g j) (∘-cong (f j) (IsEquivalence.refl isEquivalence))) assoc };
      _≈_ = _≈_ on proj₁;
      isCategory = record
          { isEquivalence = record
                { refl  = IsEquivalence.refl  isEquivalence;
                  sym   = IsEquivalence.sym   isEquivalence;
                  trans = IsEquivalence.trans isEquivalence };
            ∘-cong = ∘-cong;
            ident = ident;
            assoc = assoc } }
  where open Category C

IsLimit : {a b ℓ a' b' ℓ' : _} → {J : Category a' b' ℓ'} → {C : Category a b ℓ} → {d : Functor J C} → Cone d → Set _
IsLimit {_} {_} {_} {_} {_} {_} {_} {_} {d} = Category.Property.IsTerminal (cone d)
