module Category where

open import Relation.Binary.PropositionalEquality using (_≡_; cong)

record Category : Set₁ where
    field
        Objects : Set
        Hom : Objects → Objects → Set
        _∘_ : {A B C : Objects} → (Hom B C) → (Hom A B) → (Hom A C)

        id : (A : Objects) → Hom A A

        id-law-left : {A B : Objects} (f : Hom B A) → (id A) ∘ f ≡ f
        id-law-right : {A B : Objects} (f : Hom A B) → f ∘ (id A) ≡ f

        assoc : {A B C D : Objects} (h : Hom C D) (g : Hom B C) (f : Hom A B) → 
            h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f

module BasicProps (∁ : Category) where
  open Category ∁

  postcomp-preserves-eq : {A B C : Objects} {g h : Hom A B} (f : Hom B C) → (g ≡ h) → (f ∘ g ≡ f ∘ h)
  postcomp-preserves-eq f eq = cong (λ k → f ∘ k) eq 

  precomp-preserves-eq : {A B C : Objects} {g h : Hom B C} (f : Hom A B) → (g ≡ h) → (g ∘ f ≡ h ∘ f)
  precomp-preserves-eq f eq = cong (λ k → k ∘ f) eq