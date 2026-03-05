{-
    Definitions of monomorphism, epimorphism, split epi/mono, and is_isomorphism
    Easy theorems such as split epi/mono ⇒ epi/mono
-}
open import Category as Cat using (Category)

module Morphism (∁ : Category) where
open Category ∁
open Cat.BasicProps ∁ using (postcomp_preserves_eq; precomp_preserves_eq)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)

is_monomorphism : {B C : Objects} (f : Hom B C) → Set
is_monomorphism {B} {C} f = {A : Objects} (g h : Hom A B) → (f ∘ g ≡ f ∘ h) → (g ≡ h)

is_split_mono : {A B : Objects} (f : Hom A B) → Set
is_split_mono {A} {B} f = Σ (Hom B A) (λ g → g ∘ f ≡ (id A))

is_epimorphism : {A B : Objects} (f : Hom A B) → Set
is_epimorphism {A} {B} f = {C : Objects} (g h : Hom B C) → (g ∘ f ≡ h ∘ f) → (g ≡ h)

is_split_epi : {A B : Objects} (f : Hom A B) → Set
is_split_epi {A} {B} f = Σ (Hom B A) (λ g → f ∘ g ≡ (id B))

is_isomorphism : {A B : Objects} (f : Hom A B) → Set
is_isomorphism f = is_split_epi f × is_split_mono f


--
-- This is...really ugly. I want there to be some syntax for long chains of PropositionalEquality 
-- (or any transitive relation) but I don't know where to look.
-- I think there is some kind of _≡〈_〉_ syntax defined somewhere but not exported?
--
split_mono_is_mono : {A B : Objects} (f : Hom A B) → (is_split_mono f) → (is_monomorphism f)
split_mono_is_mono f = λ x g h fg_eq_fh → 
  let f' = proj₁ x 
      f'f_eq_id = proj₂ x
      g_eq_ff'g = trans (trans 
        (sym (id_law_left g)) -- g = id ∘ g
        (precomp_preserves_eq g (sym f'f_eq_id)) -- id ∘ g = (f' ∘ f) ∘ g
        ) (sym (assoc f' f g)) -- (f' ∘ f) ∘ g = f' ∘ (f ∘ g)
      ff'h_eq_h = trans (trans
        (assoc f' f h) -- f' ∘ (f ∘ h) = (f' ∘ f) ∘ h
        (precomp_preserves_eq h f'f_eq_id) -- (f' ∘ f) ∘ h = id ∘ h
        ) (id_law_left h)
  in trans (trans 
    g_eq_ff'g       -- g = f' ∘ (f ∘ g)
    (postcomp_preserves_eq f' fg_eq_fh)   -- f' ∘ (f ∘ g) = f' ∘ (f ∘ h)
    ) ff'h_eq_h       -- f' ∘ (f ∘ h) = h