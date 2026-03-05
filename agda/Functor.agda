{-
    Definition of functor between two categories
-}
module Functor where

open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)
open import Category as Cat using (Category)
open Category renaming (_∘_ to comp) -- have to rename so that it doesn't conflict with functor composition

record Functor (𝒞 𝒟 : Category) : Set where
    field
        obj-map : Objects 𝒞 → Objects 𝒟
        morph-map : {A B : Objects 𝒞} (f : Hom 𝒞 A B) → Hom 𝒟 (obj-map A) (obj-map B)

        preserves-id : (A : Objects 𝒞) → morph-map (id 𝒞 A) ≡ id 𝒟 (obj-map A)
        preserves-comp : {A B C : Objects 𝒞} (g : Hom 𝒞 B C) (f : Hom 𝒞 A B) → 
            (morph-map (comp 𝒞 g f) ≡ comp 𝒟 (morph-map g) (morph-map f))

open Functor

_∘_ : {𝒜 ℬ 𝒞 : Category} (G : Functor ℬ 𝒞) → (F : Functor 𝒜 ℬ) → Functor 𝒜 𝒞
_∘_ G F = record
  { obj-map = λ A → obj-map G (obj-map F A)
  ; morph-map = λ f → morph-map G (morph-map F f)
  ; preserves-id = λ A → trans (cong (morph-map G) (preserves-id F A)) (preserves-id G ( obj-map F A))
  ; preserves-comp = λ g f → trans 
    (cong (morph-map G) (preserves-comp F g f)) 
    (preserves-comp G (morph-map F g) (morph-map F f))
  }