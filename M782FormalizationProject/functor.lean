/-
  What is a category without morphisms?
  What is a definition of category without functors?
-/
import M782FormalizationProject.category
open MyCategory

structure MyFunctor (C D : MyCategory) where
  map_obj : C.objects → D.objects
  map_morph : (A : C.objects) -> (B : C.objects) -> (C.Hom A B) -> (D.Hom (map_obj A) (map_obj B))

  preserves_id : ∀ a : C.objects, D.id (map_obj a) = map_morph a a (C.id a)
  preserves_comp : ∀ a b c : C.objects, ∀ f : C.Hom a b, ∀ g : C.Hom b c,
    map_morph a c (C.comp a b c f g) = (map_morph b c g) ∘ (map_morph a b f)



instance double_func : MyFunctor BN BN := {
  map_obj := fun _ => single.el
  map_morph A B n := 2*n

  preserves_id A := by
    cases A
    rfl

  preserves_comp a b c f g := by
    rw [comp]


}
