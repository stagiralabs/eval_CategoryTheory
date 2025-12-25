import VerifiedAgora.tagger
namespace CategoryTheory.Limits.Cocones

open CategoryTheory CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K] {C : Type u₃} [Category.{v₃} C] {D : Type u₄}
  [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E] {F : J ⥤ C}
/-- Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
@[target]
theorem cocone_iso_of_hom_iso {K : J ⥤ C} {c d : Cocone K} (f : c ⟶ d) [i : IsIso f.hom] :
    IsIso f :=
  ⟨⟨{ hom := inv f.hom
      w := fun j => (asIso f.hom).comp_inv_eq.2 (f.w j).symm }, by sorry