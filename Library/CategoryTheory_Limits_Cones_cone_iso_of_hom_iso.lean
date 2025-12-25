import VerifiedAgora.tagger
namespace CategoryTheory.Limits.Cones

open CategoryTheory CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K] {C : Type u₃} [Category.{v₃} C] {D : Type u₄}
  [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E] {F : J ⥤ C}
/-- Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
@[target]
theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f :=
  ⟨⟨{   hom := inv f.hom
        w := fun j => (asIso f.hom).inv_comp_eq.2 (f.w j).symm }, by sorry