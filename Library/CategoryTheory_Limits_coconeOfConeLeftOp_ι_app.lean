import VerifiedAgora.tagger
namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K] {C : Type u₃} [Category.{v₃} C] {D : Type u₄}
  [Category.{v₄} D] {E : Type u₅} [Category.{v₅} E] {F : J ⥤ Cᵒᵖ}
@[target, simp]
theorem coconeOfConeLeftOp_ι_app (c : Cone F.leftOp) (j) :
    (coconeOfConeLeftOp c).ι.app j = (c.π.app (op j)).op := by
  sorry