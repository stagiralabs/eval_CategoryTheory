import VerifiedAgora.tagger
namespace CategoryTheory.Triangulated.Localization

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ] (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
include W in
@[target]
lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  sorry