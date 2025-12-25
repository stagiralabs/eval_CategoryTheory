import VerifiedAgora.tagger
namespace CategoryTheory.Triangulated.Localization

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ] (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive]
include W in
@[target]
lemma isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  sorry