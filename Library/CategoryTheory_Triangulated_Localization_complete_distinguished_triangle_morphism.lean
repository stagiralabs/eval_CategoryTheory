import VerifiedAgora.tagger
namespace CategoryTheory.Triangulated.Localization

open CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ] [L.CommShift ℤ] (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions] [W.IsCompatibleWithTriangulation]
include W in
@[target]
lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ L.essImageDistTriang) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  sorry