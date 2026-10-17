import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows

/-!
# The path-length grading of a scalar mesh category

`graded-category.tex:156–157`: "The quotient is graded by path length." The
mesh relations are homogeneous, so the degree projections of `kQ` descend to
`C(Q, c)` and its degree parts are independent (`iSupIndep_degreePart`). If
`C(Q, c)` is finite-dimensional, only finitely many degree parts are nonzero,
so all sufficiently long paths vanish (`exists_pathMor_eq_zero`); this is the
first step of the proof of Proposition 4.1
(`periodic-mesh-calculations.tex:28–31`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

section Comm

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

/-- The quotient map `kQ(x, y) → C(x, y)`. -/
abbrev quotL (x y : V) :=
  (RelationCategory.functor k (meshRelations c)).mapLinearMap k
    (X := LinearPaths.obj (k := k) x) (Y := LinearPaths.obj y)

theorem quotL_surjective (x y : V) : Function.Surjective (quotL c x y) :=
  fun g ↦ (RelationCategory.functor k (meshRelations c)).map_surjective g

theorem ker_quotL_le (d : ℕ) (x y : V) :
    LinearMap.ker (quotL c x y) ≤
      LinearMap.ker ((quotL c x y).comp (LinearPaths.proj (k := k) d x y)) := by
  intro F hF
  rw [LinearMap.mem_ker] at hF ⊢
  change (RelationCategory.functor k (meshRelations c)).map F = 0 at hF
  change (RelationCategory.functor k (meshRelations c)).map (LinearPaths.proj d x y F) = 0
  rw [RelationCategory.functor_map_eq_zero_iff] at hF ⊢
  exact LinearPaths.proj_mem_linearSpan _ (meshRelations_homogeneous c) d hF

/-- The degree-`d` projection on the Hom spaces of `C(Q, c)`. -/
def degProj (d : ℕ) (x y : V) : (obj c x ⟶ obj c y) →ₗ[k] (obj c x ⟶ obj c y) :=
  ((LinearMap.ker (quotL c x y)).liftQ _ (ker_quotL_le c d x y)).comp
    ((quotL c x y).quotKerEquivOfSurjective (quotL_surjective c x y)).symm.toLinearMap

theorem degProj_apply (d : ℕ) {x y : V} (F : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    degProj c d x y ((RelationCategory.functor k (meshRelations c)).map F) =
      (RelationCategory.functor k (meshRelations c)).map (LinearPaths.proj d x y F) := by
  have h1 : ((quotL c x y).quotKerEquivOfSurjective (quotL_surjective c x y)).symm
      ((RelationCategory.functor k (meshRelations c)).map F) = Submodule.Quotient.mk F := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [degProj, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [h1]
  rfl

/-- The degree parts of the Hom spaces of `C(Q, c)` are independent. -/
theorem iSupIndep_degreePart (x y : V) : iSupIndep fun d ↦ degreePart c d x y := by
  rw [iSupIndep_def]
  intro d
  rw [Submodule.disjoint_def]
  intro g hd hsup
  have hfix : ∀ e, ∀ g' ∈ degreePart c e x y, degProj c d x y g' = if e = d then g' else 0 := by
    intro e g' hg'
    obtain ⟨F, hF, rfl⟩ := hg'
    change degProj c d x y ((RelationCategory.functor k (meshRelations c)).map F) = _
    rw [degProj_apply, LinearPaths.proj_of_mem hF]
    split_ifs <;> simp
  have hle : (⨆ e, ⨆ (_ : e ≠ d), degreePart c e x y) ≤ LinearMap.ker (degProj c d x y) := by
    refine iSup₂_le fun e he g' hg' ↦ ?_
    rw [LinearMap.mem_ker, hfix e g' hg', if_neg he]
  have h1 := hfix d g hd
  rw [if_pos rfl] at h1
  have h2 : degProj c d x y g = 0 := hle hsup
  rw [← h1, h2]

end Comm

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

/-- In a finite-dimensional scalar mesh category on a finite quiver, all
sufficiently long paths vanish. -/
theorem exists_pathMor_eq_zero [Finite V]
    (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) :
    ∃ N : ℕ, ∀ (x y : V) (p : Quiver.Path x y), N ≤ p.length → pathMor c p = 0 := by
  classical
  have hN : ∀ x y : V, ∃ N : ℕ, ∀ d, N ≤ d → degreePart c d x y = ⊥ := by
    intro x y
    haveI := hfin x y
    letI := (iSupIndep_degreePart c x y).fintypeNeBotOfFiniteDimensional
    refine ⟨(Finset.univ.image fun i : {d // degreePart c d x y ≠ ⊥} ↦ i.1).sup id + 1,
      fun d hd ↦ ?_⟩
    by_contra h
    have : d ≤ (Finset.univ.image fun i : {d // degreePart c d x y ≠ ⊥} ↦ i.1).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image.2 ⟨⟨d, h⟩, Finset.mem_univ _, rfl⟩)
    omega
  choose N hN using hN
  haveI := Fintype.ofFinite V
  refine ⟨Finset.univ.sup fun xy : V × V ↦ N xy.1 xy.2, fun x y p hp ↦ ?_⟩
  have hle : N x y ≤ p.length :=
    le_trans (Finset.le_sup (f := fun xy : V × V ↦ N xy.1 xy.2) (Finset.mem_univ (x, y))) hp
  have := pathMor_mem_degreePart c p
  rw [hN x y _ hle, Submodule.mem_bot] at this
  exact this

end ScalarMeshCategory

end MultiplicativeBasisDeformations
