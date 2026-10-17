import MultiplicativeBasisDeformations.Foundations.GaugeTransfer
import MultiplicativeBasisDeformations.Foundations.RowRotation

/-!
# Cokernels spanned by given rows

In characteristic two the derivative cokernels need not vanish
(`prop:residual-correction-spaces`, `positive-deformations.tex:23–48`): each periodic
component contributes at most one line, spanned by a single row. We record "the
cokernel classes of all rows of degree at least three lie in the span of the
classes of the rows in `S`" (`CokerSpan`), and show that it is preserved by
rescaling arrows and entire mesh relations (`periodic-mesh-calculations.tex:236–241`:
"rescaling arrows and entire relations changes the mesh derivative by invertible
diagonal maps, so it changes neither its cokernel …").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [DecidableEq V]

namespace ScalarMeshCategory

variable (c : MeshCoefficients k Q)

/-- A set of rows: paths `τ x → x` at nonprojective vertices. -/
abbrev RowSet (Q : TranslationQuiver V) := Set (Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)

/-- The span of the classes of the rows of `S` of degree `m + 1`. -/
def rowSpan (m : ℕ) (S : RowSet Q) : Submodule k (Coker c m) :=
  Submodule.span k ((fun R ↦ rowClass c m R.1 R.2) '' {R | R ∈ S ∧ R.2.length = m + 1})

/-- **The cokernels are spanned by the rows of `S`.** -/
def CokerSpan (S : RowSet Q) : Prop :=
  ∀ m, 2 ≤ m → ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
    rowClass c m x w ∈ rowSpan c m S

theorem rowClass_mem_rowSpan {m : ℕ} {S : RowSet Q} {R : Σ x : Q.nonprojective,
    Quiver.Path (Q.tau x).1 x.1} (hR : R ∈ S) (hl : R.2.length = m + 1) :
    rowClass c m R.1 R.2 ∈ rowSpan c m S :=
  Submodule.subset_span ⟨R, ⟨hR, hl⟩, rfl⟩

theorem rowSpan_mono {m : ℕ} {S S' : RowSet Q} (h : S ⊆ S') : rowSpan c m S ≤ rowSpan c m S' :=
  Submodule.span_mono (Set.image_mono fun _ hR ↦ ⟨h hR.1, hR.2⟩)

theorem rowSpan_empty (m : ℕ) : rowSpan c m (∅ : RowSet Q) = ⊥ := by
  rw [rowSpan, Submodule.span_eq_bot]
  rintro _ ⟨R, ⟨hR, -⟩, rfl⟩
  exact absurd hR (Set.notMem_empty _)

theorem cokerSpan_empty_iff [Fintype Q.nonprojective] [∀ x y : V, DecidableEq (x ⟶ y)]
    [DecidablePred (· ∈ Q.nonprojective)] :
    CokerSpan c (∅ : RowSet Q) ↔ ∀ m, 2 ≤ m → MeshDerivativeSurjective c m := by
  constructor
  · intro h m hm
    rw [surjective_iff_rows]
    intro x w hw
    have := h m hm x w hw
    rw [rowSpan_empty, Submodule.mem_bot, rowClass, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · intro h m hm x w hw
    have := (surjective_iff_rows c m).1 (h m hm) x w hw
    rw [rowSpan_empty, Submodule.mem_bot, rowClass, Submodule.Quotient.mk_eq_zero]
    exact this

/-! ### Gauge invariance -/

variable (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ) (c' : MeshCoefficients k Q)
  (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a)

/-- The gauge on mesh families, `g ↦ η Φ(g)`. -/
def gaugeFam : MeshFamily c →ₗ[k] MeshFamily c' where
  toFun g x := ((η x : kˣ) : k) • (gaugeQ μ η c c' h).map (g x)
  map_add' g g' := by
    funext x
    simp only [Pi.add_apply]
    rw [gaugeQ_map_add, smul_add]
    rfl
  map_smul' t g := by
    funext x
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [gaugeQ_map_smul, smul_comm]
    rfl

theorem gaugeFam_imageD (m : ℕ) : imageD c m ≤ (imageD c' m).comap (gaugeFam c μ η c' h) := by
  rintro g ⟨f, hf, rfl⟩
  refine ⟨gaugeFamily μ η c c' h f, gaugeFamily_mem μ η c c' h hf, ?_⟩
  funext x
  rw [meshDerivativeₗ_apply, meshDerivative_gauge]
  rfl

/-- The induced map on cokernels. -/
def gaugeCoker (m : ℕ) : Coker c m →ₗ[k] Coker c' m :=
  (imageD c m).mapQ (imageD c' m) (gaugeFam c μ η c' h) (gaugeFam_imageD c μ η c' h m)

theorem gaugeCoker_rowClass (m : ℕ) (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) :
    gaugeCoker c μ η c' h m (rowClass c m x w) =
      (((η x : kˣ) : k) * ((pathWt μ w : kˣ) : k)) • rowClass c' m x w := by
  rw [rowClass, gaugeCoker, Submodule.mapQ_apply, rowClass, ← Submodule.Quotient.mk_smul]
  congr 1
  funext x'
  change ((η x' : kˣ) : k) • (gaugeQ μ η c c' h).map (row c x w x') = _
  by_cases hx : x' = x
  · subst hx
    simp only [row, Pi.single_eq_same, gaugeQ_pathMor, Pi.smul_apply]
    exact (mul_smul _ _ (pathMor c' w)).symm
  · simp only [row, Pi.single_eq_of_ne hx, Pi.smul_apply]
    rw [gaugeQ_map_zero, smul_zero, smul_zero]
    rfl

include h in
/-- **Spanning rows transfer along a gauge transformation.** -/
theorem rowClass_mem_rowSpan_gauge {m : ℕ} {S : RowSet Q} {x : Q.nonprojective}
    {w : Quiver.Path (Q.tau x).1 x.1} (hx : rowClass c m x w ∈ rowSpan c m S) :
    rowClass c' m x w ∈ rowSpan c' m S := by
  have h1 := Submodule.mem_map_of_mem (f := gaugeCoker c μ η c' h m) hx
  rw [gaugeCoker_rowClass, rowSpan, Submodule.map_span] at h1
  have h2 : Submodule.span k (gaugeCoker c μ η c' h m '' ((fun R ↦ rowClass c m R.1 R.2) ''
      {R | R ∈ S ∧ R.2.length = m + 1})) ≤ rowSpan c' m S := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨R, hR, rfl⟩, rfl⟩
    rw [gaugeCoker_rowClass]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨R, hR, rfl⟩)
  have h3 := h2 h1
  set e : kˣ := η x * pathWt μ w
  have := Submodule.smul_mem _ ((e⁻¹ : kˣ) : k) h3
  rwa [smul_smul, show ((e⁻¹ : kˣ) : k) * (((η x : kˣ) : k) * ((pathWt μ w : kˣ) : k)) = 1 by
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul] at this

include h in
theorem cokerSpan_gauge {S : RowSet Q} (hS : CokerSpan c S) : CokerSpan c' S :=
  fun m hm x w hw ↦ rowClass_mem_rowSpan_gauge c μ η c' h (hS m hm x w hw)

end ScalarMeshCategory

end MultiplicativeBasisDeformations
