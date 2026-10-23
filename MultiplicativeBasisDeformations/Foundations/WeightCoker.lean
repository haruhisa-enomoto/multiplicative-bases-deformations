module

public import MultiplicativeBasisDeformations.Foundations.WeightLift
public import MultiplicativeBasisDeformations.Foundations.RowSpan

/-!
# Weights of mesh corrections (Proposition 7.6, weights)

`weights-and-parameters.tex`: "a mesh weight `w` grades `V_{m+1}(C)` by giving a
path at row `v` the weight `w(path) − ν_v`, and grades `U_m(C)` by giving a path parallel
to an arrow `a` the weight `w(path) − w(a)`. The map `D_m` preserves these gradings,
because each term `(σa)a` of the mesh at `v` has weight `ν_v`. Hence `coker D_m` is
graded".

`mfProj χ`, `afProj χ` are the relative weight-`χ` projections of mesh and arrow
families; `D_m` commutes with them (`meshDerivative_afProj`), so they descend to the
cokernel (`cokerProj`). Consequently, when the rows of `S` span the cokernels, a family of
relative weight `χ` lies in the span of the rows of `S` of relative weight `χ`
(`mem_rowSpan_char`), and so does the class `Ψ[μ]` of a cocycle of character `χ`
(`Ψc_mem_rowSpan_char`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) (χ : M)

/-- The relative weight-`χ` projection of mesh families. -/
def mfProj : MeshFamily c →ₗ[k] MeshFamily c :=
  LinearMap.pi fun x ↦ wπ c W (W.ν x + χ) (Q.tau x).1 x.1 ∘ₗ LinearMap.proj (R := k)
    (φ := fun x : Q.nonprojective ↦ obj c (Q.tau x).1 ⟶ obj c x.1) x

theorem mfProj_apply (z : MeshFamily c) (x : Q.nonprojective) :
    mfProj W χ z x = wπ c W (W.ν x + χ) (Q.tau x).1 x.1 (z x) := rfl

/-- The relative weight-`χ` projection of arrow families. -/
def afProj : ArrowFamily c →ₗ[k] ArrowFamily c :=
  LinearMap.pi fun a ↦ wπ c W (W.w a.2.2 + χ) a.1 a.2.1 ∘ₗ LinearMap.proj (R := k)
    (φ := fun a : Σ x y : V, x ⟶ y ↦ obj c a.1 ⟶ obj c a.2.1) a

theorem afProj_apply (f : ArrowFamily c) (a : Σ x y : V, x ⟶ y) :
    afProj W χ f a = wπ c W (W.w a.2.2 + χ) a.1 a.2.1 (f a) := rfl

include hfin in
/-- **`D_m` preserves the relative weights.** -/
theorem meshDerivative_afProj (f : ArrowFamily c) :
    meshDerivative c (afProj W χ f) = mfProj W χ (meshDerivative c f) := by
  funext x
  rw [mfProj_apply]
  simp only [meshDerivative, map_sum, map_smul, map_add, afProj_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 2
  · rw [show W.ν x + χ = W.w (Q.mate x a.1 a.2) + χ + W.w a.2 by rw [← W.mesh x a]; abel]
    exact (wπ_comp_right W hfin (arrowMor_mem_wP W a.2) _ _).symm
  · rw [show W.ν x + χ = W.w (Q.mate x a.1 a.2) + (W.w a.2 + χ) by rw [← W.mesh x a]; abel]
    exact (wπ_comp_left W hfin (arrowMor_mem_wP W _) _ _).symm

theorem afProj_mem {m : ℕ} {f : ArrowFamily c} (hf : f ∈ familiesDeg c m) :
    afProj W χ f ∈ familiesDeg c m := fun a ↦ wπ_mem_degreePart W _ (hf a)

include hfin in
theorem mfProj_imageD (m : ℕ) : imageD c m ≤ (imageD c m).comap (mfProj W χ) := by
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨afProj W χ f, afProj_mem W χ hf, meshDerivative_afProj W hfin χ f⟩

/-- The relative weight-`χ` projection of the cokernel. -/
def cokerProj (m : ℕ) : Coker c m →ₗ[k] Coker c m :=
  (imageD c m).mapQ (imageD c m) (mfProj W χ) (mfProj_imageD W hfin χ m)

theorem mfProj_row (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) :
    mfProj W χ (row c x w) = if W.pw w = W.ν x + χ then row c x w else 0 := by
  funext x'
  rw [mfProj_apply]
  by_cases hx : x' = x
  · subst hx
    simp only [row, Pi.single_eq_same]
    rw [wπ_of_mem W (pathMor_mem_wP W w)]
    split_ifs <;> simp
  · simp only [row, Pi.single_eq_of_ne hx, map_zero]
    split_ifs <;> simp [Pi.single_eq_of_ne hx]

/-- The rows of `S` of relative weight `χ`. -/
def rowsOf (S : RowSet Q) : RowSet Q := {R | R ∈ S ∧ W.pw R.2 = W.ν R.1 + χ}

theorem cokerProj_rowSpan (m : ℕ) (S : RowSet Q) :
    (rowSpan c m S).map (cokerProj W hfin χ m) ≤ rowSpan c m (rowsOf W χ S) := by
  rw [rowSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨R, ⟨hR, hl⟩, rfl⟩, rfl⟩
  change Submodule.Quotient.mk (mfProj W χ (row c R.1 R.2)) ∈ _
  rw [mfProj_row]
  split_ifs with h
  · exact rowClass_mem_rowSpan c ⟨hR, h⟩ hl
  · rw [Submodule.Quotient.mk_zero]; exact zero_mem _

variable [Fintype Q.nonprojective]

omit [Fintype V] in
theorem mk_mem_rowSpan {S : RowSet Q} (hS : CokerSpan c S) {m : ℕ} (hm : 2 ≤ m) (z : MeshFamily c)
    (hz : ∀ x, z x ∈ degreePart c (m + 1) (Q.tau x).1 x.1) :
    (Submodule.Quotient.mk z : Coker c m) ∈ rowSpan c m S := by
  have hsingle : ∀ x (e : obj c (Q.tau x).1 ⟶ obj c x.1),
      e ∈ degreePart c (m + 1) (Q.tau x).1 x.1 →
        (Submodule.Quotient.mk (Pi.single x e) : Coker c m) ∈ rowSpan c m S := by
    intro x e he
    rw [degreePart_eq_span] at he
    induction he using Submodule.span_induction with
    | mem e he =>
        obtain ⟨w, hw, rfl⟩ := he
        exact hS m hm x w hw
    | zero => rw [Pi.single_zero, Submodule.Quotient.mk_zero]; exact zero_mem _
    | add e₁ e₂ _ _ h₁ h₂ =>
        rw [Pi.single_add, Submodule.Quotient.mk_add]; exact add_mem h₁ h₂
    | smul t e _ he =>
        rw [Pi.single_smul, Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ t he
  rw [← Finset.univ_sum_single z, ← Submodule.mkQ_apply, map_sum]
  exact sum_mem fun x _ ↦ hsingle x (z x) (hz x)

include hfin in
/-- **A family of relative weight `χ` lies in the span of the rows of weight `χ`.** -/
theorem mem_rowSpan_char {S : RowSet Q} (hS : CokerSpan c S) {m : ℕ} (hm : 2 ≤ m)
    (z : MeshFamily c) (hz : ∀ x, z x ∈ degreePart c (m + 1) (Q.tau x).1 x.1)
    (hzw : ∀ x, z x ∈ wP c W (W.ν x + χ) (Q.tau x).1 x.1) :
    (Submodule.Quotient.mk z : Coker c m) ∈ rowSpan c m (rowsOf W χ S) := by
  have hfix : mfProj W χ z = z := by
    funext x; rw [mfProj_apply, wπ_of_mem W (hzw x), if_pos rfl]
  have h := mk_mem_rowSpan hS hm z hz
  refine cokerProj_rowSpan W hfin χ m S ⟨_, h, ?_⟩
  change Submodule.Quotient.mk (mfProj W χ z) = _
  rw [hfix]

/-! ### The class `Ψ` of a cocycle of character `χ` -/

variable {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {q : ℕ} {μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}

/-- **Proposition 7.6, weights** (`weights-and-parameters.tex`): the class `Ψ[μ]`
of a cocycle of character `χ` lies in the span of the spanning rows of relative weight
`χ`. -/
theorem Ψc_mem_rowSpan_char (J : D.InjData) (h1 : DegOne D)
    (hμχ : HasChar W hfin D χ μ) {S : RowSet Q}
    (hS : CokerSpan c S) (hq : 1 ≤ q) (Ld : LiftData D hfin q μ) :
    Ψc Ld ∈ rowSpan c (q + 1) (rowsOf W χ S) := by
  rw [Ψc_indep J h1 (wLiftData W χ hμχ Ld) Ld]
  exact mem_rowSpan_char W hfin χ hS (by omega) _ (fun x ↦ zhat_mem _ x)
    (fun x ↦ zhat_wLiftData hμχ Ld x)

end MeshWalk

end MultiplicativeBasisDeformations
