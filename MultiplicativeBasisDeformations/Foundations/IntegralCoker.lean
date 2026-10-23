module

public import MultiplicativeBasisDeformations.Foundations.ReductionMesh
public import MultiplicativeBasisDeformations.Foundations.ResidualCorrection
public import MultiplicativeBasisDeformations.Foundations.ZModFour

/-!
# Lemma B.2: the derivative cokernels over `ℤ/4` are killed by two

`lem:integral-mesh-cokernels` (`characteristic-two-mesh-calculations.tex`): "Each
retained derivative cokernel is thus killed by two. … All other degree and weight components
vanish by their zero reduction."

With `𝒪 = ℤ/4` and unit coefficients `ũ` reducing to the coefficients `c` of a scalar mesh
category over `𝔽₂`: given rows spanning the cokernels over `𝔽₂` (`CokerSpan`; for `C⁽²⁾`
these are `IndSkeleton.prime_cokerSpan`) which are killed by two over every coefficient ring
(`TwoRows`, from the trace calculations), and since reduction is right exact
(`ReductionMesh`), every family of degree `m + 1 ≥ 3` is, up to `2·(families)`, an
`𝒪`-combination of these rows plus a derivative, so twice it is a derivative
(`two_smul_mem_imageD`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

open LinearPaths

section Kernel

variable {V : Type v} [Quiver.{w} V]

/-- Division by two on `2𝒪`. -/
def half (a : ZMod 4) : ZMod 4 := (a.val / 2 : ℕ)

theorem half_zero : half 0 = 0 := by decide

theorem two_mul_half {a : ZMod 4} (h : Z4.red a = 0) : 2 * half a = a := by
  revert a; decide

/-- **The kernel of the reduction of path combinations is `2·(path combinations)`.** -/
theorem eq_two_smul_of_redP {x y : V} {Φ : LinearPaths.obj (k := ZMod 4) x ⟶ LinearPaths.obj y}
    (h : redP Z4.red Φ = 0) : ∃ H, Φ = (2 : ZMod 4) • H := by
  refine ⟨ofFinsupp (Finsupp.mapRange half half_zero (toFinsupp Φ)), ?_⟩
  have h' : ∀ p, Z4.red (toFinsupp Φ p) = 0 := fun p ↦ by
    have := congrArg (fun f ↦ toFinsupp f p) h
    change (Finsupp.mapRange Z4.red (map_zero Z4.red) (toFinsupp Φ)) p = 0 at this
    rwa [Finsupp.mapRange_apply] at this
  change toFinsupp Φ = (2 : ZMod 4) • Finsupp.mapRange half half_zero (toFinsupp Φ)
  refine Finsupp.ext fun p ↦ ?_
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact (two_mul_half (h' p)).symm

end Kernel

variable {V : Type v} [Quiver.{w} V]
  [Fintype V] [DecidableEq V] [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {Q : TranslationQuiver V} [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]
  {c : MeshCoefficients 𝔽₂ Q} {u : MeshCoefficients (ZMod 4) Q}
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

include hred in
theorem eq_two_smul_of_redE {X Y : V} {φ : obj u X ⟶ obj u Y}
    (h : redE Z4.red u c φ = 0) : ∃ ψ, φ = (2 : ZMod 4) • ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := ZMod 4) _ φ
  rw [redE_map hred, RelationCategory.functor_map_eq_zero_iff] at h
  obtain ⟨I, hI, hIΦ⟩ := exists_lift_ideal hred Z4.red_surjective h
  obtain ⟨H, hH⟩ := eq_two_smul_of_redP (Φ := Φ - I) (by rw [map_sub, hIΦ, sub_self])
  refine ⟨(RelationCategory.functor (ZMod 4) (meshRelations u)).map H, ?_⟩
  have hI0 : (RelationCategory.functor (ZMod 4) (meshRelations u)).map I = 0 :=
    (RelationCategory.functor_map_eq_zero_iff _ _).2 hI
  rw [← Functor.map_smul, ← hH, Functor.map_sub, hI0, sub_zero]

/-- **A family of degree `m + 1` has class in the span of rows spanning the cokernels.** -/
theorem mk_mem_rowSpan {S : RowSet Q} (hS : CokerSpan c S) {m : ℕ} (hm : 2 ≤ m)
    {g : MeshFamily c} (hg : ∀ x, g x ∈ degreePart c (m + 1) (Q.tau x).1 x.1) :
    Submodule.Quotient.mk g ∈ rowSpan c m S := by
  classical
  rw [← Finset.univ_sum_single g]
  change (imageD c m).mkQ (∑ x, Pi.single x (g x)) ∈ _
  rw [map_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  change Submodule.Quotient.mk _ ∈ _
  suffices key : ∀ e ∈ degreePart c (m + 1) (Q.tau x).1 x.1,
      Submodule.Quotient.mk (p := imageD c m) (Pi.single x e) ∈ rowSpan c m S from key _ (hg x)
  intro e hx
  rw [degreePart_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem e he =>
      obtain ⟨w, hw, rfl⟩ := he
      exact hS m hm x w hw
  | zero => rw [Pi.single_zero, Submodule.Quotient.mk_zero]; exact zero_mem _
  | add e e' _ _ he he' =>
      rw [Pi.single_add, Submodule.Quotient.mk_add]; exact add_mem he he'
  | smul a e _ he => rw [Pi.single_smul, Submodule.Quotient.mk_smul]; exact Submodule.smul_mem _ a he

include hred in
/-- **Lemma B.2** (`lem:integral-mesh-cokernels`): over `ℤ/4`, twice every family of mesh
corrections of degree `m + 1 ≥ 3` is a derivative. -/
theorem two_smul_mem_imageD {S : RowSet Q} (hspan : CokerSpan c S) (htwo : TwoRows.{0} Q S)
    {m : ℕ} (hm : 2 ≤ m) {g : MeshFamily u}
    (hg : ∀ x, g x ∈ degreePart u (m + 1) (Q.tau x).1 x.1) : (2 : ZMod 4) • g ∈ imageD u m := by
  classical
  -- the reduction of `g` is a combination of rows and a derivative
  have hgk : ∀ x, redF Z4.red u c g x ∈ degreePart c (m + 1) (Q.tau x).1 x.1 :=
    fun x ↦ redE_degreePart hred (hg x)
  have hmem := mk_mem_rowSpan hspan hm hgk
  obtain ⟨n, f, g', hfg⟩ := (Submodule.mem_span_set' (R := 𝔽₂)).1 hmem
  choose R hR hgR using fun i ↦ (g' i).2
  have hrow : redF Z4.red u c g - ∑ i, f i • row c (R i).1 (R i).2 ∈ imageD c m := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hfg, sub_eq_zero]
    change _ = (imageD c m).mkQ (∑ i, f i • row c (R i).1 (R i).2)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ← hgR i]; rfl
  obtain ⟨fk, hfk, hDfk⟩ := hrow
  choose fO hfO hfOk using fun a ↦ exists_lift_degreePart hred Z4.red_surjective (hfk a)
  -- the remainder reduces to zero
  set r : MeshFamily u := g - ∑ i, Z4.lift (f i) • row u (R i).1 (R i).2 - meshDerivative u fO
  have hr : ∀ x, redE Z4.red u c (r x) = 0 := by
    intro x
    have e : redF Z4.red u c r = 0 := by
      simp only [r]
      rw [redF_sub hred, redF_sub hred, redF_sum hred, redF_meshDerivative hred]
      have ha : redA Z4.red u c fO = fk := funext fun a ↦ hfOk a
      rw [ha, ← meshDerivativeₗ_apply, hDfk]
      simp only [redF_smul hred, redF_row hred, Z4.red_lift]
      abel
    exact congrFun e x
  choose ψ hψ using fun x ↦ eq_two_smul_of_redE hred (hr x)
  have hr2 : r = (2 : ZMod 4) • ψ := funext fun x ↦ hψ x
  -- twice `g`
  have hg2 : (2 : ZMod 4) • g = ∑ i, Z4.lift (f i) • ((2 : ZMod 4) • row u (R i).1 (R i).2) +
      meshDerivative u ((2 : ZMod 4) • fO) + ((2 : ZMod 4) * 2) • ψ := by
    have e : g = ∑ i, Z4.lift (f i) • row u (R i).1 (R i).2 + meshDerivative u fO + r := by
      simp only [r]; abel
    rw [← meshDerivativeₗ_apply, map_smul, meshDerivativeₗ_apply, mul_smul, ← hr2]
    conv_lhs => rw [e]
    rw [smul_add, smul_add, Finset.smul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_comm]
  rw [hg2, Z4.four_eq_zero, zero_smul, add_zero]
  refine add_mem (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_)
    ⟨_, Submodule.smul_mem _ _ (fun a ↦ hfO a), rfl⟩
  have h2 := htwo (ZMod 4) u m hm (R i) (hR i).1 (hR i).2
  rw [rowClass, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end ScalarMeshCategory

end MultiplicativeBasisDeformations
