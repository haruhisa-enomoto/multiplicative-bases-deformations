import MultiplicativeBasisDeformations.Foundations.BaseChange
import MultiplicativeBasisDeformations.Foundations.RowSpan
import MultiplicativeBasisDeformations.Foundations.ARPrime
import MultiplicativeBasisDeformations.Foundations.ResidualCorrection
import MultiplicativeBasisDeformations.Foundations.ARBrick

/-!
# The spanning rows of `C⁽²⁾` (Lemma B.2 over `𝔽₂`)

`lem:integral-mesh-cokernels` is applied in Section 10 to the prime-field model `C⁽²⁾`. The
rows of Proposition 6.1 span the derivative cokernels of `k(Γ_A)` (`residual_cokerSpan`); the
spanning property passes to the all-one presentation over `k` by the gauge of Lemma 4.4
(`cokerSpan_gauge`), and from there to `𝔽₂` by a coefficient retraction `k → 𝔽₂`
(`cokerSpan_descend`): applying the retraction to a relation
`row = ∑ αᵢ rowᵢ + D f` over `k` gives `row = ∑ θ(αᵢ) rowᵢ + D(θ f)` over `𝔽₂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

open LinearPaths

variable {K : Type} [Field K] {k : Type u} [Field k] [Algebra K k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {u : MeshCoefficients K Q} {c : MeshCoefficients k Q}
  (hred : ∀ x y a, algebraMap K k (u x y a : K) = (c x y a : k)) (θ : k →ₗ[K] K)

include hred in
theorem retE_degreePart {X Y : V} {n : ℕ} {φ : obj c X ⟶ obj c Y} (hφ : φ ∈ degreePart c n X Y) :
    retE u θ φ ∈ degreePart u n X Y := by
  suffices ∀ t : k, retE u θ (t • φ) ∈ degreePart u n X Y by
    have := this 1; rwa [one_smul] at this
  rw [degreePart_eq_span] at hφ
  induction hφ using Submodule.span_induction with
  | mem e he =>
      obtain ⟨p, hp, rfl⟩ := he
      intro t
      rw [← redE_pathMor hred (u := u) p, retE_smul_redE hred]
      exact Submodule.smul_mem _ _ (hp ▸ pathMor_mem_degreePart u p)
  | zero => intro t; rw [smul_zero, retE_zero hred]; exact zero_mem _
  | add e e' _ _ he he' => intro t; rw [smul_add, retE_add hred]; exact add_mem (he t) (he' t)
  | smul s e _ he => intro t; rw [smul_smul]; exact he _

variable [DecidableEq V]

include hred in
theorem retE_meshDerivative (f : ArrowFamily c) (x : Q.nonprojective) :
    retE u θ (meshDerivative c f x) = meshDerivative u (fun a ↦ retE u θ (f a)) x := by
  simp only [meshDerivative]
  rw [retE_sum hred]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← hred, retE_algSmul hred, retE_add hred, ← redE_arrowMor hred (u := u),
    ← redE_arrowMor hred (u := u) (Q.mate x a.1 a.2), retE_comp_redE hred, retE_redE_comp hred]

include hred in
theorem retE_row (h1 : θ 1 = 1) (t : k) (x x' : Q.nonprojective)
    (w : Quiver.Path (Q.tau x).1 x.1) : retE u θ (t • row c x w x') = θ t • row u x w x' := by
  simp only [row]
  by_cases h : x' = x
  · subst h; rw [Pi.single_eq_same, Pi.single_eq_same, ← redE_pathMor hred (u := u),
      retE_smul_redE hred]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero, retE_zero hred, smul_zero]

variable [Fintype Q.nonprojective]

include hred in
/-- **Spanning rows descend along a field extension.** -/
theorem cokerSpan_descend (h1 : θ 1 = 1) {S : RowSet Q} (hS : CokerSpan c S) : CokerSpan u S := by
  classical
  intro m hm x w hw
  obtain ⟨n, f, g', hfg⟩ := (Submodule.mem_span_set' (R := k)).1 (hS m hm x w hw)
  choose R hR hgR using fun i ↦ (g' i).2
  have hrow : row c x w - ∑ i, f i • row c (R i).1 (R i).2 ∈ imageD c m := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change rowClass c m x w - _ = 0
    rw [← hfg, sub_eq_zero]
    change _ = (imageD c m).mkQ (∑ i, f i • row c (R i).1 (R i).2)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ← hgR i]; rfl
  obtain ⟨fk, hfk, hDfk⟩ := hrow
  -- retract the relation
  have key : row u x w - ∑ i, θ (f i) • row u (R i).1 (R i).2 =
      meshDerivative u (fun a ↦ retE u θ (fk a)) := by
    funext x'
    rw [← retE_meshDerivative hred θ fk x']
    have e := congrFun hDfk x'
    rw [meshDerivativeₗ_apply] at e
    rw [e, Pi.sub_apply, Pi.sub_apply, retE_sub hred, Finset.sum_apply, Finset.sum_apply,
      retE_sum hred]
    congr 1
    · have := retE_row hred θ h1 1 x x' w
      rw [one_smul, h1, one_smul] at this
      exact this.symm
    · exact Finset.sum_congr rfl fun i _ ↦ (retE_row hred θ h1 (f i) _ x' _).symm
  have hmem : row u x w - ∑ i, θ (f i) • row u (R i).1 (R i).2 ∈ imageD u m :=
    ⟨_, fun a ↦ retE_degreePart hred θ (hfk a), key.symm⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero] at hmem
  change rowClass u m x w = (imageD u m).mkQ _ at hmem
  rw [hmem, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (rowClass_mem_rowSpan u (hR i).1 (hR i).2)

end ScalarMeshCategory

namespace IndSkeleton

open ScalarMeshCategory

attribute [local instance] ZMod.algebra

variable {k A : Type u} [Field k] [IsAlgClosed k] [CharP k 2] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

include b in
/-- **The rows of Proposition 6.1 span the derivative cokernels of `C⁽²⁾`, and are killed by
two over every coefficient ring.** -/
theorem prime_cokerSpan : ∃ R : RowSet S.arTranslationQuiver,
    CokerSpan (S.oneC (ZMod 2)) R ∧ TwoRows.{0} S.arTranslationQuiver R := by
  classical
  obtain ⟨R, -, -, hspan, htwo⟩ := residual_cokerSpan (S.arCoefficients b) S.hasAtMostOneArrow
    CharTwo.two_eq_zero (S.finiteDimensional_meshHom b) (S.brickHypothesis b)
  refine ⟨R, ?_, htwo⟩
  have hK : CokerSpan S.oneK R := by
    refine cokerSpan_gauge (S.arCoefficients b) (fun a ↦ (S.arMu b a)⁻¹) (S.arEta b)⁻¹ S.oneK
      (fun x y a ↦ ?_) hspan
    rw [S.arGauge b x y a]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, mul_one, Pi.inv_apply]
    field_simp
  obtain ⟨θ, h1⟩ := exists_retraction (K := ZMod 2) (k := k)
  exact cokerSpan_descend S.hredOne θ h1 hK

end IndSkeleton

end MultiplicativeBasisDeformations
