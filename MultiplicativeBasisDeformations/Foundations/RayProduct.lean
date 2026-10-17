import MultiplicativeBasisDeformations.Foundations.RayBasis

/-!
# Ray products

Lemma 3.6 (`projective-rays.tex`): "Every unit of `R_y` is a nonzero
scalar times `1 + n` with `n ∈ rad R_y`. Thus changing representatives replaces
their product, up to a nonzero scalar and endpoint units, by `fh + fnh`. The
subbimodule `M(f,h)` is unchanged. If `fh ∉ M(f,h)`, the chain property forces
`M(f,h) ⊊ U(fh)` […] so `M(f,h) ⊆ R(fh)`. Thus the changed product remains in
`U(fh) ∖ R(fh)`, is nonzero and has ray `[fh]`. If `fh ∈ M(f,h)`, the changed
product is still in `M(f,h)`."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)

/-- `e_y ∉ rad A`. -/
theorem e_not_mem_radical (y : Fin F.m) : F.e y ∉ algebraRadical k A := by
  intro hy
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := A)
  have hK0 : F.e y ^ K = 0 := by
    have := Submodule.pow_mem_pow _ hy K
    rwa [hK, Submodule.mem_bot] at this
  apply (F.primitive y).2.1
  rw [← (F.complete.idem y).pow_succ_eq K, pow_succ, hK0, zero_mul]

/-- **A unit of `R_y` is `c e_y + n`, `c ≠ 0`, `n ∈ rad R_y`.** -/
theorem exists_unit_decomp {y : Fin F.m} {v : A} (hv : F.IsCornerUnit (k := k) y v) :
    ∃ c : k, c ≠ 0 ∧ v - c • F.e y ∈ F.cornerRadical (k := k) y := by
  obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_cornerRadical y hv.1
  refine ⟨c, fun h0 ↦ ?_, hc⟩
  rw [h0, zero_smul, sub_zero] at hc
  obtain ⟨-, v', hv', h1, -⟩ := hv
  apply F.e_not_mem_radical (k := k) y
  rw [← h1]
  exact (F.radR_mem hv' hc).2

theorem insertionSpan_isEndpoint {x y z : Fin F.m} {f h : A} (hf : f ∈ F.corner (k := k) x y)
    (hh : h ∈ F.corner (k := k) y z) :
    F.IsEndpointSubbimodule x z (F.insertionSpan (k := k) x y z f h) := by
  refine ⟨Submodule.span_le.2 ?_, fun a' ha' n hn ↦ ?_, fun b' hb' n hn ↦ ?_⟩
  · rintro _ ⟨a, ha, r, hr, b, hb, rfl⟩
    exact F.corner_mul_corner (F.corner_mul_corner (F.corner_mul_corner
      (F.corner_mul_corner ha hf) hr.1) hh) hb
  · induction hn using Submodule.span_induction with
    | mem n hn =>
        obtain ⟨a, ha, r, hr, b, hb, rfl⟩ := hn
        exact Submodule.subset_span ⟨a' * a, F.corner_mul_corner ha' ha, r, hr, b, hb, by
          simp only [mul_assoc]⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add n n' _ _ hn hn' => rw [mul_add]; exact Submodule.add_mem _ hn hn'
    | smul c n _ hn => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hn
  · induction hn using Submodule.span_induction with
    | mem n hn =>
        obtain ⟨a, ha, r, hr, b, hb, rfl⟩ := hn
        exact Submodule.subset_span ⟨a, ha, r, hr, b * b', F.corner_mul_corner hb hb', by
          simp only [mul_assoc]⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add n n' _ _ hn hn' => rw [add_mul]; exact Submodule.add_mem _ hn hn'
    | smul c n _ hn => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hn

theorem insertionSpan_le_of_mem_ray {x y z : Fin F.m} {f h f' h' : A}
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    F.insertionSpan (k := k) x y z f' h' ≤ F.insertionSpan (k := k) x y z f h := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hf'
  obtain ⟨u₂, w₂, hu₂, hw₂, rfl⟩ := hh'
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, r, hr, b, hb, rfl⟩
  refine Submodule.subset_span ⟨a * u, F.corner_mul_corner ha hu.1, w * r * u₂,
    F.radR_mem hu₂.1 (F.radL_mem hw.1 hr), w₂ * b, F.corner_mul_corner hw₂.1 hb, ?_⟩
  simp only [mul_assoc]

theorem insertionSpan_eq_of_mem_ray {x y z : Fin F.m} {f h f' h' : A}
    (hf : f ∈ F.corner (k := k) x y) (hh : h ∈ F.corner (k := k) y z)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    F.insertionSpan (k := k) x y z f' h' = F.insertionSpan (k := k) x y z f h := by
  refine le_antisymm (F.insertionSpan_le_of_mem_ray hf' hh') (F.insertionSpan_le_of_mem_ray ?_ ?_)
  · rw [F.ray_eq_of_mem hf hf']; exact F.mem_ray_self hf
  · rw [F.ray_eq_of_mem hh hh']; exact F.mem_ray_self hh

/-- **Changing representatives**: `f'h' = u (c fh + f n h) w` with units `u`, `w`,
`c ≠ 0` and `n ∈ rad R_y`. -/
theorem exists_product_decomp {x y z : Fin F.m} {f h f' h' : A}
    (hf : f ∈ F.corner (k := k) x y)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    ∃ (u w : A) (c : k) (n : A), F.IsCornerUnit (k := k) x u ∧ F.IsCornerUnit (k := k) z w ∧ c ≠ 0 ∧
      n ∈ F.cornerRadical (k := k) y ∧ f' * h' = u * (c • (f * h) + f * n * h) * w := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hf'
  obtain ⟨u₂, w₂, hu₂, hw₂, rfl⟩ := hh'
  obtain ⟨c, hc, hn⟩ := F.exists_unit_decomp (F.cornerUnit_mul hw hu₂)
  generalize hN : w * u₂ - c • F.e y = N at hn
  refine ⟨u, w₂, c, N, hu, hw₂, hc, hn, ?_⟩
  have hv : w * u₂ = c • F.e y + N := by rw [← hN]; abel
  calc u * f * w * (u₂ * h * w₂) = u * (f * (w * u₂) * h) * w₂ := by simp only [mul_assoc]
    _ = _ := by
        rw [hv, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, F.mul_e_of_mem hf]

theorem mul_mem_insertionSpan {x y z : Fin F.m} {f h n : A} (hf : f ∈ F.corner (k := k) x y)
    (hh : h ∈ F.corner (k := k) y z) (hn : n ∈ F.cornerRadical (k := k) y) :
    f * n * h ∈ F.insertionSpan (k := k) x y z f h :=
  Submodule.subset_span ⟨F.e x, F.e_mem_corner x, n, hn, F.e z, F.e_mem_corner z, by
    rw [F.e_mul_of_mem hf, F.mul_e_of_mem (F.corner_mul_corner (F.corner_mul_corner hf hn.1) hh)]⟩

theorem mem_insertionSpan_of_mem_ray {x y z : Fin F.m} {f h f' h' : A}
    (hf : f ∈ F.corner (k := k) x y) (hh : h ∈ F.corner (k := k) y z)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h)
    (hM : f * h ∈ F.insertionSpan (k := k) x y z f h) :
    f' * h' ∈ F.insertionSpan (k := k) x y z f' h' := by
  rw [F.insertionSpan_eq_of_mem_ray hf hh hf' hh']
  obtain ⟨u, w, c, n, hu, hw, -, hn, heq⟩ := F.exists_product_decomp hf hf' hh'
  have hE := F.insertionSpan_isEndpoint hf hh
  rw [heq]
  exact hE.2.2 w hw.1 _ (hE.2.1 u hu.1 _ (Submodule.add_mem _ (Submodule.smul_mem _ c hM)
    (F.mul_mem_insertionSpan hf hh hn)))

/-- **Lemma 3.6.** -/
theorem rayProduct_independent_of (hA : IsRepresentationFinite k A) {x y z : Fin F.m}
    {f f' h h' : A} (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0)
    (hh : h ∈ F.corner (k := k) y z) (hh0 : h ≠ 0)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    (f * h ∈ F.insertionSpan (k := k) x y z f h ↔
        f' * h' ∈ F.insertionSpan (k := k) x y z f' h') ∧
      (f * h ∉ F.insertionSpan (k := k) x y z f h →
        f' * h' ≠ 0 ∧ F.ray (k := k) x z (f * h) = F.ray (k := k) x z (f' * h')) := by
  have hfc' := F.ray_subset_corner hf hf'
  have hhc' := F.ray_subset_corner hh hh'
  have hf'f : f ∈ F.ray (k := k) x y f' := by rw [F.ray_eq_of_mem hf hf']; exact F.mem_ray_self hf
  have hh'h : h ∈ F.ray (k := k) y z h' := by rw [F.ray_eq_of_mem hh hh']; exact F.mem_ray_self hh
  refine ⟨⟨F.mem_insertionSpan_of_mem_ray hf hh hf' hh',
    F.mem_insertionSpan_of_mem_ray hfc' hhc' hf'f hh'h⟩, fun hM ↦ ?_⟩
  have hfh := F.corner_mul_corner hf hh
  have hfh0 : f * h ≠ 0 := fun h0 ↦ hM (h0 ▸ Submodule.zero_mem _)
  have hE := F.insertionSpan_isEndpoint hf hh
  have hU := F.isEndpoint_endpointSpan hfh
  -- `M(f, h) ⊊ U(fh)`, hence `M(f, h) ⊆ R(fh)`
  have hMU : F.insertionSpan (k := k) x y z f h ≤ F.endpointSpan (k := k) x z (f * h) := by
    rcases (F.isChain_subbimodules hA x z).total hE hU with h | h
    · exact h
    · exact absurd (h (F.mem_endpointSpan_self hfh)) hM
  have hMR := F.le_endpointRadical hA hfh hE hMU hM
  obtain ⟨u, w, c, n, hu, hw, hc, hn, heq⟩ := F.exists_product_decomp hf hf' hh'
  have hfnh := hMR (F.mul_mem_insertionSpan hf hh hn)
  have hmem : f' * h' ∈ F.ray (k := k) x z (f * h) := by
    refine (F.mem_ray_iff hA hfh hfh0 _).2 ⟨?_, fun hR ↦ ?_⟩
    · rw [heq]
      exact hU.2.2 w hw.1 _ (hU.2.1 u hu.1 _ (Submodule.add_mem _
        (Submodule.smul_mem _ c (F.mem_endpointSpan_self hfh))
        (by rw [F.endpointSpan_eq hfh]; exact Submodule.mem_sup_right hfnh)))
    · obtain ⟨u', hu', h1, h2⟩ := F.cornerUnit_inv hu
      obtain ⟨w', hw', h3, h4⟩ := F.cornerUnit_inv hw
      have hR' := F.isEndpoint_endpointRadical hfh
      have hin : c • (f * h) + f * n * h ∈ F.endpointRadical (k := k) x z (f * h) := by
        have := hR'.2.2 w' hw'.1 _ (hR'.2.1 u' hu'.1 _ hR)
        have hc' : c • (f * h) + f * n * h ∈ F.corner (k := k) x z :=
          Submodule.add_mem _ (Submodule.smul_mem _ c hfh)
            (F.corner_mul_corner (F.corner_mul_corner hf hn.1) hh)
        rwa [heq, show u' * (u * (c • (f * h) + f * n * h) * w) * w' =
            (u' * u) * (c • (f * h) + f * n * h) * (w * w') by simp only [mul_assoc],
          h2, h3, F.e_mul_of_mem hc', F.mul_e_of_mem hc'] at this
      have hcfh : c • (f * h) ∈ F.endpointRadical (k := k) x z (f * h) := by
        have := Submodule.sub_mem _ hin hfnh
        rwa [add_sub_cancel_right] at this
      apply F.not_mem_endpointRadical hfh hfh0
      have := Submodule.smul_mem _ c⁻¹ hcfh
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  exact ⟨F.ne_zero_of_mem_ray hfh hfh0 hmem, (F.ray_eq_of_mem hfh hmem).symm⟩

open Classical in
/-- **Definition 3.4, the ray product**: `[f][h] = [fh]` if `fh ∉ M(f, h)`, and the zero ray
`{0}` otherwise. -/
def rayProduct (x y z : Fin F.m) (f h : A) : Set A :=
  if f * h ∈ F.insertionSpan (k := k) x y z f h then {0} else F.ray (k := k) x z (f * h)

/-- **Lemma 3.6, first part**: the ray product does not depend on the representatives. -/
theorem rayProduct_eq_of_mem (hA : IsRepresentationFinite k A) {x y z : Fin F.m}
    {f f' h h' : A} (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0)
    (hh : h ∈ F.corner (k := k) y z) (hh0 : h ≠ 0)
    (hf' : f' ∈ F.ray (k := k) x y f) (hh' : h' ∈ F.ray (k := k) y z h) :
    F.rayProduct (k := k) x y z f h = F.rayProduct (k := k) x y z f' h' := by
  classical
  obtain ⟨h1, h2⟩ := F.rayProduct_independent_of hA hf hf0 hh hh0 hf' hh'
  unfold rayProduct
  by_cases hm : f * h ∈ F.insertionSpan (k := k) x y z f h
  · rw [if_pos hm, if_pos (h1.1 hm)]
  · rw [if_neg hm, if_neg (fun h'' ↦ hm (h1.2 h'')), (h2 hm).2]

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
