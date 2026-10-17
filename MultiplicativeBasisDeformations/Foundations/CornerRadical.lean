import MultiplicativeBasisDeformations.Foundations.EndpointChains
import MultiplicativeBasisDeformations.Foundations.BasicLabels

/-!
# The radical of a corner

For Lemma 2.1 (`graded-category.tex:49–51`): "The radical powers of `A` have
the same block description with `e_i (rad B₀)^n e_j` in each block." For an
idempotent `e` the radical of `eAe` is `e (rad A) e` (`cornerVal_mem_jacobson`,
`cornerMk_mem_jacobson`); when `AeA = A` the same holds for all radical powers
(`corner_mem_radPow`), by inserting `1 ∈ AeA` between the factors.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

/-- Elements of the radical of a Dedekind-finite ring are quasi-regular. -/
theorem isUnit_one_sub_of_mem_jacobson {R : Type*} [Ring R] [IsDedekindFiniteMonoid R] {x : R}
    (hx : x ∈ Ring.jacobson R) (y : R) : IsUnit (1 - y * x) := by
  rw [← Ideal.jacobson_bot] at hx
  obtain ⟨z, hz⟩ := (Ideal.mem_jacobson_iff).1 hx (-y)
  rw [Submodule.mem_bot] at hz
  have h1 : z * (1 - y * x) = 1 := by
    rw [mul_sub, mul_one, ← mul_assoc]
    rw [mul_neg, neg_mul] at hz
    calc z - z * y * x = (-(z * y * x) + z - 1) + 1 := by abel
      _ = 1 := by rw [hz, zero_add]
  exact ⟨⟨1 - y * x, z, mul_eq_one_comm.1 h1, h1⟩, rfl⟩

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
  {e : A} (he : IsIdempotentElem e)

variable (k A) in
include k in
theorem dedekindFinite : IsDedekindFiniteMonoid A := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  infer_instance

variable (k) in
/-- The value map of the corner, as a `k`-linear map. -/
def cornerValL : he.Corner →ₗ[k] A where
  toFun := cornerVal he
  map_add' := corner_add_val he
  map_smul' c x := corner_smul_val (k := k) he c x

theorem cornerValL_apply (x : he.Corner) : cornerValL k he x = cornerVal he x := rfl

variable (k) in
include k in
theorem cornerVal_mem_jacobson {x : he.Corner} (hx : x ∈ Ring.jacobson he.Corner) :
    cornerVal he x ∈ Ring.jacobson A := by
  haveI : FiniteDimensional k he.Corner := corner_finite he
  haveI := dedekindFinite k he.Corner
  apply mem_jacobson_of_forall_isUnit
  intro y
  set cx := cornerVal he x
  have hcx_l : e * cx = cx := corner_mul_left he x
  have hcx_r : cx * e = cx := corner_mul_right he x
  -- reduce to `1 - cx (e y e)`
  have hred : y * cx = (y * e) * cx := by rw [mul_assoc, hcx_l]
  rw [hred]
  apply isUnit_one_sub_mul_of_comm
  let z : he.Corner := cornerMk he (e * y * e) ⟨y, rfl⟩
  have hz : cx * (y * e) = cx * cornerVal he z := by
    change cx * (y * e) = cx * (e * y * e)
    conv_lhs => rw [← hcx_r]
    simp only [mul_assoc]
  rw [hz]
  -- `1 - x z` is a unit of the corner
  have hu : IsUnit (1 - x * z) :=
    isUnit_one_sub_mul_of_comm (isUnit_one_sub_of_mem_jacobson hx z)
  obtain ⟨w, hw⟩ := hu
  set W := cornerVal he (w⁻¹ : he.Cornerˣ).1
  have hval : cornerVal he (w : he.Corner) = e - cx * cornerVal he z := by
    rw [hw]
    change cornerValL k he (1 - x * z) = _
    rw [map_sub, cornerValL_apply, cornerValL_apply, corner_one_val, corner_mul_val]
  have hWl : e * W = W := corner_mul_left he _
  have hWr : W * e = W := corner_mul_right he _
  have h1 : (e - cx * cornerVal he z) * W = e := by
    rw [← hval, ← corner_mul_val, w.mul_inv, corner_one_val]
  have h2 : W * (e - cx * cornerVal he z) = e := by
    rw [← hval, ← corner_mul_val, w.inv_mul, corner_one_val]
  have hez : e * (cx * cornerVal he z) = cx * cornerVal he z := by rw [← mul_assoc, hcx_l]
  have hze : (cx * cornerVal he z) * e = cx * cornerVal he z := by
    rw [mul_assoc, corner_mul_right he z]
  refine ⟨⟨1 - cx * cornerVal he z, (1 - e) + W, ?_, ?_⟩, rfl⟩
  · calc (1 - cx * cornerVal he z) * ((1 - e) + W)
        = (1 - e) - cx * cornerVal he z + cx * cornerVal he z * e +
          (e - cx * cornerVal he z) * W + (1 - e) * W := by noncomm_ring
      _ = 1 := by rw [h1, hze, sub_mul, one_mul, hWl, sub_self, add_zero]; abel
  · calc ((1 - e) + W) * (1 - cx * cornerVal he z)
        = (1 - e) - cx * cornerVal he z + e * (cx * cornerVal he z) +
          W * (e - cx * cornerVal he z) + W * (1 - e) := by noncomm_ring
      _ = 1 := by rw [h2, hez, mul_sub, mul_one, hWr, sub_self, add_zero]; abel

variable (k) in
include k in
theorem cornerMk_mem_jacobson {z : A} (hz : z ∈ Ring.jacobson A)
    (hze : z ∈ Subsemigroup.corner e) : cornerMk he z hze ∈ Ring.jacobson he.Corner := by
  haveI := dedekindFinite k A
  apply mem_jacobson_of_forall_isUnit
  intro y
  set c := cornerVal he y * z
  have hzl : e * z = z := corner_mul_left he (cornerMk he z hze)
  have hzr : z * e = z := corner_mul_right he (cornerMk he z hze)
  have hcl : e * c = c := by rw [← mul_assoc, corner_mul_left he y]
  have hcr : c * e = c := by rw [mul_assoc, hzr]
  obtain ⟨w, hw⟩ := isUnit_one_sub_of_mem_jacobson hz (cornerVal he y)
  set W := (w⁻¹ : Aˣ).1
  have h1 : (1 - c) * W = 1 := by rw [← hw]; exact w.mul_inv
  have h2 : W * (1 - c) = 1 := by rw [← hw]; exact w.inv_mul
  have hcomm : e * W = W * e := by
    have h3 : (1 - c) * e = e * (1 - c) := by rw [sub_mul, mul_sub, hcl, hcr, one_mul, mul_one]
    calc e * W = W * (1 - c) * e * W := by rw [h2, one_mul]
      _ = W * (e * (1 - c)) * W := by rw [mul_assoc W, h3]
      _ = W * e := by rw [mul_assoc, mul_assoc, h1, mul_one]
  let V : he.Corner := cornerMk he (e * W * e) ⟨W, rfl⟩
  have hval : cornerVal he (1 - y * cornerMk he z hze) = e - c := by
    change cornerValL k he (1 - y * cornerMk he z hze) = _
    rw [map_sub, cornerValL_apply, cornerValL_apply, corner_one_val, corner_mul_val]
    rfl
  have heWe : e * W * e = W * e := by rw [hcomm, mul_assoc, he.eq]
  have hl : e - c = e * (1 - c) := by rw [mul_sub, mul_one, hcl]
  have hr : e * (e - c) = (1 - c) * e := by rw [mul_sub, he.eq, hcl, sub_mul, one_mul, hcr]
  refine ⟨⟨1 - y * cornerMk he z hze, V, ?_, ?_⟩, rfl⟩
  · apply corner_ext he
    rw [corner_mul_val, hval, corner_one_val]
    change (e - c) * (e * W * e) = e
    calc (e - c) * (e * W * e) = e * ((1 - c) * W) * e := by
          rw [heWe, hl]; simp only [mul_assoc]
      _ = e := by rw [h1, mul_one, he.eq]
  · apply corner_ext he
    rw [corner_mul_val, hval, corner_one_val]
    change (e * W * e) * (e - c) = e
    calc (e * W * e) * (e - c) = W * (e * (e - c)) := by rw [heWe, mul_assoc]
      _ = e := by rw [hr, ← mul_assoc, h2, one_mul]

variable (k) in
include k in
/-- `(rad eAe)^m ⊆ (rad A)^m`. -/
theorem cornerVal_mem_radPow {m : ℕ} (hm : 1 ≤ m) {x : he.Corner}
    (hx : x ∈ algebraRadicalPow k he.Corner m) : cornerVal he x ∈ algebraRadicalPow k A m := by
  haveI : FiniteDimensional k he.Corner := corner_finite he
  induction m, hm using Nat.le_induction generalizing x with
  | base =>
      rw [algebraRadicalPow, pow_one] at hx ⊢
      exact cornerVal_mem_jacobson k he hx
  | succ m hm ih =>
      rw [algebraRadicalPow, pow_succ] at hx ⊢
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
      · rw [corner_mul_val]
        exact Submodule.mul_mem_mul (ih ha) (cornerVal_mem_jacobson k he hb)
      · rw [show cornerVal he (a + b) = cornerVal he a + cornerVal he b from corner_add_val he a b]
        exact Submodule.add_mem _ ha hb

variable (k) in
include k in
/-- **`e (rad A)^m e ⊆ (rad eAe)^m` when `AeA = A`**: insert `1 ∈ AeA` between
the factors. -/
theorem corner_mem_radPow
    (hfull : (1 : A) ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    {m : ℕ} (hm : 1 ≤ m) {z : A} (hz : z ∈ algebraRadicalPow k A m) (p' q' : A) :
    e * p' * z * q' * e ∈ (algebraRadicalPow k he.Corner m).map (cornerValL k he) := by
  haveI : FiniteDimensional k he.Corner := corner_finite he
  have hJ : (Ring.jacobson A).IsTwoSided := inferInstance
  have hbase : ∀ {z : A}, z ∈ Ring.jacobson A → ∀ p' q' : A,
      e * p' * z * q' * e ∈ (algebraRadicalPow k he.Corner 1).map (cornerValL k he) := by
    intro z hz p' q'
    have hw : e * p' * z * q' * e ∈ Ring.jacobson A :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hz))
    have hc : e * p' * z * q' * e ∈ Subsemigroup.corner e := ⟨p' * z * q', by simp only [mul_assoc]⟩
    refine ⟨cornerMk he _ hc, ?_, rfl⟩
    rw [algebraRadicalPow, pow_one]
    exact cornerMk_mem_jacobson k he hw hc
  induction m, hm using Nat.le_induction generalizing z p' q' with
  | base =>
      rw [algebraRadicalPow, pow_one] at hz
      exact hbase hz p' q'
  | succ m hm ih =>
      rw [algebraRadicalPow, pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
      · -- insert `1 = Σ p e q` between `a` and `b`
        have key : ∀ w ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q},
            e * p' * (a * w * b) * q' * e ∈
              (algebraRadicalPow k he.Corner (m + 1)).map (cornerValL k he) := by
          intro w hw
          induction hw using Submodule.span_induction with
          | mem w hw =>
              obtain ⟨p, q, rfl⟩ := hw
              have h1 := ih ha p' p
              have h2 := hbase hb q q'
              obtain ⟨x1, hx1, hx1v⟩ := h1
              obtain ⟨x2, hx2, hx2v⟩ := h2
              refine ⟨x1 * x2, ?_, ?_⟩
              · rw [algebraRadicalPow, pow_succ]
                rw [algebraRadicalPow, pow_one] at hx2
                exact Submodule.mul_mem_mul hx1 hx2
              · rw [cornerValL_apply, corner_mul_val, ← cornerValL_apply (k := k),
                  ← cornerValL_apply (k := k), hx1v, hx2v]
                calc e * p' * a * p * e * (e * q * b * q' * e) =
                    e * p' * a * p * (e * e) * q * b * q' * e := by simp only [mul_assoc]
                  _ = e * p' * (a * (p * e * q) * b) * q' * e := by rw [he.eq]; simp only [mul_assoc]
          | zero => simp
          | add w w' _ _ hw hw' =>
              have : e * p' * (a * (w + w') * b) * q' * e =
                  e * p' * (a * w * b) * q' * e + e * p' * (a * w' * b) * q' * e := by noncomm_ring
              rw [this]; exact Submodule.add_mem _ hw hw'
          | smul c w _ hw =>
              have : e * p' * (a * (c • w) * b) * q' * e = c • (e * p' * (a * w * b) * q' * e) := by
                simp only [mul_smul_comm, smul_mul_assoc]
              rw [this]; exact Submodule.smul_mem _ c hw
        have := key 1 hfull
        rwa [mul_one] at this
      · have : e * p' * (a + b) * q' * e = e * p' * a * q' * e + e * p' * b * q' * e := by
          noncomm_ring
        rw [this]; exact Submodule.add_mem _ ha hb

end MultiplicativeBasisDeformations
