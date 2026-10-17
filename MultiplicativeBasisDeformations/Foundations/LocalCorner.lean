import MultiplicativeBasisDeformations.Foundations.GradedLayers

/-!
# Local corners are truncated polynomial algebras

Lemma 3.1(2) (`projective-rays.tex:45–52`): "Every subspace of `rad C/(rad C)²`
lifts to an ideal, so this space has dimension at most one […]. A lift `t` of a
generator generates successive radical powers, by Nakayama's lemma. Nilpotence
then writes every element as a polynomial in `t`, giving `C ≅ k[t]/(t^N)`."

Here the ideals of `C = R_x` are the endpoint subbimodules of `A(x, x)`, which
form a chain (Lemma 3.1(3), `isChain_subbimodules`); this gives
`rad C = k t + (rad C)²` (`exists_rad_gen`). Nakayama's lemma for subbimodules
gives `rad C ⊆ C t C`, and Lemma 3.1(3) makes `C t C` one-sided, `C t` or
`t C`; so every element is a polynomial in `t` (`aeval_surjective`). The kernel of
`k[X] → C` is `(X^N)` with `N` the nilpotency index of `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial

namespace MultiplicativeBasisDeformations

universe u v

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type v} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)

theorem cornerRadical_mul_le (x : Fin F.m) :
    F.cornerRadical (k := k) x * F.cornerRadical (k := k) x ≤ F.cornerRadical (k := k) x :=
  Submodule.mul_le.2 fun r hr s hs ↦
    ⟨F.corner_mul_corner hr.1 hs.1, (Ring.jacobson A).mul_mem_left r hs.2⟩

theorem e_mul_of_mem {x y : Fin F.m} {a : A} (ha : a ∈ F.corner (k := k) x y) : F.e x * a = a := by
  rw [← (F.mem_corner_iff').1 ha, ← mul_assoc, ← mul_assoc, (F.complete.idem x).eq]

theorem mul_e_of_mem {x y : Fin F.m} {a : A} (ha : a ∈ F.corner (k := k) x y) : a * F.e y = a := by
  rw [← (F.mem_corner_iff').1 ha, mul_assoc, (F.complete.idem y).eq]

/-- `a - c e_x ∈ rad R_x` for some scalar `c`. -/
theorem exists_sub_smul_mem_cornerRadical (x : Fin F.m) {a : A} (ha : a ∈ F.corner (k := k) x x) :
    ∃ c : k, a - c • F.e x ∈ F.cornerRadical (k := k) x := by
  obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k x ha
  exact ⟨c, Submodule.sub_mem _ ha (Submodule.smul_mem _ c (F.e_mem_corner x)), hc⟩

/-- Subspaces between `(rad R_x)²` and `rad R_x` are ideals of `R_x`. -/
theorem isEndpoint_of_between (x : Fin F.m) {V : Submodule k A}
    (h1 : F.cornerRadical (k := k) x * F.cornerRadical (k := k) x ≤ V)
    (h2 : V ≤ F.cornerRadical (k := k) x) : F.IsEndpointSubbimodule x x V := by
  refine ⟨h2.trans (F.cornerRadical_le_corner x), fun a ha v hv ↦ ?_, fun a ha v hv ↦ ?_⟩
  · obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_cornerRadical x ha
    have : a * v = c • v + (a - c • F.e x) * v := by
      rw [sub_mul, smul_mul_assoc, F.e_mul_of_mem (F.cornerRadical_le_corner x (h2 hv))]; abel
    rw [this]
    exact V.add_mem (V.smul_mem c hv) (h1 (Submodule.mul_mem_mul hc (h2 hv)))
  · obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_cornerRadical x ha
    have : v * a = c • v + v * (a - c • F.e x) := by
      rw [mul_sub, mul_smul_comm, F.mul_e_of_mem (F.cornerRadical_le_corner x (h2 hv))]; abel
    rw [this]
    exact V.add_mem (V.smul_mem c hv) (h1 (Submodule.mul_mem_mul (h2 hv) hc))

/-- **`rad R_x / (rad R_x)²` has dimension at most one.** -/
theorem exists_rad_gen (hA : IsRepresentationFinite k A) (x : Fin F.m) :
    ∃ t ∈ F.cornerRadical (k := k) x, F.cornerRadical (k := k) x ≤
      Submodule.span k {t} ⊔ F.cornerRadical (k := k) x * F.cornerRadical (k := k) x := by
  set J := F.cornerRadical (k := k) x
  by_cases hJ : J ≤ J * J
  · exact ⟨0, J.zero_mem, le_sup_of_le_right hJ⟩
  obtain ⟨t, htJ, ht⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨t, htJ, fun u hu ↦ ?_⟩
  have hV : ∀ w ∈ J, F.IsEndpointSubbimodule x x (Submodule.span k {w} ⊔ J * J) := fun w hw ↦
    F.isEndpoint_of_between x le_sup_right
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hw) (F.cornerRadical_mul_le x))
  rcases (F.isChain_subbimodules hA x x).total (hV t htJ) (hV u hu) with h | h
  · obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.1
      (h (Submodule.mem_sup_left (Submodule.mem_span_singleton_self t)))
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hyw
      exact ht (hyw ▸ hw)
    have : u = c⁻¹ • t - c⁻¹ • w := by
      rw [← hyw, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self t))) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hw))
  · exact h (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))

/-- **`rad R_x ⊆ R_x t R_x`** by Nakayama's lemma. -/
theorem rad_le_endpointSpan (x : Fin F.m) {t : A} (ht : t ∈ F.cornerRadical (k := k) x)
    (hgen : F.cornerRadical (k := k) x ≤
      Submodule.span k {t} ⊔ F.cornerRadical (k := k) x * F.cornerRadical (k := k) x) :
    F.cornerRadical (k := k) x ≤ F.endpointSpan (k := k) x x t := by
  have htc := F.cornerRadical_le_corner x ht
  have hL := F.isEndpoint_endpointSpan (k := k) htc
  refine F.le_of_le_rad
    (Submodule.mul_le.2 fun r hr n hn ↦ hL.2.1 r (F.cornerRadical_le_corner x hr) n hn)
    (Submodule.mul_le.2 fun n hn r hr ↦ hL.2.2 r (F.cornerRadical_le_corner x hr) n hn) ?_
  refine hgen.trans (sup_le (le_sup_of_le_right ?_) (le_sup_of_le_left le_sup_left))
  exact (Submodule.span_singleton_le_iff_mem _ _).2 (F.mem_endpointSpan_self htc)

theorem exists_of_mem_span_left {x : Fin F.m} {t z : A}
    (hz : z ∈ Submodule.span k {g | ∃ a ∈ F.corner (k := k) x x, g = a * t}) :
    ∃ a ∈ F.corner (k := k) x x, z = a * t := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, Submodule.zero_mem _, (zero_mul t).symm⟩
  | add z z' _ _ hz hz' =>
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨a', ha', rfl⟩ := hz'
      exact ⟨a + a', Submodule.add_mem _ ha ha', (add_mul a a' t).symm⟩
  | smul c z _ hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      exact ⟨c • a, Submodule.smul_mem _ c ha, (smul_mul_assoc c a t).symm⟩

theorem exists_of_mem_span_right {y : Fin F.m} {t z : A}
    (hz : z ∈ Submodule.span k {g | ∃ b ∈ F.corner (k := k) y y, g = t * b}) :
    ∃ b ∈ F.corner (k := k) y y, z = t * b := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, Submodule.zero_mem _, (mul_zero t).symm⟩
  | add z z' _ _ hz hz' =>
      obtain ⟨a, ha, rfl⟩ := hz
      obtain ⟨a', ha', rfl⟩ := hz'
      exact ⟨a + a', Submodule.add_mem _ ha ha', (mul_add t a a').symm⟩
  | smul c z _ hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      exact ⟨c • a, Submodule.smul_mem _ c ha, (mul_smul_comm c t a).symm⟩

theorem cornerVal_mem_corner (x : Fin F.m) (r : (F.complete.idem x).Corner) :
    cornerVal (F.complete.idem x) r ∈ F.corner (k := k) x x :=
  (F.mem_corner_iff').2 (by rw [corner_mul_left, corner_mul_right])

theorem cornerVal_algebraMap (x : Fin F.m) (c : k) :
    cornerVal (F.complete.idem x) (algebraMap k (F.complete.idem x).Corner c) = c • F.e x := by
  change cornerVal _ (c • (1 : (F.complete.idem x).Corner)) = _
  rw [corner_smul_val, corner_one_val]

variable (k) in
/-- **`R_x` is generated by one nilpotent element.** -/
theorem exists_aeval_surjective (hA : IsRepresentationFinite k A) (x : Fin F.m) :
    ∃ t : (F.complete.idem x).Corner, IsNilpotent t ∧
      Function.Surjective (aeval t : k[X] →ₐ[k] (F.complete.idem x).Corner) := by
  set he := F.complete.idem x
  obtain ⟨t, htJ, hgen⟩ := F.exists_rad_gen hA x
  have hL := F.rad_le_endpointSpan x htJ hgen
  have htc := F.cornerRadical_le_corner x htJ
  let t' : he.Corner := cornerMk he t (F.corner_mem_sub x htc)
  have hpow : ∀ n, cornerVal he (t' ^ (n + 1)) = t ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp [t']
    | succ n ih =>
        rw [pow_succ, corner_mul_val, ih]
        change t ^ (n + 1) * t = _
        rw [← pow_succ]
  obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := A)
  have htK : t ^ K = 0 := by
    have := Submodule.pow_mem_pow _ (F.cornerRadical_le_radical x htJ) K
    rwa [hK, Submodule.mem_bot] at this
  have ht'K : t' ^ (K + 1) = 0 :=
    corner_ext he (by rw [hpow, pow_succ, htK, zero_mul, corner_zero_val])
  have hdec : ∀ r : he.Corner, ∃ c : k, ∃ j ∈ F.cornerRadical (k := k) x,
      cornerVal he r = c • F.e x + j := fun r ↦ by
    obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_cornerRadical x (F.cornerVal_mem_corner (k := k) x r)
    exact ⟨c, _, hc, by abel⟩
  refine ⟨t', ⟨K + 1, ht'K⟩, fun a ↦ ?_⟩
  rcases F.endpointSpan_one_sided hA htc with h | h
  · -- `rad R_x ⊆ R_x t`
    have key : ∀ n, ∃ p : k[X], ∃ r : he.Corner, a = aeval t' p + r * t' ^ n := by
      intro n
      induction n with
      | zero => exact ⟨0, a, by simp⟩
      | succ n ih =>
          obtain ⟨p, r, hpr⟩ := ih
          obtain ⟨c, j, hj, hrj⟩ := hdec r
          obtain ⟨b, hb, rfl⟩ := F.exists_of_mem_span_left (h ▸ hL hj)
          let b' : he.Corner := cornerMk he b (F.corner_mem_sub x hb)
          have hr : r = algebraMap k he.Corner c + b' * t' := corner_ext he (by
            rw [hrj, corner_add_val, cornerVal_algebraMap, corner_mul_val]; rfl)
          refine ⟨p + Polynomial.C c * X ^ n, b', ?_⟩
          rw [hpr, hr, add_mul, map_add, map_mul, aeval_C, aeval_X_pow, mul_assoc, ← pow_succ',
            add_assoc]
    obtain ⟨p, r, hpr⟩ := key (K + 1)
    exact ⟨p, by rw [hpr, ht'K, mul_zero, add_zero]⟩
  · -- `rad R_x ⊆ t R_x`
    have key : ∀ n, ∃ p : k[X], ∃ r : he.Corner, a = aeval t' p + t' ^ n * r := by
      intro n
      induction n with
      | zero => exact ⟨0, a, by simp⟩
      | succ n ih =>
          obtain ⟨p, r, hpr⟩ := ih
          obtain ⟨c, j, hj, hrj⟩ := hdec r
          obtain ⟨b, hb, rfl⟩ := F.exists_of_mem_span_right (h ▸ hL hj)
          let b' : he.Corner := cornerMk he b (F.corner_mem_sub x hb)
          have hr : r = algebraMap k he.Corner c + t' * b' := corner_ext he (by
            rw [hrj, corner_add_val, cornerVal_algebraMap, corner_mul_val]; rfl)
          refine ⟨p + Polynomial.C c * X ^ n, b', ?_⟩
          rw [hpr, hr, mul_add, map_add, map_mul, aeval_C, aeval_X_pow, ← mul_assoc, ← pow_succ,
            ← Algebra.commutes, add_assoc]
    obtain ⟨p, r, hpr⟩ := key (K + 1)
    exact ⟨p, by rw [hpr, ht'K, zero_mul, add_zero]⟩

variable (k) in
/-- **Lemma 3.1(2)**: `R_x ≅ k[t]/(t^N)` with `N ≥ 1`. -/
theorem localCorner_iso (hA : IsRepresentationFinite k A) (x : Fin F.m) :
    ∃ N : ℕ, 1 ≤ N ∧ Nonempty ((F.complete.idem x).Corner ≃ₐ[k]
      k[X] ⧸ Ideal.span {(X : k[X]) ^ N}) := by
  classical
  haveI := F.corner_isLocalRing k x
  set C := (F.complete.idem x).Corner
  obtain ⟨t, hnil, hsurj⟩ := F.exists_aeval_surjective k hA x
  set N := Nat.find hnil
  have hN : t ^ N = 0 := Nat.find_spec hnil
  have hN1 : 1 ≤ N := Nat.pos_of_ne_zero fun h0 ↦ one_ne_zero (by rw [← pow_zero t, ← h0]; exact hN)
  have hcomm : ∀ q : k[X], Commute (aeval t q) t := fun q ↦ by
    change aeval t q * t = t * aeval t q
    calc aeval t q * t = aeval t (q * X) := by rw [map_mul, aeval_X]
      _ = aeval t (X * q) := by rw [mul_comm]
      _ = t * aeval t q := by rw [map_mul, aeval_X]
  have hker : RingHom.ker (aeval t : k[X] →ₐ[k] C) = Ideal.span {(X : k[X]) ^ N} := by
    refine le_antisymm (fun p hp ↦ ?_) ((Ideal.span_le).2 ?_)
    · rw [RingHom.mem_ker] at hp
      rw [Ideal.mem_span_singleton]
      by_cases hp0 : p = 0
      · rw [hp0]; exact dvd_zero _
      obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
      simp only [map_zero, sub_zero] at hpq hq
      have hq0 : q.coeff 0 ≠ 0 := fun h ↦ hq (X_dvd_iff.2 h)
      have hunit : IsUnit (aeval t q) := by
        have hsplit : aeval t q = aeval t q.divX * t + algebraMap k C (q.coeff 0) := by
          conv_lhs => rw [← divX_mul_X_add q]
          rw [map_add, map_mul, aeval_X, aeval_C]
        rw [hsplit]
        refine IsNilpotent.isUnit_add_right_of_commute ?_ ((isUnit_iff_ne_zero.2 hq0).map _)
          (Algebra.commutes _ _).symm
        exact (hcomm _).isNilpotent_mul_left hnil
      have htm : t ^ rootMultiplicity 0 p = 0 := by
        have := hp
        rw [hpq, map_mul, map_pow, aeval_X] at this
        exact hunit.mul_left_eq_zero.1 this
      rw [hpq]
      exact dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.find_min' hnil htm)) q
    · rintro _ rfl
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change aeval t (X ^ N) = 0
      rw [map_pow, aeval_X, hN]
  exact ⟨N, hN1, ⟨(Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.trans
    (Ideal.quotientEquivAlgOfEq k hker)⟩⟩

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
