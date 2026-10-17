import MultiplicativeBasisDeformations.Foundations.EndpointChains
import MultiplicativeBasisDeformations.Foundations.CornerRepFinite

/-!
# Homogeneous layers of a graded representation-finite algebra

Proposition 3.8(1) and Corollary 3.3 (`projective-rays.tex`),
for an algebra graded by path length, as used for `A₀` in Proposition 4.14:
"Every endpoint subbimodule is homogeneous: the automorphisms that multiply a
degree-`d` vector by `a^d`, for `a ∈ k*`, preserve its dimension, and the chain
has at most one member of each dimension. Since `k` is infinite, invariance
under those automorphisms implies homogeneity. A homogeneous lift of the
one-dimensional top generates each cyclic subbimodule, and positive endpoint
degrees make successive layers have strictly increasing degrees." and "In each
corner, the chosen vectors represent the consecutive one-dimensional quotients
of a finite chain. They therefore form a basis adapted to every member of that
chain. The intersection of a two-sided ideal with the corner is one such
member."

`LenGrading` is a grading of the algebra by `ℕ` with homogeneous products; the
scaling maps `σ_t` (`scale`) are multiplicative.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

variable (k : Type u) [Field k] (B : Type v) [Ring B] [Algebra k B]

/-- A grading by length with homogeneous products. -/
structure LenGrading where
  proj : ℕ → B →ₗ[k] B
  N : ℕ
  proj_proj : ∀ d e (a : B), proj d (proj e a) = if e = d then proj e a else 0
  proj_ge : ∀ d, N ≤ d → proj d = 0
  sum : ∀ a : B, a = ∑ d ∈ Finset.range N, proj d a
  mul_hom : ∀ d e (a b : B), proj (d + e) (proj d a * proj e b) = proj d a * proj e b

variable {k B} (G : LenGrading k B)

namespace LenGrading

/-- A homogeneous element of degree `d`. -/
def IsHom (d : ℕ) (a : B) : Prop := G.proj d a = a

theorem isHom_proj (d : ℕ) (a : B) : G.IsHom d (G.proj d a) := by
  unfold IsHom; rw [G.proj_proj, if_pos rfl]

theorem proj_of_isHom {d e : ℕ} {a : B} (h : G.IsHom e a) : G.proj d a = if e = d then a else 0 := by
  rw [← h, G.proj_proj, h]

theorem isHom_mul {d e : ℕ} {a b : B} (ha : G.IsHom d a) (hb : G.IsHom e b) :
    G.IsHom (d + e) (a * b) := by
  unfold IsHom; rw [← ha, ← hb]; exact G.mul_hom d e a b

theorem isHom_zero_of_ge {d : ℕ} {a : B} (ha : G.IsHom d a) (hd : G.N ≤ d) : a = 0 := by
  rw [← ha, G.proj_ge d hd, LinearMap.zero_apply]

/-- Components only in degrees `≥ m`. -/
def Ge (m : ℕ) (a : B) : Prop := ∀ d < m, G.proj d a = 0

theorem ge_zero (a : B) : G.Ge 0 a := fun d hd ↦ absurd hd (Nat.not_lt_zero d)

theorem ge_of_isHom {d : ℕ} {a : B} (ha : G.IsHom d a) : G.Ge d a := fun e he ↦ by
  rw [G.proj_of_isHom ha, if_neg (Nat.ne_of_gt he)]

theorem ge_add {m : ℕ} {a b : B} (ha : G.Ge m a) (hb : G.Ge m b) : G.Ge m (a + b) :=
  fun d hd ↦ by rw [map_add, ha d hd, hb d hd, add_zero]

theorem ge_smul {m : ℕ} (c : k) {a : B} (ha : G.Ge m a) : G.Ge m (c • a) :=
  fun d hd ↦ by rw [map_smul, ha d hd, smul_zero]

theorem ge_mono {m m' : ℕ} (h : m' ≤ m) {a : B} (ha : G.Ge m a) : G.Ge m' a :=
  fun d hd ↦ ha d (lt_of_lt_of_le hd h)

/-- The decomposition of a product into homogeneous products. -/
theorem mul_eq_sum (a b : B) :
    a * b = ∑ d ∈ Finset.range G.N, ∑ e ∈ Finset.range G.N, G.proj d a * G.proj e b := by
  conv_lhs => rw [G.sum a, G.sum b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

theorem ge_mul {m n : ℕ} {a b : B} (ha : G.Ge m a) (hb : G.Ge n b) : G.Ge (m + n) (a * b) := by
  intro p hp
  rw [G.mul_eq_sum a b, map_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ ↦ ?_
  rw [G.proj_of_isHom (G.isHom_mul (G.isHom_proj d a) (G.isHom_proj e b))]
  split_ifs with h
  · by_cases hd : d < m
    · rw [ha d hd, zero_mul]
    · rw [hb e (by omega), mul_zero]
  · rfl

/-- **The scaling map** `σ_t`: degree `d` is multiplied by `t^d`. -/
def scale (t : k) : B →ₗ[k] B := ∑ d ∈ Finset.range G.N, t ^ d • G.proj d

theorem scale_apply (t : k) (a : B) :
    G.scale t a = ∑ d ∈ Finset.range G.N, t ^ d • G.proj d a := by
  simp [scale, LinearMap.sum_apply]

theorem scale_isHom (t : k) {d : ℕ} {a : B} (ha : G.IsHom d a) : G.scale t a = t ^ d • a := by
  rw [scale_apply]
  simp_rw [G.proj_of_isHom ha, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [G.isHom_zero_of_ge ha (by simpa using h), smul_zero]

/-- The scaling maps are multiplicative. -/
theorem scale_mul (t : k) (a b : B) : G.scale t (a * b) = G.scale t a * G.scale t b := by
  rw [G.mul_eq_sum a b, map_sum, scale_apply, scale_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [G.scale_isHom t (G.isHom_mul (G.isHom_proj d a) (G.isHom_proj e b)), smul_mul_smul_comm,
    pow_add]

theorem scale_scale {t s : k} (a : B) : G.scale t (G.scale s a) = G.scale (t * s) a := by
  conv_lhs => rw [scale_apply G s a]
  rw [map_sum, scale_apply]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_smul, G.scale_isHom t (G.isHom_proj d a), smul_smul, mul_pow, mul_comm]

theorem scale_one (a : B) : G.scale 1 a = a := by
  rw [scale_apply]
  simp only [one_pow, one_smul]
  exact (G.sum a).symm

theorem scale_inv {t : k} (ht : t ≠ 0) (a : B) : G.scale t (G.scale t⁻¹ a) = a := by
  rw [G.scale_scale, mul_inv_cancel₀ ht, G.scale_one]

theorem scale_injective {t : k} (ht : t ≠ 0) : Function.Injective (G.scale t) := fun a b h ↦ by
  have := congrArg (G.scale t⁻¹) h
  rwa [G.scale_scale, G.scale_scale, inv_mul_cancel₀ ht, G.scale_one, G.scale_one] at this

end LenGrading

/-! ### Endpoint subbimodules are homogeneous -/

namespace PrimitiveIdempotents

variable [IsAlgClosed k] [FiniteDimensional k B] (F : PrimitiveIdempotents B)
  (he0 : ∀ x, G.IsHom 0 (F.e x))

include he0 in
theorem scale_e (t : k) (x : Fin F.m) : G.scale t (F.e x) = F.e x := by
  rw [G.scale_isHom t (he0 x), pow_zero, one_smul]

include he0 in
theorem scale_corner (t : k) {x y : Fin F.m} {a : B} (ha : a ∈ F.corner (k := k) x y) :
    G.scale t a ∈ F.corner (k := k) x y := by
  rw [F.mem_corner_iff'] at ha ⊢
  conv_rhs => rw [← ha]
  rw [G.scale_mul, G.scale_mul, F.scale_e G he0, F.scale_e G he0]

include he0 in
theorem isEndpoint_map_scale {t : k} (ht : t ≠ 0) {x y : Fin F.m} {N : Submodule k B}
    (hN : F.IsEndpointSubbimodule x y N) : F.IsEndpointSubbimodule x y (N.map (G.scale t)) := by
  refine ⟨?_, fun a ha z hz ↦ ?_, fun b hb z hz ↦ ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact F.scale_corner G he0 t (hN.1 hn)
  · obtain ⟨n, hn, rfl⟩ := hz
    refine ⟨G.scale t⁻¹ a * n, hN.2.1 _ (F.scale_corner G he0 t⁻¹ ha) n hn, ?_⟩
    rw [G.scale_mul, G.scale_inv ht]
  · obtain ⟨n, hn, rfl⟩ := hz
    refine ⟨n * G.scale t⁻¹ b, hN.2.2 _ (F.scale_corner G he0 t⁻¹ hb) n hn, ?_⟩
    rw [G.scale_mul, G.scale_inv ht]

include he0 in
/-- The scaling maps preserve every endpoint subbimodule (the chain has one
member of each dimension). -/
theorem scale_mem (hA : IsRepresentationFinite k B) {t : k} (ht : t ≠ 0) {x y : Fin F.m}
    {N : Submodule k B} (hN : F.IsEndpointSubbimodule x y N) {n : B} (hn : n ∈ N) :
    G.scale t n ∈ N := by
  have hM := F.isEndpoint_map_scale G he0 ht hN
  have hrank : Module.finrank k (N.map (G.scale t)) = Module.finrank k N :=
    (N.equivMapOfInjective _ (G.scale_injective ht)).finrank_eq.symm
  have heq : N.map (G.scale t) = N := by
    by_cases hne : N.map (G.scale t) = N
    · exact hne
    rcases F.isChain_subbimodules hA x y hM hN hne with h | h
    · exact Submodule.eq_of_le_of_finrank_eq h hrank
    · exact (Submodule.eq_of_le_of_finrank_eq h hrank.symm).symm
  rw [← heq]
  exact ⟨n, hn, rfl⟩

include he0 in
/-- **Endpoint subbimodules are homogeneous** (`k` infinite). -/
theorem proj_mem [Infinite k] (hA : IsRepresentationFinite k B) {x y : Fin F.m}
    {N : Submodule k B} (hN : F.IsEndpointSubbimodule x y N) {n : B} (hn : n ∈ N) (d : ℕ) :
    G.proj d n ∈ N := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  intro ℓ
  set P : Polynomial k := ∑ e ∈ Finset.range G.N,
    Polynomial.monomial e (ℓ (Submodule.Quotient.mk (G.proj e n)))
  have hroot : ∀ t : k, t ≠ 0 → P.IsRoot t := by
    intro t ht
    have h := F.scale_mem G he0 hA ht hN hn
    have h2 : (ℓ ∘ₗ N.mkQ) (G.scale t n) = 0 := by
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2 h,
        map_zero]
    rw [G.scale_apply, map_sum] at h2
    simp only [map_smul, smul_eq_mul] at h2
    simp only [Polynomial.IsRoot, P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [← h2]
    exact Finset.sum_congr rfl fun e _ ↦ mul_comm _ _
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    exact Set.Infinite.mono (fun t ht ↦ hroot t (by simpa using ht.2))
      ((Set.infinite_univ (α := k)).sdiff (Set.finite_singleton 0))
  have hc := congrArg (fun p : Polynomial k ↦ p.coeff d) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq'] at hc
  split_ifs at hc with hd
  · exact hc
  · rw [G.proj_ge d (by simpa using hd), LinearMap.zero_apply, Submodule.Quotient.mk_zero, map_zero]

/-! ### The radical lies in positive degrees -/

theorem proj_hom_mul {m : ℕ} {e : B} (he : G.IsHom m e) (a : B) (d : ℕ) :
    G.proj (m + d) (e * a) = e * G.proj d a := by
  conv_lhs => rw [G.sum a, Finset.mul_sum, map_sum]
  simp_rw [G.proj_of_isHom (G.isHom_mul he (G.isHom_proj _ a)), add_right_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [G.proj_ge d (by simpa using h), LinearMap.zero_apply, mul_zero]

theorem proj_mul_hom {m : ℕ} {e : B} (he : G.IsHom m e) (a : B) (d : ℕ) :
    G.proj (d + m) (a * e) = G.proj d a * e := by
  conv_lhs => rw [G.sum a, Finset.sum_mul, map_sum]
  simp_rw [G.proj_of_isHom (G.isHom_mul (G.isHom_proj _ a) he), add_left_inj]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [G.proj_ge d (by simpa using h), LinearMap.zero_apply, zero_mul]

include he0 in
theorem proj_corner {x y : Fin F.m} {a : B} (ha : a ∈ F.corner (k := k) x y) (d : ℕ) :
    G.proj d a ∈ F.corner (k := k) x y := by
  rw [F.mem_corner_iff'] at ha ⊢
  have h1 := proj_hom_mul G (he0 x) (a * F.e y) d
  have h2 := proj_mul_hom G (he0 y) a d
  rw [zero_add] at h1
  rw [add_zero] at h2
  calc F.e x * G.proj d a * F.e y = F.e x * G.proj d (a * F.e y) := by rw [h2, mul_assoc]
    _ = G.proj d (F.e x * (a * F.e y)) := h1.symm
    _ = G.proj d a := by rw [← mul_assoc, ha]

theorem nilpotent_of_ge {n : B} (hn : G.Ge 1 n) : n ^ G.N = 0 := by
  have h : ∀ j : ℕ, G.Ge j (n ^ j) := by
    intro j
    induction j with
    | zero => exact G.ge_zero _
    | succ j ih =>
        rw [pow_succ]
        exact G.ge_mul ih hn
  rw [G.sum (n ^ G.N)]
  exact Finset.sum_eq_zero fun d hd ↦ h G.N d (Finset.mem_range.1 hd)

variable (hcorner0 : ∀ (x : Fin F.m) (a : B), a ∈ F.corner (k := k) x x → G.IsHom 0 a →
  ∃ c : k, a = c • F.e x)

include he0 hcorner0 in
/-- **The corner radicals lie in positive degrees.** -/
theorem rad_ge (x : Fin F.m) {a : B} (ha : a ∈ F.cornerRadical (k := k) x) : G.Ge 1 a := by
  intro d hd
  obtain rfl : d = 0 := by omega
  obtain ⟨c, hc⟩ := hcorner0 x _ (F.proj_corner G he0 ha.1 0) (G.isHom_proj 0 a)
  rw [hc]
  suffices c = 0 by rw [this, zero_smul]
  have he := F.complete.idem x
  haveI := F.corner_isLocalRing k x
  haveI : FiniteDimensional k he.Corner := corner_finite he
  -- `n = a - c e_x` is nilpotent
  set n := a - c • F.e x
  have hnC : n ∈ F.corner (k := k) x x :=
    Submodule.sub_mem _ ha.1 (Submodule.smul_mem _ c (F.e_mem_corner x))
  have hnge : G.Ge 1 n := by
    intro d hd
    obtain rfl : d = 0 := by omega
    rw [map_sub, map_smul, hc, he0 x, sub_self]
  have hnil := nilpotent_of_ge G hnge
  let a' : he.Corner := cornerMk he a (F.corner_mem_sub x ha.1)
  let n' : he.Corner := cornerMk he n (F.corner_mem_sub x hnC)
  have hsplit : a' = algebraMap k he.Corner c + n' := by
    apply corner_ext
    change a = c • F.e x + n
    simp [n]
  -- `a'` is not a unit: its inverse would put `e_x` in the radical
  have hnu : ¬ IsUnit a' := by
    rintro ⟨u, hu⟩
    have h1 : a * cornerVal he u.inv = F.e x := by
      have := congrArg (cornerVal he) u.val_inv
      rw [corner_mul_val, hu] at this
      exact this
    have hJ : F.e x ∈ algebraRadical k B := by
      rw [← h1]
      change a * _ ∈ Ring.jacobson B
      haveI : (Ring.jacobson B).IsTwoSided := inferInstance
      exact Ideal.mul_mem_right _ (Ring.jacobson B) ha.2
    obtain ⟨K, hK⟩ := algebraRadical_pow_eq_bot (k := k) (A := B)
    have : F.e x ^ (K + 1) ∈ algebraRadical k B ^ (K + 1) := Submodule.pow_mem_pow _ hJ _
    rw [(F.complete.idem x).pow_succ_eq] at this
    have hK1 : algebraRadical k B ^ (K + 1) = ⊥ := by
      rw [pow_succ, hK, Submodule.bot_mul]
    rw [hK1, Submodule.mem_bot] at this
    exact (F.primitive x).2.1 this
  have hres_a : MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k a' = 0 :=
    MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_eq_of_isResidueScalar
      (by simpa [MBDVendor.Magnitude.LocalAlgebraResidue.IsResidueScalar] using hnu)
  have hres_n : MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k n' = 0 := by
    have hval : ∀ j : ℕ, cornerVal he (n' ^ (j + 1)) = n ^ (j + 1) := by
      intro j
      induction j with
      | zero => rw [zero_add, pow_one, pow_one]; rfl
      | succ j ih =>
          rw [pow_succ, corner_mul_val, ih]
          exact (pow_succ n (j + 1)).symm
    have hpow : n' ^ (G.N + 1) = 0 := by
      apply corner_ext
      rw [hval, pow_succ, hnil, zero_mul]; rfl
    have hres : ∀ j : ℕ, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k (n' ^ j) =
        MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar k n' ^ j := by
      intro j
      induction j with
      | zero =>
          rw [pow_zero, pow_zero, show (1 : he.Corner) = algebraMap k he.Corner 1 from
            (map_one _).symm, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_algebraMap]
      | succ j ih =>
          rw [pow_succ, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_mul, ih, pow_succ]
    have := hres (G.N + 1)
    rw [hpow, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_zero] at this
    exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.1 this.symm
  rw [hsplit, MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_add,
    MBDVendor.Magnitude.LocalAlgebraResidue.residueScalar_algebraMap, hres_n, add_zero] at hres_a
  exact hres_a

/-! ### Cyclic subbimodules and their radicals -/

theorem corner_mul_corner {x y z : Fin F.m} {a b : B} (ha : a ∈ F.corner (k := k) x y)
    (hb : b ∈ F.corner (k := k) y z) : a * b ∈ F.corner (k := k) x z := by
  rw [F.mem_corner_iff']
  rw [mul_assoc, mul_assoc, (F.corner_mul_mem hb).2, ← mul_assoc, (F.corner_mul_mem ha).1]

theorem mem_endpointSpan_self {x y : Fin F.m} {g : B} (hg : g ∈ F.corner (k := k) x y) :
    g ∈ F.endpointSpan (k := k) x y g := by
  have h : F.e x * g * F.e y ∈ F.endpointSpan (k := k) x y g :=
    Submodule.subset_span ⟨F.e x, F.e_mem_corner x, F.e y, F.e_mem_corner y, rfl⟩
  rwa [(F.mem_corner_iff').1 hg] at h

/-- `U(g) = k g + R(g)`. -/
theorem endpointSpan_eq {x y : Fin F.m} {g : B} (hg : g ∈ F.corner (k := k) x y) :
    F.endpointSpan (k := k) x y g = (k ∙ g) ⊔ F.endpointRadical (k := k) x y g := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨c, hc⟩ := F.exists_sub_smul_mem_radical k x ha
    obtain ⟨c', hc'⟩ := F.exists_sub_smul_mem_radical k y hb
    obtain ⟨r, hr, rfl⟩ : ∃ r ∈ F.cornerRadical (k := k) x, a = c • F.e x + r :=
      ⟨a - c • F.e x, ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ c (F.e_mem_corner x)), hc⟩,
        by abel⟩
    obtain ⟨r', hr', rfl⟩ : ∃ r' ∈ F.cornerRadical (k := k) y, b = c' • F.e y + r' :=
      ⟨b - c' • F.e y, ⟨Submodule.sub_mem _ hb (Submodule.smul_mem _ c' (F.e_mem_corner y)), hc'⟩,
        by abel⟩
    have hgl := (F.corner_mul_mem hg).1
    have hgr := (F.corner_mul_mem hg).2
    have h1 : (c • F.e x + r) * g * (c' • F.e y + r') =
        c • (c' • g + g * r') + r * g * (c' • F.e y + r') := by
      rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, hgl, mul_add, mul_smul_comm, hgr]
    rw [h1]
    have hgr' : g * r' ∈ F.endpointRadical (k := k) x y g :=
      Submodule.subset_span (Or.inr ⟨F.e x, F.e_mem_corner x, r', hr', by rw [hgl]⟩)
    have hrg : r * g * (c' • F.e y + r') ∈ F.endpointRadical (k := k) x y g :=
      Submodule.subset_span (Or.inl ⟨r, hr, _, Submodule.add_mem _
        (Submodule.smul_mem _ c' (F.e_mem_corner y)) hr'.1, rfl⟩)
    exact Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ c' (Submodule.mem_span_singleton_self g)))
      (Submodule.mem_sup_right hgr'))) (Submodule.mem_sup_right hrg)
  · refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (F.mem_endpointSpan_self hg)) ?_
    refine Submodule.span_le.2 ?_
    rintro _ (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact Submodule.subset_span ⟨a, ha.1, b, hb, rfl⟩
    · exact Submodule.subset_span ⟨a, ha, b, hb.1, rfl⟩

theorem isEndpoint_endpointSpan {x y : Fin F.m} {g : B} (hg : g ∈ F.corner (k := k) x y) :
    F.IsEndpointSubbimodule x y (F.endpointSpan (k := k) x y g) := by
  refine ⟨Submodule.span_le.2 ?_, fun a' ha' z hz ↦ ?_, fun b' hb' z hz ↦ ?_⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact F.corner_mul_corner (F.corner_mul_corner ha hg) hb
  · induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hz
        exact Submodule.subset_span ⟨a' * a, F.corner_mul_corner ha' ha, b, hb, by
          simp only [mul_assoc]⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hz
  · induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hz
        exact Submodule.subset_span ⟨a, ha, b * b', F.corner_mul_corner hb hb', by
          simp only [mul_assoc]⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [add_mul]; exact Submodule.add_mem _ hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hz

theorem isEndpoint_endpointRadical {x y : Fin F.m} {g : B} (hg : g ∈ F.corner (k := k) x y) :
    F.IsEndpointSubbimodule x y (F.endpointRadical (k := k) x y g) := by
  refine ⟨Submodule.span_le.2 ?_, fun a' ha' z hz ↦ ?_, fun b' hb' z hz ↦ ?_⟩
  · rintro _ (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact F.corner_mul_corner (F.corner_mul_corner ha.1 hg) hb
    · exact F.corner_mul_corner (F.corner_mul_corner ha hg) hb.1
  · induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
        · exact Submodule.subset_span (Or.inl ⟨a' * a, F.radL_mem ha' ha, b, hb, by
            simp only [mul_assoc]⟩)
        · exact Submodule.subset_span (Or.inr ⟨a' * a, F.corner_mul_corner ha' ha, b, hb, by
            simp only [mul_assoc]⟩)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [mul_add]; exact Submodule.add_mem _ hz hw
    | smul c z _ hz => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hz
  · induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩
        · exact Submodule.subset_span (Or.inl ⟨a, ha, b * b', F.corner_mul_corner hb hb', by
            simp only [mul_assoc]⟩)
        · exact Submodule.subset_span (Or.inr ⟨a, ha, b * b', F.radR_mem hb' hb, by
            simp only [mul_assoc]⟩)
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => rw [add_mul]; exact Submodule.add_mem _ hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hz

include he0 hcorner0 in
/-- **`R(g)` lies in degrees above that of `g`.** -/
theorem endpointRadical_ge {x y : Fin F.m} {g : B} {d : ℕ} (hgd : G.IsHom d g) {r : B}
    (hr : r ∈ F.endpointRadical (k := k) x y g) : G.Ge (d + 1) r := by
  induction hr using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨a, ha, b, _, rfl⟩ | ⟨a, _, b, hb, rfl⟩
      · have := G.ge_mul (G.ge_mul (F.rad_ge G he0 hcorner0 x ha) (G.ge_of_isHom hgd)) (G.ge_zero b)
        rwa [add_zero, add_comm] at this
      · exact G.ge_mul (G.ge_mul (G.ge_zero a) (G.ge_of_isHom hgd)) (F.rad_ge G he0 hcorner0 y hb)
          |> fun h ↦ by rwa [zero_add] at h
  | zero => exact fun e _ ↦ map_zero _
  | add z w _ _ hz hw => exact G.ge_add hz hw
  | smul c z _ hz => exact G.ge_smul c hz

/-! ### Layers -/

variable [Infinite k] (hA : IsRepresentationFinite k B)

include he0 hA in
theorem exists_hom_mem {x y : Fin F.m} {N : Submodule k B} (hN : F.IsEndpointSubbimodule x y N)
    {n : B} (hn : n ∈ N) (hn0 : n ≠ 0) : ∃ d, G.proj d n ∈ N ∧ G.proj d n ≠ 0 := by
  by_contra h
  push Not at h
  apply hn0
  rw [G.sum n]
  exact Finset.sum_eq_zero fun d _ ↦ h d (F.proj_mem G he0 hA hN hn d)

include he0 hcorner0 hA in
/-- **A homogeneous generator of minimal degree generates**: every nonzero
endpoint subbimodule is `U(g)` for a homogeneous `g`. -/
theorem layer {x y : Fin F.m} {N : Submodule k B} (hN : F.IsEndpointSubbimodule x y N)
    (hN0 : N ≠ ⊥) : ∃ g d, G.IsHom d g ∧ g ≠ 0 ∧ g ∈ N ∧ N = F.endpointSpan (k := k) x y g := by
  classical
  have hex : ∃ d, ∃ g ∈ N, G.IsHom d g ∧ g ≠ 0 := by
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
    obtain ⟨d, hd, hd0⟩ := F.exists_hom_mem G he0 hA hN hn hn0
    exact ⟨d, _, hd, G.isHom_proj d n, hd0⟩
  set d₀ := Nat.find hex
  obtain ⟨g, hgN, hgd, hg0⟩ := Nat.find_spec hex
  have hgC := hN.1 hgN
  refine ⟨g, d₀, hgd, hg0, hgN, ?_⟩
  have hUN : F.endpointSpan (k := k) x y g ≤ N := Submodule.span_le.2 (by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hN.2.2 b hb _ (hN.2.1 a ha g hgN))
  refine (le_antisymm hUN ?_).symm
  by_contra hle
  obtain ⟨n, hn, hnU⟩ := Set.not_subset.1 hle
  have hU := F.isEndpoint_endpointSpan hgC
  obtain ⟨e, he⟩ : ∃ e, G.proj e n ∉ F.endpointSpan (k := k) x y g := by
    by_contra h
    push Not at h
    apply hnU
    rw [G.sum n]
    exact Submodule.sum_mem _ fun d _ ↦ h d
  set g' := G.proj e n
  have hg'N : g' ∈ N := F.proj_mem G he0 hA hN hn e
  have hg'0 : g' ≠ 0 := fun h ↦ he (h ▸ Submodule.zero_mem _)
  have hde : d₀ ≤ e := Nat.find_min' hex ⟨g', hg'N, G.isHom_proj e n, hg'0⟩
  have hU' := F.isEndpoint_endpointSpan (hN.1 hg'N)
  have hchain := F.isChain_subbimodules hA x y
  by_cases heq : F.endpointSpan (k := k) x y g = F.endpointSpan (k := k) x y g'
  · exact he (heq ▸ F.mem_endpointSpan_self (hN.1 hg'N))
  rcases hchain hU hU' heq with h | h
  · -- `g ∈ U(g') = k g' + R(g')`
    have hgU' := h (F.mem_endpointSpan_self hgC)
    rw [F.endpointSpan_eq (hN.1 hg'N)] at hgU'
    obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 hgU'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hrge := F.endpointRadical_ge G he0 hcorner0 (G.isHom_proj e n) hr
    have hp := congrArg (G.proj d₀) hur
    rw [map_add, map_smul, G.proj_of_isHom (G.isHom_proj e n), hrge d₀ (by omega), add_zero,
      hgd] at hp
    by_cases hed : e = d₀
    · rw [if_pos hed] at hp
      have hc : c ≠ 0 := fun h0 ↦ hg0 (by rw [← hp, h0, zero_smul])
      apply he
      have : g' = c⁻¹ • g := by rw [← hp, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (F.mem_endpointSpan_self hgC)
    · rw [if_neg hed, smul_zero] at hp
      exact hg0 hp.symm
  · exact he (h (F.mem_endpointSpan_self (hN.1 hg'N)))

include he0 hcorner0 hA in
/-- **One line in each degree**: the homogeneous elements of a given degree of
an endpoint subbimodule lie on a line (successive layers have strictly
increasing degrees). -/
theorem lines {x y : Fin F.m} : ∀ (n : ℕ) (N : Submodule k B), Module.finrank k N = n →
    F.IsEndpointSubbimodule x y N → ∀ d, ∃ w : B, ∀ u ∈ N, G.IsHom d u → u ∈ k ∙ w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hN d
  by_cases hN0 : N = ⊥
  · refine ⟨0, fun u hu _ ↦ ?_⟩
    rw [hN0, Submodule.mem_bot] at hu
    rw [hu]; exact Submodule.zero_mem _
  obtain ⟨g, d₀, hgd, hg0, hgN, hNU⟩ := F.layer G he0 hcorner0 hA hN hN0
  have hgC := hN.1 hgN
  have hR := F.isEndpoint_endpointRadical hgC
  have hRN : F.endpointRadical (k := k) x y g < N := by
    rw [hNU, F.endpointSpan_eq hgC]
    refine lt_of_le_of_ne le_sup_right fun h ↦ ?_
    have hgR : g ∈ F.endpointRadical (k := k) x y g := by
      rw [h]; exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self g)
    have := F.endpointRadical_ge G he0 hcorner0 hgd hgR d₀ (by omega)
    rw [hgd] at this
    exact hg0 this
  have hdecomp : ∀ u ∈ N, ∃ c : k, ∃ r ∈ F.endpointRadical (k := k) x y g, u = c • g + r := by
    intro u hu
    rw [hNU, F.endpointSpan_eq hgC] at hu
    obtain ⟨v, hv, r, hr, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    exact ⟨c, r, hr, rfl⟩
  by_cases hd : d = d₀
  · subst hd
    refine ⟨g, fun u hu hud ↦ ?_⟩
    obtain ⟨c, r, hr, rfl⟩ := hdecomp u hu
    have hp := hud
    unfold LenGrading.IsHom at hp
    rw [map_add, map_smul, hgd, F.endpointRadical_ge G he0 hcorner0 hgd hr d (by omega),
      add_zero] at hp
    rw [← hp]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self g)
  · obtain ⟨w, hw⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hRN) _ rfl hR d
    refine ⟨w, fun u hu hud ↦ ?_⟩
    obtain ⟨c, r, hr, rfl⟩ := hdecomp u hu
    have hp := hud
    unfold LenGrading.IsHom at hp
    rw [map_add, map_smul, G.proj_of_isHom hgd, if_neg (Ne.symm hd), smul_zero, zero_add] at hp
    rw [← hp]
    exact hw _ (F.proj_mem G he0 hA hR hr d) (G.isHom_proj d r)

/-! ### A homogeneous basis is adapted to every two-sided ideal -/

variable {ι : Type*} (b : Module.Basis ι k B)
  (hb : ∀ i, ∃ x y d, b i ∈ F.corner (k := k) x y ∧ G.IsHom d (b i))

include he0 in
theorem proj_corner_basis {x y : Fin F.m} {d : ℕ} (i : ι) {x' y' : Fin F.m} {d' : ℕ}
    (hi : b i ∈ F.corner (k := k) x' y') (hid : G.IsHom d' (b i)) :
    G.proj d (F.e x * b i * F.e y) = if x' = x ∧ y' = y ∧ d' = d then b i else 0 := by
  have hl := (F.corner_mul_mem hi).1
  have hr := (F.corner_mul_mem hi).2
  by_cases hx : x' = x
  · subst hx
    by_cases hy : y' = y
    · subst hy
      rw [hl, hr, G.proj_of_isHom hid]
      by_cases hd : d' = d
      · rw [if_pos hd, if_pos ⟨rfl, rfl, hd⟩]
      · rw [if_neg hd, if_neg (fun h ↦ hd h.2.2)]
    · rw [if_neg (fun h ↦ hy h.2.1)]
      have : F.e x' * b i * F.e y = 0 := by
        calc F.e x' * b i * F.e y = F.e x' * (b i * F.e y') * F.e y := by rw [hr]
          _ = F.e x' * b i * (F.e y' * F.e y) := by simp only [mul_assoc]
          _ = 0 := by rw [F.complete.ortho hy, mul_zero]
      rw [this, map_zero]
  · rw [if_neg (fun h ↦ hx h.1)]
    have : F.e x * b i * F.e y = 0 := by
      calc F.e x * b i * F.e y = F.e x * (F.e x' * b i) * F.e y := by rw [hl]
        _ = (F.e x * F.e x') * b i * F.e y := by simp only [mul_assoc]
        _ = 0 := by rw [F.complete.ortho (Ne.symm hx), zero_mul, zero_mul]
    rw [this, map_zero]

include he0 hcorner0 hA hb in
/-- Each homogeneous element of a corner lying in an endpoint subbimodule is in
the span of the basis vectors it contains. -/
theorem hom_mem_span {x y : Fin F.m} {N : Submodule k B} (hN : F.IsEndpointSubbimodule x y N)
    {d : ℕ} {h : B} (hhN : h ∈ N) (hhd : G.IsHom d h) :
    h ∈ Submodule.span k (b '' {i | b i ∈ N}) := by
  classical
  have hhC := hN.1 hhN
  -- `h` is the combination of the basis vectors of its corner and degree
  set T := {i | b i ∈ F.corner (k := k) x y ∧ G.IsHom d (b i)}
  have hexp : h = ∑ i ∈ (b.repr h).support, b.repr h i • G.proj d (F.e x * b i * F.e y) := by
    have h1 : h = G.proj d (F.e x * h * F.e y) := by rw [(F.mem_corner_iff').1 hhC, hhd]
    conv_lhs => rw [h1, ← b.linearCombination_repr h, Finsupp.linearCombination_apply,
      Finsupp.sum]
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul]
  -- the basis vectors of degree `d` in the corner lie on one line
  obtain ⟨w, hw⟩ := F.lines G he0 hcorner0 hA _ (F.corner (k := k) x y) rfl
    ⟨le_rfl, fun a ha z hz ↦ F.corner_mul_corner ha hz, fun a ha z hz ↦ F.corner_mul_corner hz ha⟩ d
  have hunique : ∀ i ∈ T, ∀ j ∈ T, i = j := by
    intro i hi j hj
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hw _ hi.1 hi.2)
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 (hw _ hj.1 hj.2)
    have hc'0 : c' ≠ 0 := fun h0 ↦ b.ne_zero j (by rw [← hc', h0, zero_smul])
    have : b i = (c * c'⁻¹) • b j := by rw [← hc, ← hc', smul_smul, mul_assoc,
      inv_mul_cancel₀ hc'0, mul_one]
    by_contra hij
    have hr := congrArg (fun v ↦ b.repr v i) this
    simp only [Module.Basis.repr_self, map_smul, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, smul_zero] at hr
    exact one_ne_zero hr
  rw [hexp]
  refine Submodule.sum_mem _ fun i hi ↦ ?_
  obtain ⟨x', y', d', hi', hid'⟩ := hb i
  rw [F.proj_corner_basis G he0 b i hi' hid']
  split_ifs with hxyd
  · obtain ⟨rfl, rfl, rfl⟩ := hxyd
    -- `h = c • b i` with `c ≠ 0`, so `b i ∈ N`
    have hiT : i ∈ T := ⟨hi', hid'⟩
    have hsum : h = b.repr h i • b i := by
      conv_lhs => rw [hexp]
      rw [Finset.sum_eq_single i]
      · rw [F.proj_corner_basis G he0 b i hi' hid', if_pos ⟨rfl, rfl, rfl⟩]
      · intro j _ hji
        obtain ⟨x'', y'', d'', hj', hjd'⟩ := hb j
        rw [F.proj_corner_basis G he0 b j hj' hjd']
        split_ifs with hj
        · obtain ⟨rfl, rfl, rfl⟩ := hj
          exact absurd (hunique j ⟨hj', hjd'⟩ i hiT) hji
        · rw [smul_zero]
      · intro hni
        rw [Finsupp.notMem_support_iff.1 hni, zero_smul]
    have hc : b.repr h i ≠ 0 := Finsupp.mem_support_iff.1 hi
    have hbi : b i ∈ N := by
      generalize b.repr h i = c at hsum hc
      have := Submodule.smul_mem N c⁻¹ hhN
      rwa [hsum, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hbi, rfl⟩)
  · rw [smul_zero]; exact Submodule.zero_mem _

include he0 hcorner0 hA hb in
/-- **Corollary 3.3 for a homogeneous basis**: its intersection with a
two-sided ideal spans that ideal. -/
theorem span_basis_ideal (I : Submodule k B) (hIl : ∀ a z, z ∈ I → a * z ∈ I)
    (hIr : ∀ a z, z ∈ I → z * a ∈ I) : Submodule.span k (b '' {i | b i ∈ I}) = I := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact hi)
  intro z hz
  have hz1 : z = ∑ x, ∑ y, F.e x * z * F.e y := by
    calc z = (∑ x, F.e x) * z * (∑ y, F.e y) := by rw [F.complete.complete, one_mul, mul_one]
      _ = ∑ x, ∑ y, F.e x * z * F.e y := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.mul_sum]
  rw [hz1]
  refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ ?_
  set N := F.corner (k := k) x y ⊓ I
  have hN : F.IsEndpointSubbimodule x y N :=
    ⟨inf_le_left, fun a ha n hn ↦ ⟨F.corner_mul_corner ha hn.1, hIl a n hn.2⟩,
      fun a ha n hn ↦ ⟨F.corner_mul_corner hn.1 ha, hIr a n hn.2⟩⟩
  have hmem : F.e x * z * F.e y ∈ N :=
    ⟨⟨z, by change F.e x * (z * F.e y) = _; rw [mul_assoc]⟩, hIr _ _ (hIl _ _ hz)⟩
  have hmono : Submodule.span k (b '' {i | b i ∈ N}) ≤ Submodule.span k (b '' {i | b i ∈ I}) :=
    Submodule.span_mono (Set.image_mono fun i hi ↦ hi.2)
  rw [G.sum (F.e x * z * F.e y)]
  exact Submodule.sum_mem _ fun d _ ↦ hmono (F.hom_mem_span G he0 hcorner0 hA b hb hN
    (F.proj_mem G he0 hA hN hmem d) (G.isHom_proj d _))

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
