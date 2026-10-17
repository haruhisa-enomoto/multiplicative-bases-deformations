import MultiplicativeBasisDeformations.Foundations.CornerRadical
import MultiplicativeBasisDeformations.Foundations.PrimitiveDecomposition
import MultiplicativeBasisDeformations.Foundations.A0Normed

/-!
# Lemma 2.1: normed bases from the basic algebra

`lem:nonbasic-basis` (`graded-category.tex:17–52`). Let `B₀ = eAe` with
`AeA = A` have a normed multiplicative basis with primitive idempotents `e_i`.
"Every basis element `b` belongs to one corner: in `b = Σ e_i b e_j`, each nonzero
summand is a basis element by multiplicativity […]." Each primitive idempotent
`f` of a complete set of `A` has `fA ≅ e_i A`, given by elements `u ∈ fAe_i`,
`v ∈ e_iAf` with `uv = f`, `vu = e_i` (here from `1 ∈ AeA` and the local corner
`fAf`). "For each element `b ∈ e_iB₀e_j` of the given basis, take all its
single-entry matrices `E_{iα,jβ}(b)`": here `u_s b v_t`. "Their multiplication is
`E_{iα,jβ}(b) E_{lγ,mδ}(c) = E_{iα,mδ}(bc)` if `(j,β) = (l,γ)`, `0` otherwise
[…]. The single-entry matrices `E_{iα,iα}(e_i)` form a complete set of primitive
orthogonal idempotents. The radical powers of `A` have the same block
description with `e_i (rad B₀)^n e_j` in each block."
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace Nonbasic

open Classical

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
  {e : A} (he : IsIdempotentElem e) {ι : Type v} (b : Module.Basis ι k he.Corner)

/-- The hypotheses on the basis of `B₀ = eAe`. -/
structure Hyp (E : Finset ι) : Prop where
  ortho : CompleteOrthogonalIdempotents (fun i : E ↦ b i)
  mul : IsMultiplicativeBasis b
  prim : ∀ i ∈ E, IsPrimitiveIdempotent (b i)
  rad : ∀ n : ℕ, 1 ≤ n → Submodule.span k (b '' {i | b i ∈ algebraRadicalPow k he.Corner n}) =
    algebraRadicalPow k he.Corner n

/-- A basis element of `B₀`, in `A`. -/
def bv (l : ι) : A := cornerVal he (b l)

variable {he b} {E : Finset ι}

/-- The idempotent `e_i` of `B₀`, in `A`. -/
def ε (he : IsIdempotentElem e) (b : Module.Basis ι k he.Corner) (i : E) : A := bv he b i.1

namespace Hyp

variable (H : Hyp he b E)

theorem bv_ne_zero (l : ι) : bv he b l ≠ 0 := fun h ↦
  b.ne_zero l (corner_ext he (by rw [corner_zero_val]; exact h))

theorem e_mul_bv (l : ι) : e * bv he b l = bv he b l := corner_mul_left he _

theorem bv_mul_e (l : ι) : bv he b l * e = bv he b l := corner_mul_right he _

include H in
theorem ε_idem (i : E) : ε he b i * ε he b i = ε he b i := by
  unfold ε bv; rw [← corner_mul_val]; exact congrArg _ (H.ortho.idem i).eq

include H in
theorem ε_orth {i j : E} (hij : i ≠ j) : ε he b i * ε he b j = 0 := by
  unfold ε bv; rw [← corner_mul_val, H.ortho.ortho hij]; rfl

include H in
theorem sum_ε : ∑ i : E, ε he b i = e := by
  have h := congrArg (cornerValL k he) H.ortho.complete
  rw [map_sum, cornerValL_apply, corner_one_val] at h
  exact h

include H in
theorem triple (i l j : ι) : b i * b l * b j = 0 ∨ ∃ m, b i * b l * b j = b m := by
  rcases H.mul i l with h | ⟨m, hm⟩
  · left; rw [h, zero_mul]
  · rw [hm]; exact H.mul m j

include H in
/-- **Every basis element lies in one corner `e_i B₀ e_j`.** -/
theorem exists_corner (l : ι) : ∃ i j : E, ε he b i * bv he b l * ε he b j = bv he b l := by
  by_contra hcon
  push Not at hcon
  have h1 : b l = ∑ i : E, ∑ j : E, b i * b l * b j := by
    simp_rw [← Finset.mul_sum, H.ortho.complete, mul_one, ← Finset.sum_mul, H.ortho.complete,
      one_mul]
  have h2 : ∀ i j : E, b.repr (b i * b l * b j) l = 0 := by
    intro i j
    rcases H.triple i l j with h | ⟨m, hm⟩
    · rw [h, map_zero, Finsupp.zero_apply]
    · rw [hm, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
      rintro rfl
      apply hcon i j
      unfold ε bv
      rw [← corner_mul_val, ← corner_mul_val, hm]
  have h3 := congrArg (fun x ↦ b.repr x l) h1
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply, h2, Finset.sum_const_zero] at h3
  exact one_ne_zero h3

/-- The source idempotent of a basis element. -/
def src (l : ι) : E := Classical.choose (H.exists_corner l)

/-- The target idempotent of a basis element. -/
def tgt (l : ι) : E := Classical.choose (Classical.choose_spec (H.exists_corner l))

theorem src_tgt (l : ι) : ε he b (H.src l) * bv he b l * ε he b (H.tgt l) = bv he b l :=
  Classical.choose_spec (Classical.choose_spec (H.exists_corner l))

theorem src_mul (l : ι) : ε he b (H.src l) * bv he b l = bv he b l := by
  conv_lhs => rw [← H.src_tgt l]
  rw [← mul_assoc, ← mul_assoc, H.ε_idem, H.src_tgt]

theorem mul_tgt (l : ι) : bv he b l * ε he b (H.tgt l) = bv he b l := by
  conv_lhs => rw [← H.src_tgt l]
  rw [mul_assoc, H.ε_idem, H.src_tgt]

theorem ε_mul_bv (i : E) (l : ι) :
    ε he b i * bv he b l = if i = H.src l then bv he b l else 0 := by
  split_ifs with h
  · rw [h, H.src_mul]
  · rw [← H.src_mul l, ← mul_assoc, H.ε_orth h, zero_mul]

theorem bv_mul_ε (i : E) (l : ι) :
    bv he b l * ε he b i = if i = H.tgt l then bv he b l else 0 := by
  split_ifs with h
  · rw [h, H.mul_tgt]
  · rw [← H.mul_tgt l, mul_assoc, H.ε_orth (Ne.symm h), mul_zero]

theorem src_ε (i : E) : H.src i.1 = i := by
  by_contra h
  have := H.ε_mul_bv i i.1
  rw [if_neg (Ne.symm h)] at this
  exact bv_ne_zero i.1 (by rw [← this]; exact (H.ε_idem i).symm)

theorem tgt_ε (i : E) : H.tgt i.1 = i := by
  by_contra h
  have := H.bv_mul_ε i i.1
  rw [if_neg (Ne.symm h)] at this
  exact bv_ne_zero i.1 (by rw [← this]; exact (H.ε_idem i).symm)

theorem e_mul_ε (i : E) : e * ε he b i = ε he b i := e_mul_bv _

theorem ε_mul_e (i : E) : ε he b i * e = ε he b i := bv_mul_e _

include H in
/-- **`e_i` is primitive in `A`.** -/
theorem ε_primitive (i : E) : IsPrimitiveIdempotent (ε he b i) := by
  have hp := H.prim i i.2
  refine ⟨H.ε_idem i, bv_ne_zero _, fun g hg h1 h2 ↦ ?_⟩
  have hge : e * g = g := by rw [← h1, ← mul_assoc, e_mul_ε]
  have hge' : g * e = g := by rw [← h2, mul_assoc, ε_mul_e]
  let G : he.Corner := cornerMk he g ((Subsemigroup.mem_corner_iff he).2 ⟨hge, hge'⟩)
  have hG : IsIdempotentElem G := corner_ext he (by rw [corner_mul_val]; exact hg.eq)
  rcases hp.2.2 G hG (corner_ext he (by rw [corner_mul_val]; exact h1))
    (corner_ext he (by rw [corner_mul_val]; exact h2)) with h | h
  · left; exact congrArg (cornerVal he) h
  · right; exact congrArg (cornerVal he) h

omit [FiniteDimensional k A] in
/-- An element of the two-sided ideal `AeA` is a sum `Σ p_r e q_r`. -/
theorem exists_sum_of_mem_span {a : A} (ha : a ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}) :
    ∃ (m : ℕ) (p q : Fin m → A), ∑ r, p r * e * q r = a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, q, rfl⟩ := hx
      exact ⟨1, fun _ ↦ p, fun _ ↦ q, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, p, q, rfl⟩ := hx
      obtain ⟨m', p', q', rfl⟩ := hy
      refine ⟨m + m', Fin.append p p', Fin.append q q', ?_⟩
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
      obtain ⟨m, p, q, rfl⟩ := hx
      refine ⟨m, fun r ↦ c • p r, q, ?_⟩
      rw [Finset.smul_sum]
      simp only [smul_mul_assoc]

include H in
/-- **Each primitive idempotent `f` of `A` is isomorphic to some `e_i`**: there are
`u ∈ fAe_i`, `v ∈ e_iAf` with `uv = f` and `vu = e_i`. Write
`f = Σ f p_r e_i q_r f` from `1 ∈ AeA`; the corner `fAf` is local, so one summand is
a unit. -/
theorem exists_match (hfull : (1 : A) ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    {f0 : A} (hp : IsPrimitiveIdempotent f0) :
    ∃ (i : E) (u v : A), f0 * u = u ∧ u * ε he b i = u ∧ ε he b i * v = v ∧ v * f0 = v ∧
      u * v = f0 ∧ v * u = ε he b i := by
  haveI := corner_isLocalRing_of_primitive k hp
  obtain ⟨m, p, q, hpq⟩ := exists_sum_of_mem_span hfull
  let t : Fin m → E → hp.1.Corner := fun r i ↦
    cornerMk hp.1 (f0 * (p r * ε he b i * q r) * f0) ⟨_, rfl⟩
  have hsum : ∑ r, ∑ i, t r i = 1 := by
    apply corner_ext hp.1
    have hv : cornerVal hp.1 (∑ r, ∑ i, t r i) =
        ∑ r, ∑ i : E, f0 * (p r * ε he b i * q r) * f0 := by
      rw [← cornerValL_apply (k := k), map_sum]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [map_sum]
      rfl
    rw [hv, corner_one_val]
    have he0 : f0 * f0 = f0 := hp.1.eq
    have hin : ∀ r, ∑ i : E, p r * ε he b i * q r = p r * e * q r := fun r ↦ by
      rw [← Finset.sum_mul, ← Finset.mul_sum, H.sum_ε]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hin, hpq, mul_one, he0]
  have hunit : ∃ r i, IsUnit (t r i) := by
    by_contra hcon
    push Not at hcon
    have : ∑ r, ∑ i, t r i ∈ nonunits hp.1.Corner :=
      Finset.sum_induction _ (· ∈ nonunits _) (fun _ _ ha hb ↦ IsLocalRing.nonunits_add ha hb)
        (zero_mem_nonunits.2 zero_ne_one) fun r _ ↦
          Finset.sum_induction _ (· ∈ nonunits _) (fun _ _ ha hb ↦ IsLocalRing.nonunits_add ha hb)
            (zero_mem_nonunits.2 zero_ne_one) fun i _ ↦ hcon r i
    rw [hsum] at this
    exact this isUnit_one
  obtain ⟨r, i, ⟨w, hw⟩⟩ := hunit
  set x := f0 * p r * ε he b i
  set y := ε he b i * q r * f0
  set W := cornerVal hp.1 (w⁻¹ : hp.1.Cornerˣ).1
  have hxy : cornerVal hp.1 (t r i) = x * y := by
    simp only [t, x, y]
    calc f0 * (p r * ε he b i * q r) * f0 = f0 * p r * (ε he b i * ε he b i) * q r * f0 := by
          rw [H.ε_idem]; simp only [mul_assoc]
      _ = f0 * p r * ε he b i * (ε he b i * q r * f0) := by simp only [mul_assoc]
  have h1 : x * y * W = f0 := by
    have := congrArg (cornerVal hp.1) w.mul_inv
    rwa [corner_mul_val, hw, hxy, corner_one_val] at this
  have h2 : W * (x * y) = f0 := by
    have := congrArg (cornerVal hp.1) w.inv_mul
    rwa [corner_mul_val, hw, hxy, corner_one_val] at this
  have hWf : W * f0 = W := corner_mul_right hp.1 _
  set g := y * W * x
  have hg : IsIdempotentElem g := by
    change y * W * x * (y * W * x) = y * W * x
    calc y * W * x * (y * W * x) = y * W * (x * y * W) * x := by simp only [mul_assoc]
      _ = y * W * x := by rw [h1, mul_assoc y W f0, hWf]
  have hεg : ε he b i * g = g := by simp only [g, y, ← mul_assoc, H.ε_idem]
  have hgε : g * ε he b i = g := by simp only [g, x, mul_assoc, H.ε_idem]
  have hg0 : g ≠ 0 := by
    intro h0
    apply hp.2.1
    calc f0 = (x * y * W) * (x * y * W) := by rw [h1, hp.1.eq]
      _ = x * g * y * W := by simp only [g, mul_assoc]
      _ = 0 := by rw [h0]; simp
  refine ⟨i, x, y * W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [x, ← mul_assoc, hp.1.eq]
  · simp only [x, mul_assoc, H.ε_idem]
  · simp only [y, ← mul_assoc, H.ε_idem]
  · rw [mul_assoc, hWf]
  · rw [← mul_assoc, h1]
  · rcases (H.ε_primitive i).2.2 g hg hεg hgε with h | h
    · exact absurd h hg0
    · exact h

end Hyp

/-- The matching data: a complete set `f_s` of primitive orthogonal idempotents of
`A`, with `f_s A ≅ e_{σ s} A` given by `u_s`, `v_s`. -/
structure Match (H : Hyp he b E) where
  n : ℕ
  f : Fin n → A
  hf : CompleteOrthogonalIdempotents f
  prim : ∀ s, IsPrimitiveIdempotent (f s)
  σ : Fin n → E
  u : Fin n → A
  v : Fin n → A
  fu : ∀ s, f s * u s = u s
  uε : ∀ s, u s * ε he b (σ s) = u s
  εv : ∀ s, ε he b (σ s) * v s = v s
  vf : ∀ s, v s * f s = v s
  uv : ∀ s, u s * v s = f s
  vu : ∀ s, v s * u s = ε he b (σ s)

namespace Hyp

variable (H : Hyp he b E)

include H in
theorem nonempty_match (hfull : (1 : A) ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}) :
    Nonempty (Match H) := by
  obtain ⟨n, f, hf, hp⟩ := exists_primitive_decomposition k A
  choose σ u v h using fun s ↦ H.exists_match hfull (hp s)
  exact ⟨⟨n, f, hf, hp, σ, u, v, fun s ↦ (h s).1, fun s ↦ (h s).2.1, fun s ↦ (h s).2.2.1,
    fun s ↦ (h s).2.2.2.1, fun s ↦ (h s).2.2.2.2.1, fun s ↦ (h s).2.2.2.2.2⟩⟩

end Hyp

variable (k he) in
/-- The corner projection `a ↦ eae`. -/
def P : A →ₗ[k] he.Corner where
  toFun a := cornerMk he (e * a * e) ⟨a, rfl⟩
  map_add' a a' := corner_ext he (by
    rw [corner_add_val]
    change e * (a + a') * e = e * a * e + e * a' * e
    rw [mul_add, add_mul])
  map_smul' c a := corner_ext he (by
    rw [corner_smul_val (k := k)]
    change e * (c • a) * e = c • (e * a * e)
    rw [mul_smul_comm, smul_mul_assoc])

theorem P_val (a : A) : cornerVal he (P k he a) = e * a * e := rfl

namespace Match

variable {H : Hyp he b E} (M : Match H)

theorem vu_ne {s t : Fin M.n} (h : s ≠ t) : M.v s * M.u t = 0 := by
  rw [← M.vf s, ← M.fu t, mul_assoc, ← mul_assoc (M.f s), M.hf.ortho h, zero_mul, mul_zero]

theorem e_mul_v (s : Fin M.n) : e * M.v s = M.v s := by
  rw [← M.εv s, ← mul_assoc, Hyp.e_mul_ε]

theorem u_mul_e (s : Fin M.n) : M.u s * e = M.u s := by
  rw [← M.uε s, mul_assoc, Hyp.ε_mul_e]

/-- The index set: triples `(s, l, t)` with `b_l ∈ e_{σ s} B₀ e_{σ t}`. -/
def Idx : Type v := {x : Fin M.n × ι × Fin M.n // H.src x.2.1 = M.σ x.1 ∧ H.tgt x.2.1 = M.σ x.2.2}

/-- The basis element `E_{s,t}(b_l) = u_s b_l v_t`. -/
def Eb (x : M.Idx) : A := M.u x.1.1 * bv he b x.1.2.1 * M.v x.1.2.2

/-- `x ↦ u_s x v_t` on `B₀`. -/
def T (s t : Fin M.n) : he.Corner →ₗ[k] A :=
  LinearMap.mulLeft k (M.u s) ∘ₗ LinearMap.mulRight k (M.v t) ∘ₗ cornerValL k he

theorem T_apply (s t : Fin M.n) (x : he.Corner) : M.T s t x = M.u s * cornerVal he x * M.v t := by
  simp [T, cornerValL_apply, mul_assoc]

theorem T_basis (s t : Fin M.n) (l : ι) :
    M.T s t (b l) = 0 ∨ ∃ y : M.Idx, y.1.2.1 = l ∧ M.T s t (b l) = M.Eb y := by
  by_cases h : H.src l = M.σ s ∧ H.tgt l = M.σ t
  · exact Or.inr ⟨⟨(s, l, t), h⟩, rfl, by rw [T_apply]; rfl⟩
  · left
    rw [T_apply]
    change M.u s * bv he b l * M.v t = 0
    rcases not_and_or.1 h with h | h
    · rw [← M.uε s, mul_assoc (M.u s), H.ε_mul_bv, if_neg (Ne.symm h), mul_zero, zero_mul]
    · rw [← M.εv t, mul_assoc, ← mul_assoc (bv he b l), H.bv_mul_ε, if_neg (Ne.symm h), zero_mul,
        mul_zero]

theorem v_Eb_u (y : M.Idx) (s t : Fin M.n) :
    M.v s * M.Eb y * M.u t = if y.1.1 = s ∧ y.1.2.2 = t then bv he b y.1.2.1 else 0 := by
  unfold Eb
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    subst h1 h2
    calc M.v y.1.1 * (M.u y.1.1 * bv he b y.1.2.1 * M.v y.1.2.2) * M.u y.1.2.2
        = (M.v y.1.1 * M.u y.1.1) * bv he b y.1.2.1 * (M.v y.1.2.2 * M.u y.1.2.2) := by
          simp only [mul_assoc]
      _ = bv he b y.1.2.1 := by rw [M.vu, M.vu, ← y.2.1, ← y.2.2, H.src_tgt]
  · rcases not_and_or.1 h with h | h
    · calc M.v s * (M.u y.1.1 * bv he b y.1.2.1 * M.v y.1.2.2) * M.u t
          = (M.v s * M.u y.1.1) * bv he b y.1.2.1 * M.v y.1.2.2 * M.u t := by simp only [mul_assoc]
        _ = 0 := by rw [M.vu_ne (Ne.symm h)]; simp
    · calc M.v s * (M.u y.1.1 * bv he b y.1.2.1 * M.v y.1.2.2) * M.u t
          = M.v s * M.u y.1.1 * bv he b y.1.2.1 * (M.v y.1.2.2 * M.u t) := by simp only [mul_assoc]
        _ = 0 := by rw [M.vu_ne h]; simp

/-- The coordinate of index `y`: `a ↦ (coefficient of b_l in v_s a u_t)`. -/
def κ (y : M.Idx) : A →ₗ[k] k :=
  Finsupp.lapply y.1.2.1 ∘ₗ b.repr.toLinearMap ∘ₗ P k he ∘ₗ LinearMap.mulLeft k (M.v y.1.1) ∘ₗ
    LinearMap.mulRight k (M.u y.1.2.2)

theorem κ_apply (y : M.Idx) (a : A) :
    M.κ y a = b.repr (P k he (M.v y.1.1 * a * M.u y.1.2.2)) y.1.2.1 := by
  simp [κ, mul_assoc]

theorem P_bv (l : ι) : P k he (bv he b l) = b l :=
  corner_ext he (by rw [P_val, Hyp.e_mul_bv, Hyp.bv_mul_e]; rfl)

theorem κ_Eb (x y : M.Idx) : M.κ y (M.Eb x) = if x = y then 1 else 0 := by
  rw [κ_apply, M.v_Eb_u]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos ⟨rfl, rfl⟩, P_bv, Module.Basis.repr_self, Finsupp.single_eq_same, if_pos rfl]
  · rw [if_neg hxy]
    split_ifs with h
    · rw [P_bv, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
      intro hl
      exact hxy (Subtype.ext (Prod.ext h.1 (Prod.ext hl h.2)))
    · rw [map_zero, map_zero, Finsupp.zero_apply]

theorem linearIndependent_Eb : LinearIndependent k M.Eb := by
  refine linearIndependent_iff'.2 fun S g hg y hy ↦ ?_
  have := congrArg (M.κ y) hg
  rw [map_sum, map_zero] at this
  simp_rw [map_smul, κ_Eb, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
  simpa [Finset.sum_ite_eq', hy] using this

theorem decomp (a : A) : a = ∑ s, ∑ t, M.T s t (P k he (M.v s * a * M.u t)) := by
  have h1 : ∀ s t, M.T s t (P k he (M.v s * a * M.u t)) = M.f s * a * M.f t := by
    intro s t
    rw [T_apply, P_val]
    calc M.u s * (e * (M.v s * a * M.u t) * e) * M.v t
        = M.u s * ((e * M.v s) * a * (M.u t * e)) * M.v t := by simp only [mul_assoc]
      _ = (M.u s * M.v s) * a * (M.u t * M.v t) := by
          rw [M.e_mul_v, M.u_mul_e]; simp only [mul_assoc]
      _ = M.f s * a * M.f t := by rw [M.uv, M.uv]
  have h2 : ∀ s, ∑ t, M.f s * a * M.f t = M.f s * a := by
    intro s; rw [← Finset.mul_sum, M.hf.complete, mul_one]
  simp_rw [h1, h2]
  rw [← Finset.sum_mul, M.hf.complete, one_mul]

theorem T_mem_span (s t : Fin M.n) (S : Set ι) (Q : Submodule k A)
    (hQ : ∀ y : M.Idx, y.1.2.1 ∈ S → M.Eb y ∈ Q) {z : he.Corner}
    (hz : z ∈ Submodule.span k (b '' S)) : M.T s t z ∈ Q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      rcases M.T_basis s t l with h | ⟨y, hy, h⟩
      · rw [h]; exact Q.zero_mem
      · rw [h]; exact hQ y (hy ▸ hl)
  | zero => rw [map_zero]; exact Q.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact Q.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Q.smul_mem c hx

theorem span_Eb : ⊤ ≤ Submodule.span k (Set.range M.Eb) := by
  intro a _
  rw [M.decomp a]
  refine Submodule.sum_mem _ fun s _ ↦ Submodule.sum_mem _ fun t _ ↦
    M.T_mem_span s t Set.univ (Submodule.span k (Set.range M.Eb))
      (fun y _ ↦ Submodule.subset_span ⟨y, rfl⟩) ?_
  rw [Set.image_univ, b.span_eq]
  trivial

/-- **The basis `E_{s,t}(b_l)` of `A`.** -/
def basis : Module.Basis M.Idx k A := Module.Basis.mk M.linearIndependent_Eb M.span_Eb

theorem basis_apply (x : M.Idx) : M.basis x = M.Eb x := Module.Basis.mk_apply _ _ _

theorem Eb_mul (x y : M.Idx) :
    M.Eb x * M.Eb y = if x.1.2.2 = y.1.1 then M.T x.1.1 y.1.2.2 (b x.1.2.1 * b y.1.2.1) else 0 := by
  unfold Eb
  split_ifs with h
  · rw [T_apply, corner_mul_val]
    have hb : bv he b x.1.2.1 * (M.v x.1.2.2 * M.u y.1.1) = bv he b x.1.2.1 := by
      rw [← h, M.vu, ← x.2.2, H.mul_tgt]
    calc M.u x.1.1 * bv he b x.1.2.1 * M.v x.1.2.2 * (M.u y.1.1 * bv he b y.1.2.1 * M.v y.1.2.2)
        = M.u x.1.1 * (bv he b x.1.2.1 * (M.v x.1.2.2 * M.u y.1.1)) * bv he b y.1.2.1 *
            M.v y.1.2.2 := by simp only [mul_assoc]
      _ = _ := by rw [hb]; simp only [bv, mul_assoc]
  · calc M.u x.1.1 * bv he b x.1.2.1 * M.v x.1.2.2 * (M.u y.1.1 * bv he b y.1.2.1 * M.v y.1.2.2)
        = M.u x.1.1 * bv he b x.1.2.1 * (M.v x.1.2.2 * M.u y.1.1) * bv he b y.1.2.1 *
            M.v y.1.2.2 := by simp only [mul_assoc]
      _ = 0 := by rw [M.vu_ne h]; simp

theorem basis_isMultiplicative : IsMultiplicativeBasis M.basis := by
  intro x y
  rw [basis_apply, basis_apply, Eb_mul]
  split_ifs
  · rcases H.mul x.1.2.1 y.1.2.1 with h0 | ⟨m, hm⟩
    · left; rw [h0, map_zero]
    · rw [hm]
      rcases M.T_basis x.1.1 y.1.2.2 m with h | ⟨z, -, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨z, by rw [h, basis_apply]⟩
  · exact Or.inl rfl

/-- The index of `E_{s,s}(e_{σ s}) = f_s`. -/
def Fidx (s : Fin M.n) : M.Idx := ⟨(s, (M.σ s).1, s), H.src_ε _, H.tgt_ε _⟩

theorem Eb_Fidx (s : Fin M.n) : M.Eb (M.Fidx s) = M.f s := by
  change M.u s * ε he b (M.σ s) * M.v s = M.f s
  rw [M.uε, M.uv]

theorem Fidx_injective : Function.Injective M.Fidx := fun s s' h ↦ congrArg (fun x ↦ x.1.1) h

/-- The idempotent indices. -/
def Fset : Finset M.Idx := Finset.univ.image M.Fidx

theorem basis_of_mem_Fset {i : M.Idx} (hi : i ∈ M.Fset) : ∃ s, i = M.Fidx s ∧ M.basis i = M.f s := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hi
  exact ⟨s, rfl, by rw [basis_apply, Eb_Fidx]⟩

theorem basis_idempotents : CompleteOrthogonalIdempotents (fun i : M.Fset ↦ M.basis i) := by
  refine ⟨⟨fun i ↦ ?_, fun i j hij ↦ ?_⟩, ?_⟩
  · obtain ⟨s, -, hs⟩ := M.basis_of_mem_Fset i.2
    rw [hs]; exact M.hf.idem s
  · obtain ⟨s, his, hs⟩ := M.basis_of_mem_Fset i.2
    obtain ⟨s', hjs, hs'⟩ := M.basis_of_mem_Fset j.2
    change M.basis i * M.basis j = 0
    rw [hs, hs']
    refine M.hf.ortho fun h ↦ hij (Subtype.ext ?_)
    rw [his, hjs, h]
  · rw [Finset.sum_coe_sort M.Fset (fun i ↦ M.basis i), Fset,
      Finset.sum_image fun s _ s' _ h ↦ M.Fidx_injective h]
    simp_rw [basis_apply, Eb_Fidx]
    exact M.hf.complete

theorem Eb_mem_radPow {n : ℕ} (hn : 1 ≤ n) (y : M.Idx)
    (hy : b y.1.2.1 ∈ algebraRadicalPow k he.Corner n) : M.Eb y ∈ algebraRadicalPow k A n :=
  algebraRadicalPow_mul_right hn _
    (algebraRadicalPow_mul_left hn _ (cornerVal_mem_radPow k he hn hy))

theorem basis_radicalPow (hfull : (1 : A) ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q})
    (n : ℕ) (hn : 1 ≤ n) :
    Submodule.span k (M.basis '' {i | M.basis i ∈ algebraRadicalPow k A n}) =
      algebraRadicalPow k A n := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun a ha ↦ ?_
  · rintro _ ⟨i, hi, rfl⟩; exact hi
  have hQ : ∀ y : M.Idx, y.1.2.1 ∈ {l | b l ∈ algebraRadicalPow k he.Corner n} →
      M.Eb y ∈ Submodule.span k (M.basis '' {i | M.basis i ∈ algebraRadicalPow k A n}) := by
    intro y hy
    have hm : M.basis y ∈ algebraRadicalPow k A n := by
      rw [basis_apply]; exact M.Eb_mem_radPow hn y hy
    rw [← basis_apply]
    exact Submodule.subset_span ⟨y, hm, rfl⟩
  rw [M.decomp a]
  refine Submodule.sum_mem _ fun s _ ↦ Submodule.sum_mem _ fun t _ ↦
    M.T_mem_span s t _ _ hQ ?_
  rw [H.rad n hn]
  obtain ⟨x, hx, hxv⟩ := corner_mem_radPow k he hfull hn ha (M.v s) (M.u t)
  have : P k he (M.v s * a * M.u t) = x := corner_ext he (by
    rw [P_val, ← cornerValL_apply (k := k), hxv]; simp only [mul_assoc])
  rw [this]; exact hx

include M in
/-- **Lemma 2.1.** -/
theorem hasNormedBasis (hfull : (1 : A) ∈ Submodule.span k {x | ∃ p q : A, x = p * e * q}) :
    HasNormedMultiplicativeBasis k A :=
  ⟨M.Idx, M.basis, M.basis_isMultiplicative, ⟨M.Fset, M.basis_idempotents, fun i hi ↦ by
    obtain ⟨s, -, hs⟩ := M.basis_of_mem_Fset hi
    rw [hs]; exact M.prim s⟩, M.basis_radicalPow hfull⟩

end Match

end Nonbasic

end MultiplicativeBasisDeformations
