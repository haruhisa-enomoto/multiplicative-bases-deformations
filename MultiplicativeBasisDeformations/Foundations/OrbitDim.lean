import MultiplicativeBasisDeformations.Foundations.KrullTrdeg

/-!
# Lemma 8.8, geometric part: finitely many orbits cannot cover a large zero set

`local-ray-geometry.tex` (`lem:dimension-infinity`): "The representation variety is
a nonempty zero set of at most `F` scalar polynomial equations in affine `N`-space; the zero
arrow assignment is a point. Every component of such a zero set has dimension at least
`N − F`. The change-of-basis group has dimension `D`, and its simultaneous scalar subgroup
stabilizes every representation. An orbit has dimension equal to that of the group minus
that of the stabilizer, so each orbit has dimension at most `D − 1`. The variety cannot be a
finite union of these orbits."

Setting: arrows `a : s a → t a` between vertices with dimensions `d`, representation space of
matrices `x_a ∈ k^{d(t a) × d(s a)}`, the group `∏ GL_{d v}` acting by `x_a ↦ g_{t a} x_a g_{s a}⁻¹`.
Formalization of the dimension count:
* (step 1) the zero set `X` of `F` polynomials vanishing at `0`: `dim k[x]/I ≥ N − F` by
  Krull's height theorem at the origin, whose height is `N` (a chain of coordinate primes);
* (step 2) an orbit is covered by the images of the charts `g_c = 1` of the group (scalar
  invariance), each a localization of a polynomial ring in `D − 1` variables; the vanishing
  ideal `J_{x,c}` of a chart image is prime and `dim k[x]/J_{x,c} ≤ D − 1` (Noether
  normalization and transcendence degree);
* (step 3) by the Nullstellensatz a prime over `I` contains some `J_{x,c}`, so
  `dim k[x]/I ≤ D − 1`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace OrbitDim

open MvPolynomial

/-! ### Step 1: the height of the origin and Krull's height theorem -/

section Step1

variable {k : Type*} [Field k] {σ : Type} [Fintype σ] [DecidableEq σ]

/-- Kill the variables of index below `j`. -/
def killBelow (e : σ ≃ Fin (Fintype.card σ)) (j : ℕ) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun c ↦ if (e c : ℕ) < j then 0 else X c

/-- The coordinate primes. -/
def Pj (e : σ ≃ Fin (Fintype.card σ)) (j : ℕ) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (killBelow e j).toRingHom

theorem Pj_isPrime (e : σ ≃ Fin (Fintype.card σ)) (j : ℕ) : (Pj (k := k) e j).IsPrime :=
  RingHom.ker_isPrime _

theorem killBelow_comp (e : σ ≃ Fin (Fintype.card σ)) (j : ℕ) :
    (killBelow (k := k) e (j + 1)).comp (killBelow e j) = killBelow e (j + 1) := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [killBelow, AlgHom.comp_apply, aeval_X]
  split_ifs with h1 h2 <;> simp_all [aeval_X] <;> omega

theorem Pj_lt (e : σ ≃ Fin (Fintype.card σ)) (j : ℕ) (hj : j < Fintype.card σ) :
    Pj (k := k) e j < Pj e (j + 1) := by
  refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
  · change killBelow e (j + 1) f = 0
    rw [← killBelow_comp e j, AlgHom.comp_apply]
    change killBelow e j f = 0 at hf
    rw [hf, map_zero]
  · set c := e.symm ⟨j, hj⟩
    have h1 : X c ∈ Pj (k := k) e (j + 1) := by
      change killBelow e (j + 1) (X c) = 0
      simp [killBelow, c]
    rw [← h] at h1
    change killBelow e j (X c) = 0 at h1
    simp [killBelow, c] at h1

theorem killBelow_top (e : σ ≃ Fin (Fintype.card σ)) (f : MvPolynomial σ k) :
    killBelow e (Fintype.card σ) f = C (eval 0 f) := by
  have : killBelow (k := k) e (Fintype.card σ) = (Algebra.ofId k (MvPolynomial σ k)).comp
      (aeval (0 : σ → k)) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp [killBelow, (e c).isLt]
  rw [this]; simp [MvPolynomial.coe_aeval_eq_eval]

/-- **The height of the origin is at least the number of variables.** -/
theorem height_origin_ge (e : σ ≃ Fin (Fintype.card σ)) :
    (Fintype.card σ : ℕ∞) ≤ (Pj (k := k) e (Fintype.card σ)).height := by
  have := height_ge_of_chain (Fintype.card σ) (fun i : Fin (Fintype.card σ + 1) ↦ Pj (k := k) e i)
    (fun i ↦ Pj_isPrime e i) (fun i ↦ Pj_lt e i i.isLt)
  simpa using this

theorem mem_Pj_top (e : σ ≃ Fin (Fintype.card σ)) {f : MvPolynomial σ k} (hf : eval 0 f = 0) :
    f ∈ Pj (k := k) e (Fintype.card σ) := by
  change killBelow e (Fintype.card σ) f = 0
  rw [killBelow_top, hf, map_zero]

/-- **Step 1**: the zero set of `F` polynomials vanishing at the origin has dimension at
least `N − F`. -/
theorem dim_quot_ge {F : ℕ} (f : Fin F → MvPolynomial σ k) (hf : ∀ i, eval 0 (f i) = 0) :
    (Fintype.card σ : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial σ k ⧸ Ideal.span (Set.range f)) + F := by
  set e := Fintype.equivFin σ
  have hle : Ideal.span (Set.range f) ≤ Pj (k := k) e (Fintype.card σ) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_Pj_top e (hf i)
  haveI := Pj_isPrime (k := k) e (Fintype.card σ)
  have h1 := height_le_ringKrullDim_quotient_add_spanFinrank hle
  have h2 : (Ideal.span (Set.range f)).spanFinrank ≤ F := by
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPolynomial σ k)
      (Set.finite_range f)
    refine this.trans ?_
    calc (Set.range f).ncard ≤ (Set.univ : Set (Fin F)).ncard := by
          rw [← Set.image_univ]; exact Set.ncard_image_le (Set.finite_univ)
      _ = F := by simp
  have h3 := height_origin_ge (k := k) e
  calc (Fintype.card σ : WithBot ℕ∞) = ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ (Pj (k := k) e (Fintype.card σ)).height := by exact_mod_cast h3
    _ ≤ _ := h1
    _ ≤ _ := by gcongr

end Step1

/-! ### Step 2: charts of an orbit -/

section Charts

variable {k : Type*} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
  {α : Type} [Fintype α] (s t : α → ι)

/-- The coordinates of the representation space. -/
abbrev Coord := Σ a : α, Fin (d (t a)) × Fin (d (s a))

/-- The coordinates of the group. -/
abbrev GC := Σ v : ι, Fin (d v) × Fin (d v)

variable {d s t}

/-- The matrix of an arrow. -/
def mat (x : Coord d s t → k) (a : α) : Matrix (Fin (d (t a))) (Fin (d (s a))) k :=
  fun i j ↦ x ⟨a, i, j⟩

/-- **The action of `∏ GL_{d v}`.** -/
def act (g : ∀ v, GL (Fin (d v)) k) (x : Coord d s t → k) : Coord d s t → k :=
  fun co ↦ ((g (t co.1)).val * mat x co.1 * ((g (s co.1))⁻¹).val) co.2.1 co.2.2

theorem mat_act (g : ∀ v, GL (Fin (d v)) k) (x : Coord d s t → k) (a : α) :
    mat (act g x) a = (g (t a)).val * mat x a * ((g (s a))⁻¹).val := rfl

theorem act_act (g h : ∀ v, GL (Fin (d v)) k) (x : Coord d s t → k) :
    act g (act h x) = act (g * h) x := by
  funext co
  change ((g (t co.1)).val * mat (act h x) co.1 * ((g (s co.1))⁻¹).val) co.2.1 co.2.2 = _
  rw [mat_act]
  simp only [act, Pi.mul_apply, Units.val_mul, mul_inv_rev, Matrix.mul_assoc]

theorem act_one (x : Coord d s t → k) : act (1 : ∀ v, GL (Fin (d v)) k) x = x := by
  funext co
  simp only [act, Pi.one_apply, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rfl

variable (c : GC d)

/-- The variables of the chart `c`: the group coordinates other than `c`. -/
abbrev Var := {e : GC d // e ≠ c}

variable (k) in
/-- The generic matrix of the chart, with `1` at `c`. -/
def Gm (v : ι) : Matrix (Fin (d v)) (Fin (d v)) (MvPolynomial (Var c) k) :=
  fun i j ↦ if h : (⟨v, i, j⟩ : GC d) = c then 1 else X ⟨⟨v, i, j⟩, h⟩

variable (k) in
/-- The product of the determinants. -/
def δ : MvPolynomial (Var c) k := ∏ v, (Gm k c v).det

/-- The specialized matrices. -/
def gm (pt : Var c → k) (v : ι) : Matrix (Fin (d v)) (Fin (d v)) k :=
  fun i j ↦ if h : (⟨v, i, j⟩ : GC d) = c then 1 else pt ⟨⟨v, i, j⟩, h⟩

theorem map_Gm (pt : Var c → k) (v : ι) : (Gm k c v).map (eval pt) = gm c pt v := by
  ext i j
  simp only [Matrix.map_apply, Gm, gm]
  split_ifs <;> simp

theorem eval_δ (pt : Var c → k) : eval pt (δ k c) = ∏ v, (gm c pt v).det := by
  simp only [δ, map_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [RingHom.map_det, ← map_Gm]
  rfl

/-- A point of the chart where all specialized matrices have determinant one. -/
def pt0 : Var c → k := fun e ↦ if e.1.2.1 = e.1.2.2 then 1 else 0

theorem det_gm_pt0 (v : ι) : (gm c (pt0 c) v).det = (1 : k) := by
  obtain ⟨v0, i0, j0⟩ := c
  by_cases hv : v = v0
  · subst hv
    by_cases hij : i0 = j0
    · subst hij
      have : gm (k := k) ⟨v, i0, i0⟩ (pt0 _) v = 1 := by
        ext i j
        simp only [gm, pt0, Matrix.one_apply]
        split_ifs with h1 h2 <;> simp_all [Sigma.mk.inj_iff]
      rw [this, Matrix.det_one]
    · have : gm (k := k) ⟨v, i0, j0⟩ (pt0 _) v = Matrix.transvection i0 j0 1 := by
        ext i j
        simp only [gm, pt0, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
          Matrix.single_apply]
        split_ifs <;> simp_all [Sigma.mk.inj_iff]
      rw [this, Matrix.det_transvection_of_ne _ _ hij]
  · have : gm (k := k) ⟨v0, i0, j0⟩ (pt0 _) v = 1 := by
      ext i j
      simp only [gm, pt0, Matrix.one_apply]
      split_ifs with h1 h2 <;> simp_all [Sigma.mk.inj_iff]
    rw [this, Matrix.det_one]

theorem δ_ne_zero : δ k c ≠ 0 := fun h ↦ by
  have := eval_δ (k := k) c (pt0 c)
  rw [h, map_zero] at this
  simp only [det_gm_pt0, Finset.prod_const_one] at this
  exact zero_ne_one this

/-- The chart ring. -/
abbrev Rc := Localization.Away (δ k c)

theorem isUnit_det (v : ι) : IsUnit (algebraMap _ (Rc (k := k) c) (Gm k c v).det) := by
  have hdvd : (Gm k c v).det ∣ δ k c :=
    Finset.dvd_prod_of_mem (fun v ↦ (Gm k c v).det) (Finset.mem_univ v)
  exact isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit (δ k c))

variable (k) in
/-- **The chart map of the orbit of `x`**: `x_a ↦ G_{t a} x_a G_{s a}⁻¹` for the generic matrices. -/
def Ψ (x : Coord d s t → k) : MvPolynomial (Coord d s t) k →ₐ[k] Rc (k := k) c :=
  aeval fun co ↦ ((Gm k c (t co.1)).map (algebraMap _ (Rc (k := k) c)) *
      (mat x co.1).map (algebraMap k (Rc (k := k) c)) *
      ((Gm k c (s co.1)).map (algebraMap _ (Rc (k := k) c))).adjugate) co.2.1 co.2.2 *
    ↑(isUnit_det (k := k) c (s co.1)).unit⁻¹

theorem isUnit_aeval_pow (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0)
    (y : Submonoid.powers (δ k c)) : IsUnit (aeval pt (y : MvPolynomial (Var c) k)) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  change IsUnit (eval pt (δ k c) ^ n)
  exact (hpt.isUnit).pow n

/-- Evaluation at a point of the chart. -/
def ev (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) : Rc (k := k) c →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (δ k c)) (f := aeval pt)
    (isUnit_aeval_pow c pt hpt)

theorem ev_algebraMap (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) (P : MvPolynomial (Var c) k) :
    ev c pt hpt (algebraMap _ (Rc (k := k) c) P) = eval pt P := by
  rw [ev, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem det_gm_ne (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) (v : ι) : (gm c pt v).det ≠ 0 := by
  rw [eval_δ] at hpt
  exact Finset.prod_ne_zero_iff.1 hpt v (Finset.mem_univ v)

/-- The group element of a chart point. -/
def grp (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) : ∀ v, GL (Fin (d v)) k :=
  fun v ↦ Matrix.GeneralLinearGroup.mkOfDetNeZero (gm c pt v) (det_gm_ne c pt hpt v)

theorem ev_unitInv (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) (v : ι) :
    ev c pt hpt ↑(isUnit_det (k := k) c v).unit⁻¹ = ((gm c pt v).det)⁻¹ := by
  have h1 : ev c pt hpt ↑(isUnit_det (k := k) c v).unit⁻¹ * ev c pt hpt
      ↑(isUnit_det (k := k) c v).unit = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ev c pt hpt ↑(isUnit_det (k := k) c v).unit = (gm c pt v).det := by
    rw [IsUnit.unit_spec, ev_algebraMap, RingHom.map_det, ← map_Gm]; rfl
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem map_ev_Gm (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) (v : ι) :
    ((Gm k c v).map (algebraMap _ (Rc (k := k) c))).map (ev c pt hpt) = gm c pt v := by
  rw [Matrix.map_map, ← map_Gm]
  congr 1; funext P; exact ev_algebraMap c pt hpt P

/-- **Evaluating the chart map** gives the action of the chart's group element. -/
theorem ev_Ψ (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0) (x : Coord d s t → k)
    (f : MvPolynomial (Coord d s t) k) :
    ev c pt hpt (Ψ k c x f) = eval (act (grp c pt hpt) x) f := by
  have key : (ev c pt hpt).comp (Ψ k c x) = aeval (act (grp c pt hpt) x) := by
    apply MvPolynomial.algHom_ext
    intro co
    rw [AlgHom.comp_apply, Ψ, aeval_X, aeval_X, map_mul, ev_unitInv]
    have hm : ∀ {m n p : Type} [Fintype n] [Fintype p] (A : Matrix m n (Rc (k := k) c))
        (B : Matrix n p (Rc (k := k) c)) (i : m) (j : p),
        ev c pt hpt ((A * B) i j) = (A.map (ev c pt hpt) * B.map (ev c pt hpt)) i j := by
      intro m n p _ _ A B i j
      rw [← Matrix.map_mul]; rfl
    have hadj : ((Gm k c (s co.1)).map (algebraMap _ (Rc (k := k) c))).adjugate.map
        (ev c pt hpt) = (gm c pt (s co.1)).adjugate := by
      rw [← map_ev_Gm c pt hpt (s co.1)]
      simpa [AlgHom.mapMatrix_apply] using (AlgHom.map_adjugate (ev c pt hpt)
        ((Gm k c (s co.1)).map (algebraMap _ (Rc (k := k) c))))
    have hx : ((mat x co.1).map (algebraMap k (Rc (k := k) c))).map (ev c pt hpt) = mat x co.1 := by
      ext i j; simp
    rw [hm, Matrix.map_mul, map_ev_Gm, hadj, hx]
    change _ = ((gm c pt (t co.1)) * mat x co.1 *
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero (gm c pt (s co.1)) (det_gm_ne c pt hpt _))⁻¹).val)
        co.2.1 co.2.2
    rw [Matrix.coe_units_inv]
    change _ = ((gm c pt (t co.1)) * mat x co.1 * (gm c pt (s co.1))⁻¹) co.2.1 co.2.2
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul,
      mul_comm]
  rw [← coe_aeval_eq_eval, ← key]; rfl

instance : IsDomain (Rc (k := k) c) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (δ_ne_zero c))

/-- **An element of the chart ring vanishing at all points is zero.** -/
theorem eq_zero_of_ev [Infinite k] (r : Rc (k := k) c)
    (h : ∀ (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0), ev c pt hpt r = 0) : r = 0 := by
  obtain ⟨⟨P, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (δ k c)) r
  have hP : P * δ k c = 0 := by
    apply MvPolynomial.funext; intro pt
    rw [map_mul, map_zero]
    by_cases hpt : eval pt (δ k c) = 0
    · rw [hpt, mul_zero]
    · have h1 := h pt hpt
      rw [ev, IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'] at h1
      have h2 : (aeval pt).toRingHom P = 0 := by
        rcases mul_eq_zero.1 h1 with h3 | h3
        · exact h3
        · exact absurd h3 (Units.ne_zero _)
      change eval pt P = 0 at h2
      rw [h2, zero_mul]
  have : P = 0 := (mul_eq_zero.1 hP).resolve_right (δ_ne_zero c)
  subst this
  simp

variable (k) in
/-- **The vanishing ideal of the chart image of the orbit of `x`.** -/
abbrev J (x : Coord d s t → k) : Ideal (MvPolynomial (Coord d s t) k) :=
  RingHom.ker (Ψ k c x)

instance J_isPrime (x : Coord d s t → k) : (J k c x).IsPrime := RingHom.ker_isPrime _

theorem mem_J_iff [Infinite k] (x : Coord d s t → k) (f : MvPolynomial (Coord d s t) k) :
    f ∈ J k c x ↔ ∀ (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0),
      eval (act (grp c pt hpt) x) f = 0 := by
  constructor
  · intro hf pt hpt
    rw [← ev_Ψ]
    change Ψ k c x f = 0 at hf
    rw [hf, map_zero]
  · intro h
    change Ψ k c x f = 0
    exact eq_zero_of_ev c _ fun pt hpt ↦ by rw [ev_Ψ]; exact h pt hpt

/-- **Charts cover the orbit**: rescaling `g` to have entry one at `c`. -/
theorem exists_chart_pt (g : ∀ v, GL (Fin (d v)) k) (hc : (g c.1).val c.2.1 c.2.2 ≠ 0)
    (x : Coord d s t → k) :
    ∃ (pt : Var c → k) (hpt : eval pt (δ k c) ≠ 0), act g x = act (grp c pt hpt) x := by
  set lam := (g c.1).val c.2.1 c.2.2
  set pt : Var c → k := fun e ↦ lam⁻¹ * (g e.1.1).val e.1.2.1 e.1.2.2
  have hgm : ∀ v, gm c pt v = lam⁻¹ • (g v).val := by
    intro v
    ext i j
    simp only [gm, pt, Matrix.smul_apply, smul_eq_mul]
    split_ifs with h
    · subst h; exact (inv_mul_cancel₀ hc).symm
    · rfl
  have hdet : ∀ v, (gm c pt v).det ≠ 0 := by
    intro v
    rw [hgm, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) ((g v).isUnit.map Matrix.detMonoidHom).ne_zero
  have hpt : eval pt (δ k c) ≠ 0 := by
    rw [eval_δ]; exact Finset.prod_ne_zero_iff.2 fun v _ ↦ hdet v
  refine ⟨pt, hpt, ?_⟩
  funext co
  change _ = ((gm c pt (t co.1)) * mat x co.1 *
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero (gm c pt (s co.1)) (det_gm_ne c pt hpt _))⁻¹).val)
        co.2.1 co.2.2
  rw [Matrix.coe_units_inv]
  change _ = ((gm c pt (t co.1)) * mat x co.1 * (gm c pt (s co.1))⁻¹) co.2.1 co.2.2
  have hu : IsUnit ((g (s co.1)).val).det := (g (s co.1)).isUnit.map Matrix.detMonoidHom
  have hinv : (lam⁻¹ • (g (s co.1)).val)⁻¹ = lam • ((g (s co.1))⁻¹).val := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  rw [hgm, hgm, hinv]
  simp only [act, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  exact (mul_inv_cancel_left₀ hc _).symm

/-- Every invertible family has a nonzero entry. -/
theorem exists_nonzero_entry (hd : ∃ v, 0 < d v) (g : ∀ v, GL (Fin (d v)) k) :
    ∃ c : GC d, (g c.1).val c.2.1 c.2.2 ≠ 0 := by
  obtain ⟨v, hv⟩ := hd
  by_contra h
  push Not at h
  have h0 : (g v).val = 0 := by ext i j; exact h ⟨v, i, j⟩
  have hu : IsUnit ((g v).val).det := (g v).isUnit.map Matrix.detMonoidHom
  haveI : Nonempty (Fin (d v)) := ⟨⟨0, hv⟩⟩
  rw [h0, Matrix.det_zero] at hu
  exact not_isUnit_zero hu

end Charts

/-! ### Step 3: the count -/

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
  {α : Type} [Fintype α] {s t : α → ι}

theorem card_var (c : GC d) : Fintype.card (Var c) = Fintype.card (GC d) - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

set_option maxHeartbeats 2000000 in
/-- **The chart image of an orbit has dimension at most `D − 1`.** -/
theorem dim_J_le (c : GC d) (x : Coord d s t → k) :
    ringKrullDim (MvPolynomial (Coord d s t) k ⧸ J k c x) ≤ ((Fintype.card (GC d) - 1 : ℕ) : WithBot ℕ∞) := by
  rw [← card_var c]
  haveI : Nontrivial (MvPolynomial (Coord d s t) k ⧸ J k c x) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  haveI : Algebra.FiniteType k (MvPolynomial (Coord d s t) k ⧸ J k c x) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _) (Ideal.Quotient.mkₐ_surjective k _)
  refine ringKrullDim_le_of_noether k _ _ fun n g hg ↦ ?_
  have hinj := (Ideal.kerLiftAlg_injective (Ψ k c x)).comp hg
  exact card_le_of_inj_localization k (δ k c) (δ_ne_zero c)
    ((Ideal.kerLiftAlg (Ψ k c x)).comp g) hinj

theorem withBot_aux (a : WithBot ℕ∞) (N F D : ℕ) (h1 : (N : WithBot ℕ∞) ≤ a + F)
    (h2 : D + F ≤ N) : (D : WithBot ℕ∞) ≤ a := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h1
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact le_top.trans (le_of_eq rfl)
    | coe n =>
      have : N ≤ n + F := by exact_mod_cast h1
      exact_mod_cast (by omega : D ≤ n)

/-- **Lemma 8.8, geometric part**: the zero set of `F` polynomials vanishing at the origin
and stable under `∏ GL_{d v}`, in `N` coordinates with `N ≥ D + F`, is not a finite union
of orbits. -/
theorem orbits_not_finite (F : ℕ) (f : Fin F → MvPolynomial (Coord d s t) k)
    (hf0 : ∀ i, eval 0 (f i) = 0)
    (hstab : ∀ (g : ∀ v, GL (Fin (d v)) k) (x : Coord d s t → k),
      (∀ i, eval x (f i) = 0) → ∀ i, eval (act g x) (f i) = 0)
    (hd : ∃ v, 0 < d v) (hN : Fintype.card (GC d) + F ≤ Fintype.card (Coord d s t))
    (S : Finset (Coord d s t → k))
    (hS : ∀ y, (∀ i, eval y (f i) = 0) → ∃ x ∈ S, ∃ g, y = act g x) : False := by
  classical
  set I : Ideal (MvPolynomial (Coord d s t) k) := Ideal.span (Set.range f)
  set D := Fintype.card (GC d)
  have hD1 : 1 ≤ D := by
    obtain ⟨v, hv⟩ := hd
    exact Fintype.card_pos_iff.2 ⟨⟨v, ⟨0, hv⟩, ⟨0, hv⟩⟩⟩
  have hdim : (D : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Coord d s t) k ⧸ I) :=
    withBot_aux _ _ F D (dim_quot_ge f hf0) hN
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hdim
  set P := (l 0).asIdeal.comap (Ideal.Quotient.mk I)
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hIP : I ≤ P := fun a ha ↦ by
    change Ideal.Quotient.mk I a ∈ (l 0).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact zero_mem _
  set T := S ×ˢ (Finset.univ : Finset (GC d))
  have hprod : T.prod (fun xc ↦ J k xc.2 xc.1) ≤ P := by
    intro h hh
    rw [← (inferInstance : P.IsPrime).radical, ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) P]
    intro y hy
    have hyX : ∀ i, eval y (f i) = 0 := fun i ↦ by
      exact hy (f i) (hIP (Ideal.subset_span ⟨i, rfl⟩))
    obtain ⟨x, hxS, g, rfl⟩ := hS y hyX
    obtain ⟨c, hc⟩ := exists_nonzero_entry hd g
    obtain ⟨pt, hpt, hact⟩ := exists_chart_pt c g hc x
    have h1 : T.prod (fun xc ↦ J k xc.2 xc.1) ≤ J k c x := by
      have hmem : (x, c) ∈ T := Finset.mem_product.2 ⟨hxS, Finset.mem_univ c⟩
      rw [← Finset.mul_prod_erase T (fun xc ↦ J k xc.2 xc.1) hmem]
      exact Ideal.mul_le_left (R := MvPolynomial (Coord d s t) k) (I := J k c x)
    change eval (act g x) h = 0
    rw [hact]
    exact (mem_J_iff c x h).1 (h1 hh) pt hpt
  obtain ⟨⟨x, c⟩, -, hJP⟩ := (Ideal.IsPrime.prod_le inferInstance).1 hprod
  -- a chain of length `D` in `k[x]/J`
  have hle : ∀ i, J k c x ≤ (l i).asIdeal.comap (Ideal.Quotient.mk I) := fun i ↦
    hJP.trans (Ideal.comap_mono (l.monotone (Fin.zero_le i)))
  let m : Fin (l.length + 1) → PrimeSpectrum (MvPolynomial (Coord d s t) k ⧸ J k c x) := fun i ↦
    ⟨((l i).asIdeal.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk (J k c x)),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle i)⟩
  have hm : StrictMono m := by
    intro i j hij
    have hlt : l i < l j := l.strictMono hij
    have h1 : (l i).asIdeal.comap (Ideal.Quotient.mk I) < (l j).asIdeal.comap (Ideal.Quotient.mk I) := by
      refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun h ↦ hlt.ne ?_
      apply PrimeSpectrum.ext
      have := congrArg (Ideal.map (Ideal.Quotient.mk I)) h
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
    change (m i).asIdeal < (m j).asIdeal
    refine lt_of_le_of_ne (Ideal.map_mono h1.le) fun h ↦ h1.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk (J k c x))) h
    simp only [m] at this
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 (hle i), sup_eq_left.2 (hle j)] at this
  have hlow : (D : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Coord d s t) k ⧸ J k c x) := by
    rw [← hl]
    exact Order.le_krullDim_iff.2 ⟨LTSeries.mk l.length m hm, rfl⟩
  have := hlow.trans (dim_J_le c x)
  have : D ≤ D - 1 := by exact_mod_cast this
  omega

end Main

end OrbitDim

end MultiplicativeBasisDeformations
