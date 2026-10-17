import MultiplicativeBasisDeformations.Foundations.BarComplex

/-!
# Graded modules and graded `Ext` via the bar complex

Section 6 (`positive-deformations.tex`): "Internal degree `t` in
`Hom` or `Ext` means maps from a graded projective resolution to the target which
raise degree by `t`", computed by the bar resolution. Here graded `Ext^n_t(M, N)`
is the cohomology of the bar complex `Hom_R(M ⊗ Λ^{⊗n}, N)` in internal degree
`t` (`Good`, `ExtVanish`), for graded right modules over a graded `R`-algebra
`Λ` (`R` a commutative ring: a field, or `ℤ/4` in Section 10).

The bar complex is taken over `R` rather than relative to `S`; both compute `Ext`
(`weights-and-parameters.tex` for the relative form). That it computes the manuscript's
`Ext` is proved in `ExtResolutions.lean`: for every graded projective resolution, the `Ext`
computed from it vanishes exactly when the bar `Ext` does (`GRes.extVanish_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R]

/-- A `ℤ`-grading of an `R`-module by finitely supported projections. -/
structure ZGr (M : Type*) [AddCommGroup M] [Module R M] where
  proj : ℤ → M →ₗ[R] M
  supp : Finset ℤ
  proj_proj : ∀ p q m, proj p (proj q m) = if q = p then proj q m else 0
  proj_out : ∀ p, p ∉ supp → proj p = 0
  sum : ∀ m, m = ∑ p ∈ supp, proj p m

namespace ZGr

variable {M : Type*} [AddCommGroup M] [Module R M] (g : ZGr (R := R) M)

/-- A homogeneous element. -/
def IsHom (p : ℤ) (m : M) : Prop := g.proj p m = m

theorem isHom_proj (p : ℤ) (m : M) : g.IsHom p (g.proj p m) := by
  unfold IsHom; rw [g.proj_proj, if_pos rfl]

theorem proj_of_isHom {p q : ℤ} {m : M} (h : g.IsHom p m) : g.proj q m = if p = q then m else 0 := by
  rw [← h, g.proj_proj, h]

theorem isHom_add {p : ℤ} {m m' : M} (h : g.IsHom p m) (h' : g.IsHom p m') : g.IsHom p (m + m') := by
  unfold IsHom; rw [map_add, h, h']

theorem isHom_smul {p : ℤ} (c : R) {m : M} (h : g.IsHom p m) : g.IsHom p (c • m) := by
  unfold IsHom; rw [map_smul, h]

theorem isHom_zero (p : ℤ) : g.IsHom p (0 : M) := by unfold IsHom; rw [map_zero]

theorem isHom_neg {p : ℤ} {m : M} (h : g.IsHom p m) : g.IsHom p (-m) := by
  unfold IsHom; rw [map_neg, h]

theorem isHom_sum {p : ℤ} {ι : Type*} (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, g.IsHom p (f i)) :
    g.IsHom p (∑ i ∈ s, f i) := by
  unfold IsHom; rw [map_sum]; exact Finset.sum_congr rfl h

theorem eq_zero_of_isHom_out {p : ℤ} {m : M} (h : g.IsHom p m) (hp : p ∉ g.supp) : m = 0 := by
  rw [← h, g.proj_out p hp, LinearMap.zero_apply]

/-- Linear maps that agree on homogeneous elements agree. -/
theorem ext_of_hom {N : Type*} [AddCommGroup N] [Module R N] {f f' : M →ₗ[R] N}
    (h : ∀ p m, g.IsHom p m → f m = f' m) : f = f' := by
  ext m
  rw [g.sum m, map_sum, map_sum]
  exact Finset.sum_congr rfl fun p _ ↦ h p _ (g.isHom_proj p m)

end ZGr

variable {Λ : Type*} [Ring Λ] [Algebra R Λ]

/-- A graded algebra. -/
structure GAlg (Λ : Type*) [Ring Λ] [Algebra R Λ] where
  gr : ZGr (R := R) Λ
  mul_hom : ∀ p q a b, gr.IsHom p a → gr.IsHom q b → gr.IsHom (p + q) (a * b)
  one_hom : gr.IsHom 0 (1 : Λ)

variable (GΛ : GAlg (R := R) Λ)

/-- A graded right `Λ`-module. -/
structure GMod (M : Type*) [AddCommGroup M] [Module R M] where
  act : M →ₗ[R] Λ →ₗ[R] M
  act_one : ∀ m, act m 1 = m
  act_mul : ∀ m a b, act (act m a) b = act m (a * b)
  gr : ZGr (R := R) M
  act_hom : ∀ p q m a, gr.IsHom p m → GΛ.gr.IsHom q a → gr.IsHom (p + q) (act m a)

variable {GΛ}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The bimodule `Hom_R(M, N)`: `(a·φ)(m) = φ(ma)`, `(φ·b)(m) = φ(m)b`. -/
def homAct (MM : GMod GΛ M) (NN : GMod GΛ N) : Bar.Act Λ (M →ₗ[R] N) where
  l a :=
    { toFun := fun φ ↦ (φ ∘ₗ MM.act.flip a)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  r b :=
    { toFun := fun φ ↦ (NN.act.flip b ∘ₗ φ)
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp }
  l_mul a b φ := by ext m; simp [MM.act_mul]
  r_mul a b φ := by ext m; simp [NN.act_mul]
  lr a b φ := rfl

theorem homAct_l (MM : GMod GΛ M) (NN : GMod GΛ N) (a : Λ) (φ : M →ₗ[R] N) (m : M) :
    (homAct MM NN).l a φ m = φ (MM.act m a) := rfl

theorem homAct_r (MM : GMod GΛ M) (NN : GMod GΛ N) (b : Λ) (φ : M →ₗ[R] N) (m : M) :
    (homAct MM NN).r b φ m = NN.act (φ m) b := rfl

open Bar in
/-- **Good cochains**: the bar cochains `M × Λⁿ → N`, `R`-multilinear, of internal
degree `t`. -/
structure Good (MM : GMod GΛ M) (NN : GMod GΛ N) (n : ℕ) (t : ℤ)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) : Prop where
  tr : ∀ a, F a = F (Bar.tr n a)
  add : ∀ a i x y, i < n → F (Function.update a i (x + y)) =
    F (Function.update a i x) + F (Function.update a i y)
  smul : ∀ a i (c : R) x, i < n → F (Function.update a i (c • x)) = c • F (Function.update a i x)
  deg : ∀ (a : ℕ → Λ) (ds : ℕ → ℤ) p m, (∀ i < n, GΛ.gr.IsHom (ds i) (a i)) → MM.gr.IsHom p m →
    NN.gr.IsHom (p + ∑ i ∈ Finset.range n, ds i + t) (F a m)

namespace Good

variable {MM : GMod GΛ M} {NN : GMod GΛ N} {n : ℕ} {t : ℤ}

theorem zero : Good MM NN n t 0 :=
  ⟨fun _ ↦ rfl, fun _ _ _ _ _ ↦ by simp, fun _ _ _ _ _ ↦ by simp,
    fun _ _ _ _ _ _ ↦ NN.gr.isHom_zero _⟩

theorem add' {F G : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN n t F) (hG : Good MM NN n t G) :
    Good MM NN n t (F + G) := by
  refine ⟨fun a ↦ by simp [hF.tr a, hG.tr a], fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_,
    fun a ds p m ha hm ↦ ?_⟩
  · simp only [Pi.add_apply, hF.add a i x y hi, hG.add a i x y hi]; abel
  · simp only [Pi.add_apply, hF.smul a i c x hi, hG.smul a i c x hi, smul_add]
  · simp only [Pi.add_apply, LinearMap.add_apply]
    exact NN.gr.isHom_add (hF.deg a ds p m ha hm) (hG.deg a ds p m ha hm)

theorem zsmul' {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN n t F) (z : ℤ) :
    Good MM NN n t (z • F) := by
  refine ⟨fun a ↦ by simp [hF.tr a], fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_,
    fun a ds p m ha hm ↦ ?_⟩
  · simp only [Pi.smul_apply, hF.add a i x y hi, smul_add]
  · simp only [Pi.smul_apply, hF.smul a i c x hi, smul_comm z c]
  · simp only [Pi.smul_apply, LinearMap.smul_apply]
    rw [← Int.cast_smul_eq_zsmul R]
    exact NN.gr.isHom_smul _ (hF.deg a ds p m ha hm)

theorem sum' {ι : Type*} (s : Finset ι) {F : ι → Bar.Cochain Λ (M →ₗ[R] N)}
    (h : ∀ i ∈ s, Good MM NN n t (F i)) : Good MM NN n t (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : Good MM NN n t 0)
  | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (h j (Finset.mem_insert_self j s)).add' (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end Good

open Bar

theorem sum_range_contract (n p : ℕ) (hp : p < n) (ds : ℕ → ℤ) :
    ∑ k ∈ Finset.range n,
      (if k < p then ds k else if k = p then ds p + ds (p + 1) else ds (k + 1)) =
    ∑ k ∈ Finset.range (n + 1), ds k := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k ↦ ds k) (n + 1)]
      rcases Nat.lt_or_ge p n with h | h
      · rw [ih h, if_neg (by omega), if_neg (by omega)]
      · obtain rfl : p = n := by omega
        rw [if_neg (by omega), if_pos rfl, Finset.sum_range_succ]
        rw [Finset.sum_congr rfl fun k hk ↦ if_pos (Finset.mem_range.1 hk)]
        ring

variable {MM : GMod GΛ M} {NN : GMod GΛ N}

/-- **Cofaces preserve good cochains.** -/
theorem Good.coface {n : ℕ} {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN n t F)
    (j : ℕ) (hj : j ≤ n + 1) : Good MM NN (n + 1) t (Bar.coface (homAct MM NN) n j F) := by
  classical
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- `a₀ · F(a₁, …)`
    refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩
    · rw [coface_zero, coface_zero, sh_tr, ← hF.tr]
      simp [Bar.tr]
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · ext m
        simp only [coface_zero, sh_update_zero, Function.update_self, homAct_l, map_add,
          LinearMap.add_apply]
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_lt hi0
        simp only [coface_zero, zero_add] at *
        rw [sh_update_succ, sh_update_succ, sh_update_succ, hF.add _ _ _ _ (by omega),
          Function.update_apply, if_neg (by omega), Function.update_apply, if_neg (by omega),
          Function.update_apply, if_neg (by omega), map_add]
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · ext m
        rw [coface_zero, coface_zero, sh_update_zero, sh_update_zero, Function.update_self,
          Function.update_self, LinearMap.smul_apply, homAct_l, homAct_l, map_smul (MM.act m),
          map_smul]
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_lt hi0
        simp only [coface_zero, zero_add] at *
        rw [sh_update_succ, sh_update_succ, hF.smul _ _ _ _ (by omega),
          Function.update_apply, if_neg (by omega), Function.update_apply, if_neg (by omega)]
        ext m
        rfl
    · rw [coface_zero, homAct_l]
      have h1 := hF.deg (sh a) (fun i ↦ ds (i + 1)) (p + ds 0) (MM.act m (a 0))
        (fun i hi ↦ ha (i + 1) (by omega)) (MM.act_hom _ _ _ _ hm (ha 0 (by omega)))
      convert h1 using 1
      rw [Finset.sum_range_succ']
      ring
  · rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · -- `F(…, a_p a_{p+1}, …)`
      obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
      have hp : p < n := by omega
      have hc : ∀ a, Bar.coface (homAct MM NN) n (p + 1) F a = F (ct p a) := fun a ↦ by
        rw [coface_mid _ (by omega) (by omega)]; rfl
      refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds q m ha hm ↦ ?_⟩
      · rw [hc, hc, hF.tr, ← ct_tr hp]
      · simp only [hc]
        rcases lt_trichotomy i p with h | rfl | h
        · rw [ct_update_lt h, ct_update_lt h, ct_update_lt h, hF.add _ _ _ _ (by omega)]
        · rw [ct_update_left, ct_update_left, ct_update_left, add_mul,
            hF.add _ _ _ _ hp]
        · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
          · subst h'
            rw [ct_update_right, ct_update_right, ct_update_right, mul_add,
              hF.add _ _ _ _ hp]
          · rw [ct_update_gt h', ct_update_gt h', ct_update_gt h', hF.add _ _ _ _ (by omega)]
      · simp only [hc]
        rcases lt_trichotomy i p with h | rfl | h
        · rw [ct_update_lt h, ct_update_lt h, hF.smul _ _ _ _ (by omega)]
        · rw [ct_update_left, ct_update_left, smul_mul_assoc, hF.smul _ _ _ _ hp]
        · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
          · subst h'
            rw [ct_update_right, ct_update_right, mul_smul_comm, hF.smul _ _ _ _ hp]
          · rw [ct_update_gt h', ct_update_gt h', hF.smul _ _ _ _ (by omega)]
      · rw [hc]
        have h1 := hF.deg (ct p a)
          (fun k ↦ if k < p then ds k else if k = p then ds p + ds (p + 1) else ds (k + 1)) q m
          (fun k hk ↦ by
            simp only [ct]
            split_ifs with h1 h2
            · exact ha k (by omega)
            · subst h2; exact GΛ.mul_hom _ _ _ _ (ha k (by omega)) (ha (k + 1) (by omega))
            · exact ha (k + 1) (by omega)) hm
        rwa [sum_range_contract n p hp] at h1
    · -- `F(a₀, …, a_{n-1}) a_n`
      obtain rfl : j = n + 1 := by omega
      refine ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds q m ha hm ↦ ?_⟩
      · rw [coface_last, coface_last, tr_tr]
        simp [Bar.tr]
      · ext m
        simp only [coface_last, homAct_r, LinearMap.add_apply]
        rcases Nat.lt_or_ge i n with h | h
        · rw [tr_update_lt h, tr_update_lt h, tr_update_lt h, hF.add _ _ _ _ h]
          simp only [Function.update_of_ne (show n ≠ i by omega), LinearMap.add_apply, map_add]
        · obtain rfl : i = n := by omega
          rw [tr_update_ge le_rfl, tr_update_ge le_rfl, tr_update_ge le_rfl]
          simp only [Function.update_self, map_add]
      · ext m
        simp only [coface_last, homAct_r, LinearMap.smul_apply]
        rcases Nat.lt_or_ge i n with h | h
        · rw [tr_update_lt h, tr_update_lt h, hF.smul _ _ _ _ h]
          simp only [Function.update_of_ne (show n ≠ i by omega), LinearMap.smul_apply,
            LinearMap.map_smul₂]
        · obtain rfl : i = n := by omega
          rw [tr_update_ge le_rfl, tr_update_ge le_rfl]
          simp only [Function.update_self, map_smul]
      · rw [coface_last, homAct_r]
        have h1 := hF.deg (Bar.tr n a) ds q m
          (fun k hk ↦ by rw [tr_apply_lt hk]; exact ha k (by omega)) hm
        have h2 := NN.act_hom _ _ _ _ h1 (ha n (by omega))
        convert h2 using 1
        rw [Finset.sum_range_succ]
        ring

/-- **`d` preserves good cochains.** -/
theorem Good.d {n : ℕ} {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN n t F) :
    Good MM NN (n + 1) t (Bar.d (homAct MM NN) n F) := by
  rw [show Bar.d (homAct MM NN) n F = ∑ i ∈ Finset.range (n + 2),
    (-1 : ℤ) ^ i • Bar.coface (homAct MM NN) n i F from Bar.d_apply _ _ _]
  exact Good.sum' _ fun i hi ↦ (hF.coface i (by have := Finset.mem_range.1 hi; omega)).zsmul' _

variable (MM NN) in
/-- **`Ext^{n+1}_t(M, N) = 0`**: every good cocycle is a good coboundary. -/
def ExtVanish (n : ℕ) (t : ℤ) : Prop :=
  ∀ F, Good MM NN (n + 1) t F → Bar.d (homAct MM NN) (n + 1) F = 0 →
    ∃ H, Good MM NN n t H ∧ Bar.d (homAct MM NN) n H = F

/-! ### Pullback along module maps -/

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- Pullback of cochains along `π : M' → M`. -/
def pull (π : M' →ₗ[R] M) (F : Bar.Cochain Λ (M →ₗ[R] N)) : Bar.Cochain Λ (M' →ₗ[R] N) :=
  fun a ↦ F a ∘ₗ π

theorem pull_apply (π : M' →ₗ[R] M) (F : Bar.Cochain Λ (M →ₗ[R] N)) (a : ℕ → Λ) (m : M') :
    pull π F a m = F a (π m) := rfl

theorem pull_add (π : M' →ₗ[R] M) (F G : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull π (F + G) = pull π F + pull π G := rfl

theorem pull_sub (π : M' →ₗ[R] M) (F G : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull π (F - G) = pull π F - pull π G := rfl

theorem pull_comp {M'' : Type*} [AddCommGroup M''] [Module R M''] (π : M' →ₗ[R] M)
    (π' : M'' →ₗ[R] M') (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull π' (pull π F) = pull (π ∘ₗ π') F := rfl

theorem pull_id (F : Bar.Cochain Λ (M →ₗ[R] N)) : pull LinearMap.id F = F := rfl

variable {MM' : GMod GΛ M'}

/-- Pullback along a `Λ`-linear map commutes with the cofaces. -/
theorem coface_pull {π : M' →ₗ[R] M} (hπ : ∀ m a, π (MM'.act m a) = MM.act (π m) a) (n j : ℕ)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    Bar.coface (homAct MM' NN) n j (pull π F) = pull π (Bar.coface (homAct MM NN) n j F) := by
  funext a
  ext m
  simp only [Bar.coface, AddMonoidHom.coe_mk, ZeroHom.coe_mk, pull_apply]
  split_ifs
  · rw [homAct_l, homAct_l, pull_apply, hπ]
  · rfl
  · rfl

/-- Pullback along a `Λ`-linear map commutes with `d`. -/
theorem d_pull {π : M' →ₗ[R] M} (hπ : ∀ m a, π (MM'.act m a) = MM.act (π m) a) (n : ℕ)
    (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    Bar.d (homAct MM' NN) n (pull π F) = pull π (Bar.d (homAct MM NN) n F) := by
  rw [Bar.d_apply, Bar.d_apply]
  simp only [coface_pull hπ]
  funext a
  ext m
  simp [pull_apply, Finset.sum_apply, LinearMap.sum_apply]

/-- Pullback along a map of degree `s` sends good cochains of degree `t` to good
cochains of degree `t + s`. -/
theorem Good.pull {n : ℕ} {t s : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN n t F)
    {π : M' →ₗ[R] M} (hπ : ∀ p m, MM'.gr.IsHom p m → MM.gr.IsHom (p + s) (π m)) :
    Good MM' NN n (t + s) (pull π F) := by
  refine ⟨fun a ↦ by simp only [GExt.pull, ← hF.tr], fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_,
    fun a ds p m ha hm ↦ ?_⟩
  · ext m; simp [pull_apply, hF.add a i x y hi]
  · ext m; simp [pull_apply, hF.smul a i c x hi]
  · rw [pull_apply]
    have := hF.deg a ds (p + s) (π m) ha (hπ p m hm)
    convert this using 1
    ring

/-! ### Cyclic projective modules -/

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- A cyclic graded projective `P ≅ eΛ⟨b⟩` with generator `g`. -/
structure CycProj (PP : GMod GΛ P) where
  e : Λ
  g : P
  b : ℤ
  hg : PP.gr.IsHom b g
  ψ : P →ₗ[R] Λ
  ψ_act : ∀ m a, ψ (PP.act m a) = ψ m * a
  act_ψ : ∀ m, PP.act g (ψ m) = m
  ψ_deg : ∀ p m, PP.gr.IsHom p m → GΛ.gr.IsHom (p - b) (ψ m)

/-- **`Ext^{n+1}` out of a cyclic projective vanishes**, by the contracting
homotopy `H(a)(m) = F(ψ m, a)(g)`. -/
theorem CycProj.extVanish {PP : GMod GΛ P} (C : CycProj PP) (NN : GMod GΛ N) (n : ℕ) (t : ℤ) :
    ExtVanish PP NN n t := by
  intro F hF hd
  -- additivity of `F` in the first slot
  have hcons_add : ∀ (a : ℕ → Λ) (x y : Λ), F (Bar.cons (x + y) a) =
      F (Bar.cons x a) + F (Bar.cons y a) := fun a x y ↦ by
    have := hF.add (Bar.cons 0 a) 0 x y (by omega)
    simpa [Bar.update_cons_zero] using this
  have hcons_smul : ∀ (a : ℕ → Λ) (c : R) (x : Λ), F (Bar.cons (c • x) a) = c • F (Bar.cons x a) :=
    fun a c x ↦ by
      have := hF.smul (Bar.cons 0 a) 0 c x (by omega)
      simpa [Bar.update_cons_zero] using this
  let H : Bar.Cochain Λ (P →ₗ[R] N) := fun a ↦
    { toFun := fun m ↦ F (Bar.cons (C.ψ m) a) C.g
      map_add' := fun m m' ↦ by simp [map_add, hcons_add]
      map_smul' := fun c m ↦ by simp [map_smul, hcons_smul] }
  have hH : ∀ a m, H a m = F (Bar.cons (C.ψ m) a) C.g := fun _ _ ↦ rfl
  refine ⟨H, ⟨fun a ↦ ?_, fun a i x y hi ↦ ?_, fun a i c x hi ↦ ?_, fun a ds p m ha hm ↦ ?_⟩, ?_⟩
  · ext m; rw [hH, hH, hF.tr (Bar.cons _ a), Bar.tr_cons]
  · ext m
    simp only [hH, LinearMap.add_apply, ← Bar.update_cons_succ]
    rw [hF.add _ _ _ _ (by omega), LinearMap.add_apply]
  · ext m
    simp only [hH, LinearMap.smul_apply, ← Bar.update_cons_succ]
    rw [hF.smul _ _ _ _ (by omega), LinearMap.smul_apply]
  · rw [hH]
    have := hF.deg (Bar.cons (C.ψ m) a) (Bar.cons (p - C.b) ds) C.b C.g (fun i hi ↦ by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa [Bar.cons] using C.ψ_deg p m hm
      · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_lt hi0
        simpa [Bar.cons] using ha i' (by omega)) C.hg
    convert this using 1
    rw [Finset.sum_range_succ']
    simp only [Bar.cons, if_true, add_tsub_cancel_right, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, if_false]
    ring
  · -- `dH = F` from the cocycle equation at `(ψ m, a)`
    funext a
    ext m
    have hc := congrArg (fun G : Bar.Cochain Λ (P →ₗ[R] N) ↦ G (Bar.cons (C.ψ m) a) C.g) hd
    simp only [Bar.d_apply, Finset.sum_apply, LinearMap.sum_apply, Pi.zero_apply,
      LinearMap.zero_apply, Pi.smul_apply, LinearMap.smul_apply] at hc
    rw [Finset.sum_range_succ'] at hc
    rw [Bar.d_apply]
    simp only [Finset.sum_apply, LinearMap.sum_apply, pow_zero, one_smul, Pi.smul_apply,
      LinearMap.smul_apply] at hc ⊢
    rw [Bar.coface_zero, Bar.sh_cons, homAct_l, Bar.cons_zero, C.act_ψ] at hc
    have hterm : ∀ j ∈ Finset.range (n + 2),
        (-1 : ℤ) ^ (j + 1) • (Bar.coface (homAct PP NN) (n + 1) (j + 1) F (Bar.cons (C.ψ m) a)) C.g =
        -((-1 : ℤ) ^ j • (Bar.coface (homAct PP NN) n j H a) m) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      rw [pow_succ, mul_neg_one, neg_smul, neg_inj]
      congr 1
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [Bar.coface_mid _ (by omega) (by omega), Bar.coface_zero, homAct_l, hH,
          C.ψ_act, show 0 + 1 - 1 = 0 by omega, Bar.ct_zero_cons]
      · rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
        · rw [Bar.coface_mid _ (by omega) (by omega), Bar.coface_mid _ (by omega) (by omega), hH,
            show j + 1 - 1 = (j - 1) + 1 by omega, Bar.ct_succ_cons]
        · obtain rfl : j = n + 1 := by omega
          rw [Bar.coface_last, Bar.coface_last, homAct_r, homAct_r, hH, Bar.tr_cons,
            Bar.cons_succ]
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hc
    rw [add_comm] at hc
    exact (eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact hc)).symm

theorem pull_map_sub (f g : M' →ₗ[R] M) (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull (f - g) F = pull f F - pull g F := by
  funext a; ext m; simp [pull_apply]

theorem pull_map_add (f g : M' →ₗ[R] M) (F : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull (f + g) F = pull f F + pull g F := by
  funext a; ext m; simp [pull_apply]

theorem pull_zero_map (F : Bar.Cochain Λ (M →ₗ[R] N)) : pull (0 : M' →ₗ[R] M) F = 0 := by
  funext a; ext m; simp [pull_apply]

theorem pull_zero (π : M' →ₗ[R] M) : pull π (0 : Bar.Cochain Λ (M →ₗ[R] N)) = 0 := rfl

theorem pull_d_sub (π : M' →ₗ[R] M) (A : Bar.Act Λ (M →ₗ[R] N)) (n : ℕ)
    (F G : Bar.Cochain Λ (M →ₗ[R] N)) :
    pull π (Bar.d A n F - Bar.d A n G) = pull π (Bar.d A n F) - pull π (Bar.d A n G) := rfl

/-- **Additivity**: `Ext` vanishing passes to a finite graded direct sum
`M = ⊕ M_a⟨s_a⟩`. -/
theorem extVanish_of_decomp {ι : Type*} [Fintype ι] {Ms : ι → Type*} [∀ a, AddCommGroup (Ms a)]
    [∀ a, Module R (Ms a)] (MMs : ∀ a, GMod GΛ (Ms a)) (s : ι → ℤ) (inc : ∀ a, Ms a →ₗ[R] M)
    (pr : ∀ a, M →ₗ[R] Ms a) (hinc : ∀ a m x, inc a ((MMs a).act m x) = MM.act (inc a m) x)
    (hpr : ∀ a m x, pr a (MM.act m x) = (MMs a).act (pr a m) x)
    (hinc_deg : ∀ a p m, (MMs a).gr.IsHom p m → MM.gr.IsHom (p + s a) (inc a m))
    (hpr_deg : ∀ a p m, MM.gr.IsHom p m → (MMs a).gr.IsHom (p + -s a) (pr a m))
    (hsum : ∀ m, ∑ a, inc a (pr a m) = m) (n : ℕ) (t : ℤ)
    (h : ∀ a, inc a ≠ 0 → ExtVanish (MMs a) NN n (t + s a)) : ExtVanish MM NN n t := by
  intro F hF hd
  have hex : ∀ a, ∃ H, Good (MMs a) NN n (t + s a) H ∧
      Bar.d (homAct (MMs a) NN) n H = pull (inc a) F := fun a ↦ by
    by_cases ha : inc a = 0
    · exact ⟨0, Good.zero, by rw [ha, pull_zero_map, map_zero]⟩
    · exact h a ha (pull (inc a) F) (hF.pull (hinc_deg a)) (by rw [d_pull (hinc a), hd]; rfl)
  choose H hH hdH using hex
  refine ⟨∑ a, pull (pr a) (H a), ?_, ?_⟩
  · refine Good.sum' _ fun a _ ↦ ?_
    have := (hH a).pull (hpr_deg a)
    rwa [show t + s a + -s a = t by ring] at this
  · rw [map_sum]
    simp only [d_pull (hpr _), hdH, pull_comp]
    funext a'
    ext m
    simp only [Finset.sum_apply, LinearMap.sum_apply, pull_apply, LinearMap.comp_apply]
    rw [← map_sum, hsum]

/-- **Dimension shifting**: for an `R`-split exact sequence `0 → K → P → M → 0` of
graded modules with `Ext^{n+2}(P, -)_t = 0`, `Ext^{n+1}(K, N)_t = 0` gives
`Ext^{n+2}(M, N)_t = 0`. -/
theorem extVanish_shift {K P : Type*} [AddCommGroup K] [Module R K] [AddCommGroup P] [Module R P]
    {KK : GMod GΛ K} {PP : GMod GΛ P} (ι : K →ₗ[R] P) (π : P →ₗ[R] M) (s : M →ₗ[R] P)
    (ρ : P →ₗ[R] K) (hι : ∀ m a, ι (KK.act m a) = PP.act (ι m) a)
    (hπ : ∀ m a, π (PP.act m a) = MM.act (π m) a)
    (hι_deg : ∀ p m, KK.gr.IsHom p m → PP.gr.IsHom (p + 0) (ι m))
    (hπ_deg : ∀ p m, PP.gr.IsHom p m → MM.gr.IsHom (p + 0) (π m))
    (hs_deg : ∀ p m, MM.gr.IsHom p m → PP.gr.IsHom (p + 0) (s m))
    (hρ_deg : ∀ p m, PP.gr.IsHom p m → KK.gr.IsHom (p + 0) (ρ m))
    (hπs : π ∘ₗ s = LinearMap.id) (hρι : ρ ∘ₗ ι = LinearMap.id)
    (hsplit : ι ∘ₗ ρ + s ∘ₗ π = LinearMap.id) (hπι : π ∘ₗ ι = 0) {n : ℕ} {t : ℤ}
    (hP : ExtVanish PP NN (n + 1) t) (hK : ExtVanish KK NN n t) :
    ExtVanish MM NN (n + 1) t := by
  intro z hz hdz
  have hz' := hz.pull hπ_deg
  rw [add_zero] at hz'
  obtain ⟨w, hw, hdw⟩ := hP (pull π z) hz' (by rw [d_pull hπ, hdz]; rfl)
  have hu0 := hw.pull hι_deg
  rw [add_zero] at hu0
  obtain ⟨u, hu, hdu⟩ := hK (pull ι w) hu0 (by
    rw [d_pull hι, hdw, pull_comp, hπι, pull_zero_map])
  set w' := w - Bar.d (homAct PP NN) n (pull ρ u)
  have hρu := hu.pull hρ_deg
  rw [add_zero] at hρu
  have hw' : Good PP NN (n + 1) t w' := by
    have h := hw.add' (hρu.d.zsmul' (-1))
    have he : w' = w + (-1 : ℤ) • Bar.d (homAct PP NN) n (pull ρ u) := by
      simp [w', sub_eq_add_neg]
    rwa [he]
  have hιw' : pull ι w' = 0 := by
    simp only [w', pull_sub, ← d_pull hι, pull_comp, hρι, pull_id, hdu, sub_self]
  have hv := hw'.pull hs_deg
  rw [add_zero] at hv
  refine ⟨pull s w', hv, ?_⟩
  have hdw' : Bar.d (homAct PP NN) (n + 1) w' = pull π z := by
    simp only [w', map_sub, Bar.d_d, sub_zero, hdw]
  have hπv : pull s (pull π (Bar.d (homAct MM NN) (n + 1) (pull s w'))) =
      Bar.d (homAct MM NN) (n + 1) (pull s w') := by
    rw [pull_comp, hπs, pull_id]
  rw [← hπv, ← d_pull hπ, pull_comp]
  have hsπ : s ∘ₗ π = LinearMap.id - ι ∘ₗ ρ := by rw [← hsplit]; abel
  rw [hsπ, pull_map_sub, pull_id, ← pull_comp, hιw', pull_zero, sub_zero, hdw', pull_comp, hπs,
    pull_id]

/-! ### `Ext¹` and graded extensions -/

/-- The sequence `(a, 0, 0, …)`. -/
def single (a : Λ) : ℕ → Λ := Bar.cons a 0

theorem Good.one_eq {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN 1 t F) (a : ℕ → Λ) :
    F a = F (single (a 0)) := by
  rw [hF.tr, hF.tr (single _)]
  congr 1
  funext k
  by_cases h : k = 0 <;> simp [Bar.tr, single, Bar.cons, h]

/-- The cocycle equation of a one-cochain. -/
theorem cocycle_one {F : Bar.Cochain Λ (M →ₗ[R] N)} {t : ℤ} (hF : Good MM NN 1 t F)
    (hd : Bar.d (homAct MM NN) 1 F = 0) (a b : Λ) (m : M) :
    F (single b) (MM.act m a) - F (single (a * b)) m + NN.act (F (single a) m) b = 0 := by
  have h := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (Bar.cons a (single b)) m) hd
  simp only [Bar.d_apply, Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply,
    LinearMap.smul_apply, Pi.zero_apply, LinearMap.zero_apply] at h
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add] at h
  have h0 : Bar.coface (homAct MM NN) 1 0 F (Bar.cons a (single b)) m = F (single b) (MM.act m a) := by
    rw [Bar.coface_zero, homAct_l, Bar.sh_cons, Bar.cons_zero]
  have h1 : Bar.coface (homAct MM NN) 1 1 F (Bar.cons a (single b)) m = F (single (a * b)) m := by
    rw [Bar.coface_mid _ (by omega) (by omega), show 1 - 1 = 0 from rfl, Bar.ct_zero_cons]
    congr 2
  have h2 : Bar.coface (homAct MM NN) 1 2 F (Bar.cons a (single b)) m =
      NN.act (F (single a) m) b := by
    rw [Bar.coface_last, homAct_r, Bar.tr_cons, Bar.cons_succ]
    congr 3
  rw [h0, h1, h2] at h
  simp only [pow_zero, one_smul, pow_one, neg_smul] at h
  rw [← h]
  abel

theorem Good.single_add {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN 1 t F) (a a' : Λ) :
    F (single (a + a')) = F (single a) + F (single a') := by
  have := hF.add (single 0) 0 a a' (by omega)
  simpa [single, Bar.update_cons_zero] using this

theorem Good.single_smul {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN 1 t F) (c : R)
    (a : Λ) : F (single (c • a)) = c • F (single a) := by
  have := hF.smul (single 0) 0 c a (by omega)
  simpa [single, Bar.update_cons_zero] using this

/-- The grading of `N⟨-t⟩ ⊕ M`. -/
def twistGr (t : ℤ) : ZGr (R := R) (N × M) where
  proj p := (NN.gr.proj (p + t)).prodMap (MM.gr.proj p)
  supp := MM.gr.supp ∪ NN.gr.supp.image (· - t)
  proj_proj p q x := by
    by_cases h : q = p
    · subst h
      ext <;> simp [NN.gr.proj_proj, MM.gr.proj_proj]
    · rw [if_neg h]
      ext <;> simp [NN.gr.proj_proj, MM.gr.proj_proj, h]
  proj_out p hp := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · simp only [LinearMap.prodMap_apply, LinearMap.zero_apply, Prod.fst_zero]
      rw [NN.gr.proj_out (p + t) (fun h ↦ hp (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨_, h, by ring⟩))), LinearMap.zero_apply]
    · simp only [LinearMap.prodMap_apply, LinearMap.zero_apply, Prod.snd_zero]
      rw [MM.gr.proj_out p (fun h ↦ hp (Finset.mem_union_left _ h)), LinearMap.zero_apply]
  sum x := by
    classical
    ext
    · simp only [Prod.fst_sum, LinearMap.prodMap_apply]
      conv_lhs => rw [NN.gr.sum x.1]
      have hvan : ∀ p ∈ MM.gr.supp ∪ NN.gr.supp.image (· - t),
          p ∉ NN.gr.supp.image (· - t) → NN.gr.proj (p + t) x.1 = 0 := fun p _ hp ↦ by
        rw [NN.gr.proj_out (p + t) (fun h ↦ hp (Finset.mem_image.2 ⟨_, h, by ring⟩)),
          LinearMap.zero_apply]
      rw [← Finset.sum_subset Finset.subset_union_right hvan,
        Finset.sum_image (fun p _ q _ h ↦ by simpa using h)]
      exact Finset.sum_congr rfl fun p _ ↦ by rw [sub_add_cancel]
    · simp only [Prod.snd_sum, LinearMap.prodMap_apply]
      conv_lhs => rw [MM.gr.sum x.2]
      exact Finset.sum_subset Finset.subset_union_left fun p _ hp ↦ by
        rw [MM.gr.proj_out p hp, LinearMap.zero_apply]

theorem twistGr_isHom {t p : ℤ} {x : N × M} :
    (twistGr (MM := MM) (NN := NN) t).IsHom p x ↔ NN.gr.IsHom (p + t) x.1 ∧ MM.gr.IsHom p x.2 := by
  simp only [ZGr.IsHom, twistGr, Prod.ext_iff, LinearMap.prodMap_apply]

/-- **The extension defined by a one-cocycle**: `N⟨-t⟩ ⊕ M` with
`(n, m)·a = (na + F(a)(m), ma)`. -/
def twist {t : ℤ} (F : Bar.Cochain Λ (M →ₗ[R] N)) (hF : Good MM NN 1 t F)
    (hd : Bar.d (homAct MM NN) 1 F = 0) : GMod GΛ (N × M) where
  act := LinearMap.mk₂ R (fun x a ↦ (NN.act x.1 a + F (single a) x.2, MM.act x.2 a))
    (fun x x' a ↦ by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ext <;> simp; abel)
    (fun c x a ↦ by ext <;> simp)
    (fun x a a' ↦ by ext <;> simp [hF.single_add]; abel)
    (fun c x a ↦ by ext <;> simp [hF.single_smul])
  act_one x := by
    have h := cocycle_one hF hd 1 1 x.2
    rw [MM.act_one, mul_one, sub_self, zero_add, NN.act_one] at h
    ext <;> simp [h, NN.act_one, MM.act_one]
  act_mul x a b := by
    have h := cocycle_one hF hd a b x.2
    have h' : F (single b) (MM.act x.2 a) =
        F (single (a * b)) x.2 - NN.act (F (single a) x.2) b := by
      rw [← sub_eq_zero, ← h]; abel
    ext
    · simp only [LinearMap.mk₂_apply, map_add, LinearMap.add_apply, NN.act_mul, h']
      abel
    · simp [MM.act_mul]
  gr := twistGr t
  act_hom p q x a hx ha := by
    rw [twistGr_isHom (MM := MM) (NN := NN)] at hx ⊢
    refine ⟨?_, MM.act_hom _ _ _ _ hx.2 ha⟩
    simp only [LinearMap.mk₂_apply]
    have h1 := NN.act_hom _ _ _ _ hx.1 ha
    have h2 := hF.deg (single a) (fun _ ↦ q) p x.2 (fun i hi ↦ by
      obtain rfl : i = 0 := by omega
      simpa [single, Bar.cons] using ha) hx.2
    simp only [Finset.sum_range_one] at h2
    exact NN.gr.isHom_add (by rwa [show p + t + q = p + q + t by ring] at h1) h2

/-- **A graded section of the extension makes the cocycle a coboundary.** -/
theorem coboundary_of_section {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] N)} (hF : Good MM NN 1 t F)
    (hd : Bar.d (homAct MM NN) 1 F = 0) (σ : M →ₗ[R] N × M) (hσ2 : ∀ m, (σ m).2 = m)
    (hσ : ∀ m a, σ (MM.act m a) = (twist F hF hd).act (σ m) a)
    (hσdeg : ∀ p m, MM.gr.IsHom p m → (twistGr (MM := MM) (NN := NN) t).IsHom p (σ m)) :
    ∃ φ, Good MM NN 0 t φ ∧ Bar.d (homAct MM NN) 0 φ = F := by
  refine ⟨fun _ ↦ LinearMap.fst R N M ∘ₗ σ, ⟨fun _ ↦ rfl, fun _ _ _ _ hi ↦ absurd hi (by omega),
    fun _ _ _ _ hi ↦ absurd hi (by omega), fun a ds p m _ hm ↦ ?_⟩, ?_⟩
  · simpa using ((twistGr_isHom).1 (hσdeg p m hm)).1
  · funext a
    ext m
    rw [Bar.d_apply]
    simp only [Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, pow_one,
      neg_smul]
    have hl := Bar.coface_last (homAct MM NN) 0 (fun _ ↦ LinearMap.fst R N M ∘ₗ σ) a
    simp only [zero_add] at hl
    rw [Bar.coface_zero, hl]
    simp only [LinearMap.add_apply, LinearMap.neg_apply, homAct_l, homAct_r]
    simp only [LinearMap.comp_apply, LinearMap.fst_apply, hσ]
    simp only [twist, LinearMap.mk₂_apply, hσ2]
    rw [hF.one_eq a]
    abel

/-! ### Homogeneous components of module maps -/

section SumComp

variable {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup Z] [Module R Z]

theorem lsum_comp {ι : Type*} (S : Finset ι) (f : ι → Y →ₗ[R] Z) (g : X →ₗ[R] Y) :
    (∑ i ∈ S, f i) ∘ₗ g = ∑ i ∈ S, f i ∘ₗ g :=
  LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, LinearMap.sum_apply]

theorem lcomp_sum {ι : Type*} (S : Finset ι) (g : Y →ₗ[R] Z) (f : ι → X →ₗ[R] Y) :
    g ∘ₗ (∑ i ∈ S, f i) = ∑ i ∈ S, g ∘ₗ f i :=
  LinearMap.ext fun x ↦ by simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

end SumComp

section Components

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- The degree-`r` component `Σ_p proj_{p+r} ∘ u ∘ proj_p` of a linear map. -/
def ZGr.comp (gX : ZGr (R := R) X) (gY : ZGr (R := R) Y) (r : ℤ) (u : X →ₗ[R] Y) : X →ₗ[R] Y :=
  ∑ p ∈ gX.supp, gY.proj (p + r) ∘ₗ u ∘ₗ gX.proj p

variable (gX : ZGr (R := R) X) (gY : ZGr (R := R) Y)

theorem ZGr.comp_hom {r p : ℤ} (u : X →ₗ[R] Y) {m : X} (hm : gX.IsHom p m) :
    ZGr.comp gX gY r u m = gY.proj (p + r) (u m) := by
  classical
  simp only [ZGr.comp, LinearMap.sum_apply, LinearMap.comp_apply, gX.proj_of_isHom hm]
  by_cases hp : p ∈ gX.supp
  · rw [Finset.sum_eq_single p (fun q _ hq ↦ by rw [if_neg (Ne.symm hq), map_zero, map_zero])
      (fun h ↦ absurd hp h), if_pos rfl]
  · rw [gX.eq_zero_of_isHom_out hm hp]
    simp

theorem ZGr.comp_isHom {r p : ℤ} (u : X →ₗ[R] Y) {m : X} (hm : gX.IsHom p m) :
    gY.IsHom (p + r) (ZGr.comp gX gY r u m) := by
  rw [ZGr.comp_hom gX gY u hm]; exact gY.isHom_proj _ _

/-- The finite set of possible degrees of components. -/
def ZGr.compDegs : Finset ℤ := (gY.supp ×ˢ gX.supp).image (fun qp ↦ qp.1 - qp.2)

/-- A linear map is the sum of its components. -/
theorem ZGr.eq_sum_comp (u : X →ₗ[R] Y) :
    u = ∑ r ∈ ZGr.compDegs gX gY, ZGr.comp gX gY r u := by
  classical
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [LinearMap.sum_apply]
  simp only [ZGr.comp_hom gX gY u hm]
  by_cases hp : p ∈ gX.supp
  · have hsub : gY.supp.image (fun q ↦ q - p) ⊆ ZGr.compDegs gX gY := fun r hr ↦ by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
      exact Finset.mem_image.2 ⟨(q, p), Finset.mem_product.2 ⟨hq, hp⟩, rfl⟩
    rw [← Finset.sum_subset hsub (fun r _ hr ↦ by
      rw [gY.proj_out (p + r) (fun h ↦ hr (Finset.mem_image.2 ⟨p + r, h, by ring⟩)),
        LinearMap.zero_apply]),
      Finset.sum_image (fun q _ q' _ h ↦ by simpa using h)]
    conv_lhs => rw [gY.sum (u m)]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [add_sub_cancel]
  · rw [gX.eq_zero_of_isHom_out hm hp, map_zero]
    simp

theorem ZGr.comp_eq_zero_of_hom {r : ℤ} {u : X →ₗ[R] Y} {s : ℤ}
    (hu : ∀ p m, gX.IsHom p m → gY.IsHom (p + s) (u m)) (hrs : r ≠ s) : ZGr.comp gX gY r u = 0 := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom gX gY u hm, gY.proj_of_isHom (hu p m hm), if_neg (by omega),
    LinearMap.zero_apply]

theorem ZGr.comp_eq_self_of_hom {s : ℤ} {u : X →ₗ[R] Y}
    (hu : ∀ p m, gX.IsHom p m → gY.IsHom (p + s) (u m)) : ZGr.comp gX gY s u = u := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom gX gY u hm, hu p m hm]

theorem ZGr.comp_comp_left {Z : Type*} [AddCommGroup Z] [Module R Z] (gZ : ZGr (R := R) Z)
    (r : ℤ) (u : X →ₗ[R] Y) (v : Y →ₗ[R] Z) (hv : ∀ p m, gY.IsHom p m → gZ.IsHom p (v m)) :
    ZGr.comp gX gZ r (v ∘ₗ u) = v ∘ₗ ZGr.comp gX gY r u := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [LinearMap.comp_apply, ZGr.comp_hom gX gZ _ hm, ZGr.comp_hom gX gY _ hm, LinearMap.comp_apply]
  conv_lhs => rw [gY.sum (u m), map_sum, map_sum]
  rw [Finset.sum_eq_single (p + r)]
  · rw [gZ.proj_of_isHom (hv _ _ (gY.isHom_proj _ _)), if_pos rfl]
  · intro q _ hq
    rw [gZ.proj_of_isHom (hv _ _ (gY.isHom_proj _ _)), if_neg hq]
  · intro h
    rw [gY.proj_out _ h, LinearMap.zero_apply, map_zero, map_zero]

theorem ZGr.comp_comp_right {W : Type*} [AddCommGroup W] [Module R W] (gW : ZGr (R := R) W)
    (r : ℤ) (u : X →ₗ[R] Y) (w : W →ₗ[R] X) (hw : ∀ p m, gW.IsHom p m → gX.IsHom p (w m)) :
    ZGr.comp gW gY r (u ∘ₗ w) = ZGr.comp gX gY r u ∘ₗ w := by
  refine gW.ext_of_hom fun p m hm ↦ ?_
  rw [LinearMap.comp_apply, ZGr.comp_hom gW gY _ hm, LinearMap.comp_apply,
    ZGr.comp_hom gX gY _ (hw p m hm)]

/-- A homogeneous map of degree `s` commutes with the projections. -/
theorem ZGr.proj_map {s : ℤ} {u : X →ₗ[R] Y}
    (hu : ∀ p m, gX.IsHom p m → gY.IsHom (p + s) (u m)) (p : ℤ) (m : X) :
    gY.proj (p + s) (u m) = u (gX.proj p m) := by
  conv_lhs => rw [gX.sum m, map_sum, map_sum]
  by_cases hp : p ∈ gX.supp
  · rw [Finset.sum_eq_single p (fun q _ hq ↦ by
      rw [gY.proj_of_isHom (hu _ _ (gX.isHom_proj q m)), if_neg (by omega)]) (fun h ↦ absurd hp h),
      gY.proj_of_isHom (hu _ _ (gX.isHom_proj p m)), if_pos rfl]
  · rw [gX.proj_out p hp, LinearMap.zero_apply, map_zero]
    exact Finset.sum_eq_zero fun q hq ↦ by
      rw [gY.proj_of_isHom (hu _ _ (gX.isHom_proj q m)), if_neg (fun h ↦ hp (by
        have : q = p := by omega
        exact this ▸ hq))]

/-- An injective homogeneous map reflects homogeneity. -/
theorem ZGr.isHom_of_injective {s : ℤ} {u : X →ₗ[R] Y}
    (hu : ∀ p m, gX.IsHom p m → gY.IsHom (p + s) (u m)) (hinj : Function.Injective u) {p : ℤ}
    {m : X} (hm : gY.IsHom (p + s) (u m)) : gX.IsHom p m :=
  hinj (by rw [← ZGr.proj_map gX gY hu]; exact hm)

theorem ZGr.comp_sum {ι : Type*} (S : Finset ι) (r : ℤ) (u : ι → X →ₗ[R] Y) :
    ZGr.comp gX gY r (∑ i ∈ S, u i) = ∑ i ∈ S, ZGr.comp gX gY r (u i) := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom _ _ _ hm, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (ZGr.comp_hom _ _ _ hm).symm

theorem ZGr.comp_out {r : ℤ} (hr : r ∉ ZGr.compDegs gX gY) (u : X →ₗ[R] Y) :
    ZGr.comp gX gY r u = 0 := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom _ _ _ hm, LinearMap.zero_apply]
  by_cases hp : p ∈ gX.supp
  · rw [gY.proj_out (p + r) (fun h ↦ hr (Finset.mem_image.2 ⟨(p + r, p),
      Finset.mem_product.2 ⟨h, hp⟩, by ring⟩)), LinearMap.zero_apply]
  · rw [gX.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

/-- The degree-zero part of a composite is the sum of the matching components. -/
theorem ZGr.comp_zero_comp {Z : Type*} [AddCommGroup Z] [Module R Z] (gZ : ZGr (R := R) Z)
    (u : X →ₗ[R] Y) (v : Y →ₗ[R] Z) :
    ZGr.comp gX gZ 0 (v ∘ₗ u) =
      ∑ r ∈ ZGr.compDegs gX gY, ZGr.comp gY gZ (-r) v ∘ₗ ZGr.comp gX gY r u := by
  refine gX.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom _ _ _ hm, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  have h : ∀ r, ZGr.comp gY gZ (-r) v (ZGr.comp gX gY r u m) =
      gZ.proj p (v (ZGr.comp gX gY r u m)) := fun r ↦ by
    rw [ZGr.comp_hom gY gZ v (ZGr.comp_isHom gX gY u hm), show p + r + -r = p by ring]
  simp only [h]
  rw [← map_sum, ← map_sum, ← LinearMap.sum_apply, ← ZGr.eq_sum_comp, add_zero]

end Components

section ModComponents

variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  {XX : GMod GΛ X} {YY : GMod GΛ Y}

/-- Homogeneous components of graded modules commute with the action. -/
theorem proj_act (YY : GMod GΛ Y) {q : ℤ} {a : Λ} (ha : GΛ.gr.IsHom q a) (p : ℤ) (y : Y) :
    YY.gr.proj (p + q) (YY.act y a) = YY.act (YY.gr.proj p y) a := by
  conv_lhs => rw [YY.gr.sum y, map_sum, LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single p]
  · rw [YY.gr.proj_of_isHom (YY.act_hom _ _ _ _ (YY.gr.isHom_proj _ _) ha), if_pos rfl]
  · intro s _ hs
    rw [YY.gr.proj_of_isHom (YY.act_hom _ _ _ _ (YY.gr.isHom_proj _ _) ha), if_neg (by omega)]
  · intro h
    rw [YY.gr.proj_out _ h, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, map_zero]

/-- **Components of `Λ`-linear maps are `Λ`-linear.** -/
theorem comp_act (r : ℤ) {u : X →ₗ[R] Y} (hu : ∀ m a, u (XX.act m a) = YY.act (u m) a) (m : X)
    (a : Λ) : ZGr.comp XX.gr YY.gr r u (XX.act m a) = YY.act (ZGr.comp XX.gr YY.gr r u m) a := by
  conv_lhs => rw [XX.gr.sum m, GΛ.gr.sum a]
  conv_rhs => rw [XX.gr.sum m, GΛ.gr.sum a]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
  rw [ZGr.comp_hom _ _ _ (XX.act_hom _ _ _ _ (XX.gr.isHom_proj p m) (GΛ.gr.isHom_proj q a)),
    ZGr.comp_hom _ _ _ (XX.gr.isHom_proj p m), hu, show p + q + r = (p + r) + q by ring,
    proj_act YY (GΛ.gr.isHom_proj q a)]

end ModComponents


/-! ### Finite products with a shift -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ms : ι → Type*} [∀ a, AddCommGroup (Ms a)]
  [∀ a, Module R (Ms a)]

/-- The grading of `⊕_a M_a⟨s_a⟩`: `(⊕ M_a)_p = ⊕ (M_a)_{p-s_a}`. -/
def ZGr.piShift (gs : ∀ a, ZGr (R := R) (Ms a)) (s : ι → ℤ) : ZGr (R := R) (∀ a, Ms a) where
  proj p := LinearMap.pi fun a ↦ (gs a).proj (p - s a) ∘ₗ LinearMap.proj a
  supp := Finset.univ.biUnion fun a ↦ (gs a).supp.image (· + s a)
  proj_proj p q x := by
    funext a
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, (gs a).proj_proj]
    by_cases h : q = p
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]; rfl
  proj_out p hp := by
    refine LinearMap.ext fun x ↦ funext fun a ↦ ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply,
      Pi.zero_apply]
    rw [(gs a).proj_out (p - s a) (fun h ↦ hp (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a,
      Finset.mem_image.2 ⟨p - s a, h, by ring⟩⟩)), LinearMap.zero_apply]
  sum x := by
    classical
    funext a
    rw [Finset.sum_apply]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    conv_lhs => rw [(gs a).sum (x a)]
    have hsub : (gs a).supp.image (· + s a) ⊆ Finset.univ.biUnion fun a ↦ (gs a).supp.image (· + s a) :=
      Finset.subset_biUnion_of_mem (fun a ↦ (gs a).supp.image (· + s a)) (Finset.mem_univ a)
    rw [← Finset.sum_subset hsub (fun p _ hp ↦ by
      rw [(gs a).proj_out (p - s a) (fun h ↦ hp (Finset.mem_image.2 ⟨p - s a, h, by ring⟩)),
        LinearMap.zero_apply]),
      Finset.sum_image (fun p _ q _ h ↦ by simpa using h)]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [add_sub_cancel_right]

theorem ZGr.piShift_isHom (gs : ∀ a, ZGr (R := R) (Ms a)) (s : ι → ℤ) (p : ℤ) (x : ∀ a, Ms a) :
    (ZGr.piShift gs s).IsHom p x ↔ ∀ a, (gs a).IsHom (p - s a) (x a) := by
  simp only [ZGr.IsHom, ZGr.piShift, funext_iff, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- **`⊕_a M_a⟨s_a⟩`** as a graded module. -/
def GMod.pi (MMs : ∀ a, GMod GΛ (Ms a)) (s : ι → ℤ) : GMod GΛ (∀ a, Ms a) where
  act := LinearMap.mk₂ R (fun x b a ↦ (MMs a).act (x a) b)
    (fun x x' b ↦ by funext a; simp) (fun c x b ↦ by funext a; simp)
    (fun x b b' ↦ by funext a; simp) (fun c x b ↦ by funext a; simp)
  act_one x := by funext a; simp [(MMs a).act_one]
  act_mul x b b' := by funext a; simp [(MMs a).act_mul]
  gr := ZGr.piShift (fun a ↦ (MMs a).gr) s
  act_hom p q x b hx hb := by
    rw [ZGr.piShift_isHom] at hx ⊢
    intro a
    have := (MMs a).act_hom _ _ _ _ (hx a) hb
    simp only [LinearMap.mk₂_apply]
    rwa [show p + q - s a = p - s a + q by ring]

theorem GMod.pi_act (MMs : ∀ a, GMod GΛ (Ms a)) (s : ι → ℤ) (x : ∀ a, Ms a) (b : Λ) (a : ι) :
    (GMod.pi MMs s).act x b a = (MMs a).act (x a) b := rfl

/-- **`Ext` out of a finite sum of shifts.** -/
theorem extVanish_pi (MMs : ∀ a, GMod GΛ (Ms a)) (s : ι → ℤ) (n : ℕ) (t : ℤ)
    (h : ∀ a, ExtVanish (MMs a) NN n (t + s a)) : ExtVanish (GMod.pi MMs s) NN n t :=
  extVanish_of_decomp (MM := GMod.pi MMs s) MMs s (fun a ↦ LinearMap.single R Ms a)
    (fun a ↦ LinearMap.proj a)
    (fun a m x ↦ by
      funext a'
      rw [GMod.pi_act]
      by_cases h : a' = a
      · subst h; simp
      · simp [h])
    (fun a m x ↦ rfl)
    (fun a p m hm ↦ (ZGr.piShift_isHom _ _ _ _).2 fun a' ↦ by
      by_cases h : a' = a
      · subst h; simpa using hm
      · rw [LinearMap.single_apply, Pi.single_eq_of_ne h]
        exact ZGr.isHom_zero (MMs a').gr _)
    (fun a p m hm ↦ by
      have := (ZGr.piShift_isHom _ _ _ _).1 hm a
      simpa [sub_eq_add_neg] using this)
    (fun m ↦ by
      funext a'
      simp [Finset.sum_apply, Pi.single_apply])
    n t fun a _ ↦ h a

end Pi

/-! ### Left modules over the opposite -/

section Left

variable {B : Type*} [Ring B] [Algebra R B] {GB : GAlg (R := R) Bᵐᵒᵖ}

/-- The underlying left `B`-module of a graded right `Bᵐᵒᵖ`… i.e. right `B`-module
over `Λ = Bᵐᵒᵖ`: `b • m = m·(op b)`. -/
def Left (_MM : GMod GB M) : Type _ := M

variable (MM : GMod GB M)

instance : AddCommGroup (Left MM) := inferInstanceAs (AddCommGroup M)
instance : Module R (Left MM) := inferInstanceAs (Module R M)

instance : Module B (Left MM) where
  smul b m := (MM.act (show M from m) (MulOpposite.op b) : M)
  one_smul m := MM.act_one (show M from m)
  mul_smul b b' m :=
    (congrArg (MM.act (show M from m)) (MulOpposite.op_mul b b')).trans
      (MM.act_mul (show M from m) _ _).symm
  smul_zero b := by change MM.act (0 : M) _ = 0; simp
  smul_add b m m' := by
    change MM.act ((show M from m) + (show M from m')) _ = MM.act (show M from m) _ +
      MM.act (show M from m') _
    rw [map_add, LinearMap.add_apply]
  add_smul b b' m := by
    change MM.act (show M from m) (MulOpposite.op (b + b')) = MM.act (show M from m) _ +
      MM.act (show M from m) _
    rw [MulOpposite.op_add, map_add]
  zero_smul m := by change MM.act (show M from m) (MulOpposite.op 0) = 0; simp

instance : IsScalarTower R B (Left MM) where
  smul_assoc c b m := by
    change MM.act (show M from m) (MulOpposite.op (c • b)) = c • MM.act (show M from m) _
    rw [MulOpposite.op_smul, map_smul]

theorem Left.smul_def (b : B) (m : Left MM) : b • m = (MM.act (show M from m) (MulOpposite.op b) : M) :=
  rfl

/-- A `Λ`-linear map between graded modules as a `B`-linear map of the left modules. -/
def Left.map {NN : GMod GB N} (u : M →ₗ[R] N) (hu : ∀ m a, u (MM.act m a) = NN.act (u m) a) :
    Left MM →ₗ[B] Left NN where
  toFun := u
  map_add' := u.map_add
  map_smul' b m := hu m (MulOpposite.op b)

end Left

/-! ### Kernels of graded maps -/

section Ker

variable {P : Type*} [AddCommGroup P] [Module R P] (PP : GMod GΛ P) (MM : GMod GΛ M)
  {π : P →ₗ[R] M} (hπ : ∀ x a, π (PP.act x a) = MM.act (π x) a)
  (hdeg : ∀ p x, PP.gr.IsHom p x → MM.gr.IsHom (p + 0) (π x))

include hdeg in
theorem ker_proj_mem (p : ℤ) {x : P} (hx : x ∈ LinearMap.ker π) :
    PP.gr.proj p x ∈ LinearMap.ker π := by
  rw [LinearMap.mem_ker, ← ZGr.proj_map PP.gr MM.gr hdeg, LinearMap.mem_ker.1 hx, map_zero]

/-- The grading of a kernel. -/
def ZGr.ker : ZGr (R := R) (LinearMap.ker π) where
  proj p := (PP.gr.proj p).restrict (fun _ hx ↦ ker_proj_mem PP MM hdeg p hx)
  supp := PP.gr.supp
  proj_proj p q x := by
    apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply, PP.gr.proj_proj]
    split_ifs <;> rfl
  proj_out p hp := LinearMap.ext fun x ↦ Subtype.ext (by
    simp [PP.gr.proj_out p hp])
  sum x := Subtype.ext (by
    rw [Submodule.coe_sum]
    simp only [LinearMap.restrict_coe_apply]
    exact PP.gr.sum x)

theorem ZGr.ker_isHom (p : ℤ) (x : LinearMap.ker π) :
    (ZGr.ker PP MM hdeg).IsHom p x ↔ PP.gr.IsHom p (x : P) := by
  simp only [ZGr.IsHom, ZGr.ker, Subtype.ext_iff, LinearMap.restrict_coe_apply]

include hπ in
theorem ker_act_mem (x : LinearMap.ker π) (a : Λ) : PP.act (x : P) a ∈ LinearMap.ker π := by
  rw [LinearMap.mem_ker, hπ, LinearMap.mem_ker.1 x.2, map_zero, LinearMap.zero_apply]

/-- **The kernel of a graded map** as a graded module. -/
def GMod.ker : GMod GΛ (LinearMap.ker π) where
  act := LinearMap.mk₂ R (fun x a ↦ ⟨PP.act (x : P) a, ker_act_mem PP MM hπ x a⟩)
    (fun x x' a ↦ Subtype.ext (by simp)) (fun c x a ↦ Subtype.ext (by simp))
    (fun x a a' ↦ Subtype.ext (by simp)) (fun c x a ↦ Subtype.ext (by simp))
  act_one x := Subtype.ext (PP.act_one _)
  act_mul x a b := Subtype.ext (PP.act_mul _ _ _)
  gr := ZGr.ker PP MM hdeg
  act_hom p q x a hx ha := by
    rw [ZGr.ker_isHom] at hx ⊢
    exact PP.act_hom _ _ _ _ hx ha

theorem GMod.ker_act (x : LinearMap.ker π) (a : Λ) :
    ((GMod.ker PP MM hπ hdeg).act x a : P) = PP.act (x : P) a := rfl

end Ker

end GExt

end MultiplicativeBasisDeformations
