import MultiplicativeBasisDeformations.Refinements.ModuleLifting
import MultiplicativeBasisDeformations.Refinements.WeightCone

/-!
# Weight-homogeneous lifts of module actions (toward Proposition 12.8)

`deformation-refinements.tex`: the degree-by-degree lifting of Proposition 6.5 with the
choices "made separately in each degree and weight". If the deformation `μ_q` and the action of
`M` have all relative weights in a monoid `C` (`ConeBil`), the corrections can be taken with
relative weights in `C`: the error of the next degree has weights in `C`, and the cone part of
any correction removing it removes it as well, since the correction equation commutes with the
cone parts (`cbil`). Hence a lifted action with all relative weights in `C`
(`exists_actFam_cone`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

namespace GExt

open MGr

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M : Type*} [AddCommGroup M] [Module R M] {MM : GMod GΛ M}
  {Wt : Type*} [AddCommGroup Wt] [DecidableEq Wt] (C : AddSubmonoid Wt)
  (wΛ : MGr R Wt Λ) (wM : MGr R Wt M)

variable (MM) in
/-- Weight gradings compatible with the product, the action and the internal degrees. -/
structure WtCompat : Prop where
  mul : ∀ α β a b, wΛ.IsHom α a → wΛ.IsHom β b → wΛ.IsHom (α + β) (a * b)
  act : ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.IsHom (β + α) (MM.act m a)
  projM : ∀ g p m, MM.gr.IsHom p m → MM.gr.IsHom p (wM.proj g m)
  projΛ : ∀ g p a, GΛ.gr.IsHom p a → GΛ.gr.IsHom p (wΛ.proj g a)

variable {C wΛ wM}

theorem ConeAt.congr' {σ σ' : Wt} {G : MGr R Wt M} {n : M} (h : ConeAt C G σ n) (e : σ = σ') :
    ConeAt C G σ' n := e ▸ h

/-- **The error of a family with weights in the cone has weights in the cone.** -/
theorem assocErr_coneAt {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} {μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ}
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hμ : ∀ j, ConeBil (C := C) (G := wΛ) (G' := wΛ) (G'' := wΛ) 0 (μ j)) (n : ℕ)
    {β α α' : Wt} {m : M} {a b : Λ} (hm : wM.IsHom β m) (ha : wΛ.IsHom α a) (hb : wΛ.IsHom α' b) :
    ConeAt C wM (β + α + α') (assocErr ν μ n m a b) := by
  unfold assocErr
  refine ConeAt.sub (ConeAt.sum _ fun x _ ↦ ?_) (ConeAt.sum _ fun x _ ↦ ?_)
  · have h1 := hν x.1 β α m a hm ha
    have h2 := (hν x.2).apply h1 (coneAt_of_isHom hb)
    exact ConeAt.congr' h2 (by abel)
  · have h1 := hμ x.2 α α' a b ha hb
    have h2 := (hν x.1).apply (coneAt_of_isHom hm) h1
    exact ConeAt.congr' h2 (by abel)

/-- A trilinear identity holds when it holds on weight-homogeneous inputs. -/
theorem assocErr_eq_zero_of_wt (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ)
    (h : ∀ β α α' m a b, wM.IsHom β m → wΛ.IsHom α a → wΛ.IsHom α' b →
      assocErr ν μ n m a b = 0) (m : M) (a b : Λ) : assocErr ν μ n m a b = 0 := by
  have h1 : ∀ β m, wM.IsHom β m → ∀ α a, wΛ.IsHom α a → ∀ b, assocErr ν μ n m a b = 0 := by
    intro β m hm α a ha b
    have := wΛ.ext_of_hom (f := assocErrL₂ ν μ n m a) (f' := 0)
      (fun α' b hb ↦ h β α α' m a b hm ha hb)
    exact LinearMap.congr_fun this b
  have h2 : ∀ β m, wM.IsHom β m → ∀ a b, assocErr ν μ n m a b = 0 := by
    intro β m hm a b
    have := wΛ.ext_of_hom (f := assocErrL₁ ν μ n m b) (f' := 0)
      (fun α a ha ↦ h1 β m hm α a ha b)
    exact LinearMap.congr_fun this a
  have := wM.ext_of_hom (f := assocErrL ν μ n a b) (f' := 0) (fun β m hm ↦ h2 β m hm a b)
  exact LinearMap.congr_fun this m

variable (hW : WtCompat MM wΛ wM)
include hW

theorem act_coneBil : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 MM.act :=
  fun β α m a hm ha ↦ coneAt_of_isHom (by rw [add_zero]; exact hW.act β α m a hm ha)

theorem actFlip_shift {α : Wt} {b : Λ} (hb : wΛ.IsHom α b) : Shift wM wM α (MM.act.flip b) :=
  fun β m hm ↦ hW.act β α m b hm hb

/-- The cone part preserves the internal degree. -/
theorem cpart_isHom {σ : Wt} {p : ℤ} {m : M} (hm : MM.gr.IsHom p m) :
    MM.gr.IsHom p (cpart C wM σ m) := by
  unfold cpart
  rw [LinearMap.coe_sum, Finset.sum_apply]
  exact MM.gr.isHom_sum _ _ fun δ _ ↦ hW.projM δ p m hm

theorem isShift_cbil {n : ℤ} {D : M →ₗ[R] Λ →ₗ[R] M} (hD : IsShift MM n D) :
    IsShift MM n (cbil C wM wΛ wM 0 D) := by
  intro p q m a hm ha
  unfold cbil
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  exact MM.gr.isHom_sum _ _ fun β _ ↦ MM.gr.isHom_sum _ _ fun α _ ↦
    cpart_isHom hW (hD p q _ _ (hW.projM β p m hm) (hW.projΛ α q a ha))

theorem isShift_cbil' (ρ : Wt) {n : ℤ} {D : M →ₗ[R] Λ →ₗ[R] M} (hD : IsShift MM n D) :
    IsShift MM n (cbil C wM wΛ wM ρ D) := by
  intro p q m a hm ha
  unfold cbil
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  exact MM.gr.isHom_sum _ _ fun β _ ↦ MM.gr.isHom_sum _ _ fun α _ ↦
    cpart_isHom hW (hD p q _ _ (hW.projM β p m hm) (hW.projΛ α q a ha))

/-- **The correction equation commutes with the cone parts.** -/
theorem corr_cbil (D : M →ₗ[R] Λ →ₗ[R] M) {β α α' : Wt} {m : M} {a b : Λ} (hm : wM.IsHom β m)
    (ha : wΛ.IsHom α a) (hb : wΛ.IsHom α' b) :
    cbil C wM wΛ wM 0 D (MM.act m a) b + MM.act (cbil C wM wΛ wM 0 D m a) b -
        cbil C wM wΛ wM 0 D m (a * b) =
      cpart C wM (β + α + α') (D (MM.act m a) b + MM.act (D m a) b - D m (a * b)) := by
  rw [cbil_apply_hom 0 D (hW.act β α m a hm ha) hb, cbil_apply_hom 0 D hm ha,
    cbil_apply_hom 0 D hm (hW.mul α α' a b ha hb)]
  have hs := cpart_shift (C := C) (σ := β + α + 0) (actFlip_shift hW hb) (D m a)
  simp only [LinearMap.flip_apply] at hs
  rw [hs, map_sub, map_add]
  congr 2
  · congr 1; abel
  · congr 1; abel
  · congr 1; abel

omit hW in
theorem cpart_zero' {σ : Wt} : cpart C wM σ (0 : M) = 0 := map_zero _

omit hW in
theorem ConeAt.of_bot {G : MGr R Wt M} {σ : Wt} {n : M} (h : ConeAt ⊥ G σ n) : ConeAt C G σ n :=
  fun δ hδ ↦ h δ fun h' ↦ hδ ((AddSubmonoid.mem_bot.1 h') ▸ C.zero_mem)

omit hW in
theorem coneBil_sub {ρ : Wt} {φ ψ : M →ₗ[R] Λ →ₗ[R] M}
    (hφ : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ φ)
    (hψ : ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ ψ) :
    ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) ρ (φ - ψ) :=
  fun β α m a hm ha ↦ by
    simp only [LinearMap.sub_apply]; exact (hφ β α m a hm ha).sub (hψ β α m a hm ha)

/-- The correction removing the error, with relative weights in the cone minus `0`. -/
def corr (D : M →ₗ[R] Λ →ₗ[R] M) : M →ₗ[R] Λ →ₗ[R] M :=
  cbil C wM wΛ wM 0 D - cbil ⊥ wM wΛ wM 0 D

omit hW in
theorem coneBil_corr (D : M →ₗ[R] Λ →ₗ[R] M) :
    ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (corr (C := C) (wΛ := wΛ) (wM := wM) D) :=
  coneBil_sub (coneBil_cbil 0 D) fun β α m a hm ha ↦ ConeAt.of_bot (coneBil_cbil 0 D β α m a hm ha)

omit hW in
theorem corr_bottom (D : M →ₗ[R] Λ →ₗ[R] M) {β α : Wt} {m : M} {a : Λ} (hm : wM.IsHom β m)
    (ha : wΛ.IsHom α a) : wM.proj (β + α) (corr (C := C) (wΛ := wΛ) (wM := wM) D m a) = 0 := by
  simp only [corr, LinearMap.sub_apply, map_sub]
  rw [cbil_apply_hom 0 D hm ha, cbil_apply_hom 0 D hm ha, proj_cpart, proj_cpart, add_zero,
    sub_self, if_pos C.zero_mem, if_pos (AddSubmonoid.zero_mem _), sub_self]

theorem isShift_corr {n : ℤ} {D : M →ₗ[R] Λ →ₗ[R] M} (hD : IsShift MM n D) :
    IsShift MM n (corr (C := C) (wΛ := wΛ) (wM := wM) D) := by
  intro p q m a hm ha
  simp only [corr, LinearMap.sub_apply, sub_eq_add_neg]
  exact MM.gr.isHom_add (isShift_cbil (C := C) hW hD p q m a hm ha)
    (MM.gr.isHom_neg (isShift_cbil (C := ⊥) hW hD p q m a hm ha))

variable (hCp : ∀ γ ∈ C, ∀ δ ∈ C, γ + δ = 0 → γ = 0)

omit hW in
include hCp in
/-- **The error has no bottom component** when the lower corrections have none. -/
theorem assocErr_bottom {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} {μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ}
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hμ : ∀ j, ConeBil (C := C) (G := wΛ) (G' := wΛ) (G'' := wΛ) 0 (μ j))
    (hν0 : ∀ m a, ν 0 m a = MM.act m a) (hμ0 : ∀ a b, μ 0 a b = a * b)
    (hW : WtCompat MM wΛ wM)
    (hνb : ∀ i, 1 ≤ i → ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.proj (β + α) (ν i m a) = 0)
    (hμb : ∀ j, 1 ≤ j → ∀ α α' a b, wΛ.IsHom α a → wΛ.IsHom α' b →
      wΛ.proj (α + α') (μ j a b) = 0)
    {n : ℕ} (hn : 1 ≤ n) {β α α' : Wt} {m : M} {a b : Λ} (hm : wM.IsHom β m) (ha : wΛ.IsHom α a)
    (hb : wΛ.IsHom α' b) : wM.proj (β + α + α') (assocErr ν μ n m a b) = 0 := by
  unfold assocErr
  rw [map_sub, map_sum, map_sum]
  have z1 : ∀ x ∈ antidiagonal n, wM.proj (β + α + α') (ν x.2 (ν x.1 m a) b) = 0 := by
    intro x hx
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have e := (hν x.2).proj_bottom hCp (ConeAt.congr' (hν x.1 β α m a hm ha) (add_zero _))
      (coneAt_of_isHom hb)
    rw [add_zero] at e
    rw [e]
    rcases Nat.eq_zero_or_pos x.1 with h0 | h0
    · rw [h0, hν0, (hW.act β α m a hm ha), hb]
      exact hνb x.2 (by omega) _ _ _ _ (hW.act β α m a hm ha) hb
    · rw [hνb x.1 h0 β α m a hm ha, LinearMap.map_zero₂, map_zero]
  have z2 : ∀ x ∈ antidiagonal n, wM.proj (β + α + α') (ν x.1 m (μ x.2 a b)) = 0 := by
    intro x hx
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have e := (hν x.1).proj_bottom hCp (coneAt_of_isHom hm)
      (ConeAt.congr' (hμ x.2 α α' a b ha hb) (add_zero _))
    rw [add_zero, ← add_assoc] at e
    rw [e]
    rcases Nat.eq_zero_or_pos x.2 with h0 | h0
    · rw [h0, hμ0, (hW.mul α α' a b ha hb), hm]
      have := hνb x.1 (by omega) _ _ _ _ hm (hW.mul α α' a b ha hb)
      rwa [← add_assoc] at this
    · rw [hμb x.2 h0 α α' a b ha hb, map_zero, map_zero]
  rw [Finset.sum_eq_zero z1, Finset.sum_eq_zero z2, sub_zero]

section Actions

variable (P : PosDef GΛ) (hP : ∀ q, ConeBil (C := C) (G := wΛ) (G' := wΛ) (G'' := wΛ) 0 (P.μ q))
  (hPb : ∀ q, 1 ≤ q → ∀ α α' a b, wΛ.IsHom α a → wΛ.IsHom α' b →
    wΛ.proj (α + α') (P.μ q a b) = 0)
include hP hCp hPb

variable (MM) in
/-- **The degree-by-degree construction with homogeneous choices**, without corrections of
relative weight `0`. -/
theorem exists_partial_cone (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM MM 1 t) (N : ℕ) :
    ∃ ν : ℕ → M →ₗ[R] Λ →ₗ[R] M, (∀ m a, ν 0 m a = MM.act m a) ∧
      (∀ n : ℕ, IsShift MM n (ν n)) ∧ (∀ n, N < n → ν n = 0) ∧
        (∀ n ≤ N, ∀ m a b, assocErr ν P.μ n m a b = 0) ∧
        (∀ n, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν n)) ∧
        ∀ n, 1 ≤ n → ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.proj (β + α) (ν n m a) = 0 := by
  classical
  induction N with
  | zero =>
    obtain ⟨ν, hν0, hν, hνN, hνa⟩ := exists_partial MM P hExt 0
    refine ⟨ν, hν0, hν, hνN, hνa, fun n ↦ ?_, fun n hn β α m a _ _ ↦ ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have : ν 0 = MM.act := LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ hν0 m a
        rw [this]; exact act_coneBil hW
      · rw [hνN n hn]
        intro β α m a _ _
        exact ConeAt.zero _
    · rw [hνN n hn]; simp
  | succ N ih =>
    obtain ⟨ν, hν0, hν, hνN, hνa, hνc, hνb⟩ := ih
    obtain ⟨H, hH, hdH⟩ := hExt (N + 1) (by omega) (errCoch ν P.μ (N + 1))
      (errCoch_good hν P (N + 1))
      (errCoch_d hν0 P (N + 1) fun l hl ↦ hνa l (by omega))
    let D : M →ₗ[R] Λ →ₗ[R] M := -cochBil hH
    have hDs : IsShift MM (N + 1 : ℕ) D := by
      intro p q m a hm ha
      have := hH.deg (single a) (fun _ ↦ q) p m (fun i hi ↦ by
        obtain rfl : i = 0 := by omega
        simpa [single, Bar.cons] using ha) hm
      simp only [Finset.sum_range_one] at this
      simp only [D, LinearMap.neg_apply, cochBil_apply]
      exact MM.gr.isHom_neg (by push_cast at this ⊢; exact this)
    have hDa : ∀ m a b, assocErr (Function.update ν (N + 1) D) P.μ (N + 1) m a b = 0 := by
      intro m a b
      rw [assocErr_update P.μ (by omega) (hνN (N + 1) (by omega)) D]
      have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (Bar.cons a (single b)) m)
        hdH
      simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l,
        homAct_r, errCoch_apply] at h1
      rw [hH.one_eq (Bar.sh _), hH.one_eq (Bar.ct 0 _), hH.one_eq (Bar.tr 1 _)] at h1
      simp only [Bar.sh_cons, Bar.ct_zero_cons, Bar.cons_zero, Bar.tr_cons] at h1
      simp only [D, LinearMap.neg_apply, cochBil_apply, map_neg, LinearMap.neg_apply, hν0,
        P.μ_zero]
      simp only [single, Bar.cons_zero, Bar.cons, Bar.sh, Bar.tr] at h1 ⊢
      norm_num at h1 ⊢
      rw [← h1]
      abel
    let D' : M →ₗ[R] Λ →ₗ[R] M := corr (C := C) (wΛ := wΛ) (wM := wM) D
    refine ⟨Function.update ν (N + 1) D', fun m a ↦ ?_, fun n ↦ ?_, fun n hn ↦ ?_,
      fun n hn m a b ↦ ?_, fun n ↦ ?_, fun n hn β α m a hm ha ↦ ?_⟩
    · rw [Function.update_of_ne (by omega), hν0]
    · by_cases hn : n = N + 1
      · subst hn; rw [Function.update_self]; exact isShift_corr hW hDs
      · rw [Function.update_of_ne hn]; exact hν n
    · rw [Function.update_of_ne (by omega), hνN n (by omega)]
    · rcases Nat.lt_or_ge n (N + 1) with hlt | hge
      · rw [assocErr_congr (ν := ν) (ν' := Function.update ν (N + 1) D') P.μ (n := n)
          (fun i hi ↦ Function.update_of_ne (by omega) _ _)]
        exact hνa n (by omega) m a b
      · obtain rfl : n = N + 1 := by omega
        refine assocErr_eq_zero_of_wt (wΛ := wΛ) (wM := wM) _ P.μ (N + 1)
          (fun β α α' m a b hm ha hb ↦ ?_) m a b
        have hE := assocErr_coneAt (C := C) hνc hP (N + 1) hm ha hb
        have hEb := assocErr_bottom hCp hνc hP hν0 P.μ_zero hW hνb hPb (n := N + 1) (by omega)
          hm ha hb
        have e2 := assocErr_update P.μ (n := N + 1) (by omega) (hνN (N + 1) (by omega)) D m a b
        rw [hDa] at e2
        rw [assocErr_update P.μ (n := N + 1) (by omega) (hνN (N + 1) (by omega)) D' m a b]
        have hcC := corr_cbil (C := C) hW D hm ha hb
        have hcB := corr_cbil (C := ⊥) hW D hm ha hb
        simp only [hν0, P.μ_zero] at e2 hcC hcB ⊢
        have eL : D' (MM.act m a) b + MM.act (D' m a) b - D' m (a * b) =
            (cbil C wM wΛ wM 0 D (MM.act m a) b + MM.act (cbil C wM wΛ wM 0 D m a) b -
              cbil C wM wΛ wM 0 D m (a * b)) -
            (cbil ⊥ wM wΛ wM 0 D (MM.act m a) b + MM.act (cbil ⊥ wM wΛ wM 0 D m a) b -
              cbil ⊥ wM wΛ wM 0 D m (a * b)) := by
          simp only [D', corr, LinearMap.sub_apply, map_sub]; abel
        rw [eL, hcC, hcB, cpart_bot]
        have hLD : D (MM.act m a) b + MM.act (D m a) b - D m (a * b) =
            -assocErr ν P.μ (N + 1) m a b := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact e2.symm
        rw [hLD, map_neg, map_neg, cpart_of_coneAt hE, hEb]
        abel
    · by_cases hn : n = N + 1
      · subst hn; rw [Function.update_self]; exact coneBil_corr D
      · rw [Function.update_of_ne hn]; exact hνc n
    · by_cases hn' : n = N + 1
      · subst hn'; rw [Function.update_self]; exact corr_bottom D hm ha
      · rw [Function.update_of_ne hn']; exact hνb n hn β α m a hm ha

variable (MM) in
/-- **Proposition 6.5(1) with homogeneous choices**: a lifted action whose corrections all have
relative weights in the cone minus `0`. -/
theorem exists_actFam_cone (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q)
    (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM MM 1 t) :
    ∃ L : ActFam P MM, (∀ n, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (L.ν n)) ∧
      ∀ n, 1 ≤ n → ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.proj (β + α) (L.ν n m a) = 0 := by
  obtain ⟨ν, hν0, hν, -, hνa, hνc, hνb⟩ :=
    exists_partial_cone MM hW hCp P hP hPb hExt (2 * degBound MM.gr)
  refine ⟨⟨ν, hν0, hν, fun n m a b ↦ ?_⟩, hνc, hνb⟩
  rcases Nat.lt_or_ge (2 * degBound MM.gr) n with hn | hn
  · refine assocErr_eq_zero_of_hom (MM := MM) ν P.μ n (fun p q r m a b hm ha hb ↦ ?_) m a b
    by_cases hp : p ∈ MM.gr.supp
    · by_cases hq : q ∈ GΛ.gr.supp
      · by_cases hr : r ∈ GΛ.gr.supp
        · refine MM.gr.eq_zero_of_isHom_out (assocErr_isHom hν P n hm ha hb) fun hmem ↦ ?_
          have h1 := le_degBound hp
          have h2 := le_degBound hmem
          have h3 := hnn q hq
          have h4 := hnn r hr
          rw [abs_le] at h1 h2
          omega
        · rw [GΛ.gr.eq_zero_of_isHom_out hb hr, ← zero_smul R (0 : Λ),
            assocErr_smul_right, zero_smul]
      · rw [GΛ.gr.eq_zero_of_isHom_out ha hq, ← zero_smul R (0 : Λ), assocErr_smul_mid,
          zero_smul]
    · rw [MM.gr.eq_zero_of_isHom_out hm hp]
      simpa using assocErr_smul_left ν P.μ n (0 : R) (0 : M) a b
  · exact hνa n hn m a b

end Actions

/-! ### Weight-homogeneous lifts of maps -/

section Maps

variable {N : Type*} [AddCommGroup N] [Module R N] {NN : GMod GΛ N} {wN : MGr R Wt N}

omit hW in
theorem interErr_coneAt {F : ℕ → M →ₗ[R] N} {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M}
    {ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N} {ρ : Wt}
    (hF : ∀ i, ConeLin (C := C) (G := wM) (G' := wN) ρ (F i))
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hν' : ∀ i, ConeBil (C := C) (G := wN) (G' := wΛ) (G'' := wN) 0 (ν' i)) (n : ℕ)
    {β α : Wt} {m : M} {a : Λ} (hm : wM.IsHom β m) (ha : wΛ.IsHom α a) :
    ConeAt C wN (β + α + ρ) (interErr F ν ν' n m a) := by
  unfold interErr
  refine ConeAt.sub (ConeAt.sum _ fun x _ ↦ ?_) (ConeAt.sum _ fun x _ ↦ ?_)
  · exact ConeAt.congr' ((hF x.2).apply (hν x.1 β α m a hm ha)) (by abel)
  · exact ConeAt.congr' ((hν' x.1).apply (hF x.2 β m hm) (coneAt_of_isHom ha)) (by abel)

omit hW in
theorem interErr_eq_zero_of_wt (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) (n : ℕ)
    (h : ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → interErr F ν ν' n m a = 0) (m : M) (a : Λ) :
    interErr F ν ν' n m a = 0 := by
  have h1 : ∀ β m, wM.IsHom β m → ∀ a, interErr F ν ν' n m a = 0 := by
    intro β m hm a
    have := wΛ.ext_of_hom (f := interErrL₁ F ν ν' n m) (f' := 0) (fun α a ha ↦ h β α m a hm ha)
    exact LinearMap.congr_fun this a
  have := wM.ext_of_hom (f := interErrL F ν ν' n a) (f' := 0) (fun β m hm ↦ h1 β m hm a)
  exact LinearMap.congr_fun this m

variable (hW' : WtCompat NN wΛ wN)

include hW' in
theorem clin_isHom {ρ : Wt} {r : ℤ} {D : M →ₗ[R] N}
    (hD : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (D m)) :
    ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (clin C wM wN ρ D m) := by
  intro p m hm
  unfold clin
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  exact NN.gr.isHom_sum _ _ fun β _ ↦ cpart_isHom hW' (hD p _ (hW.projM β p m hm))

include hW' in
/-- **The map correction equation commutes with the cone parts.** -/
theorem corrMap_clin (ρ : Wt) (D : M →ₗ[R] N) {β α : Wt} {m : M} {a : Λ} (hm : wM.IsHom β m)
    (ha : wΛ.IsHom α a) :
    clin C wM wN ρ D (MM.act m a) - NN.act (clin C wM wN ρ D m) a =
      cpart C wN (β + α + ρ) (D (MM.act m a) - NN.act (D m) a) := by
  rw [clin_apply_hom ρ D (hW.act β α m a hm ha), clin_apply_hom ρ D hm]
  have hs := cpart_shift (C := C) (σ := β + ρ) (actFlip_shift hW' ha) (D m)
  simp only [LinearMap.flip_apply] at hs
  rw [hs, map_sub]
  congr 2; abel

omit hW in
include hCp in
/-- **The linearity error has no bottom component** when the lower corrections have none. -/
theorem interErr_bottom {F : ℕ → M →ₗ[R] N} {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M}
    {ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N} {ρ : Wt}
    (hF : ∀ i, ConeLin (C := C) (G := wM) (G' := wN) ρ (F i))
    (hν : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (ν i))
    (hν' : ∀ i, ConeBil (C := C) (G := wN) (G' := wΛ) (G'' := wN) 0 (ν' i))
    (hν0 : ∀ m a, ν 0 m a = MM.act m a) (hW : WtCompat MM wΛ wM)
    (hF0 : ∀ β m, wM.IsHom β m → wN.IsHom (β + ρ) (F 0 m))
    (hFb : ∀ i, 1 ≤ i → ∀ β m, wM.IsHom β m → wN.proj (β + ρ) (F i m) = 0)
    (hνb : ∀ i, 1 ≤ i → ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.proj (β + α) (ν i m a) = 0)
    (hν'b : ∀ i, 1 ≤ i → ∀ β α m a, wN.IsHom β m → wΛ.IsHom α a →
      wN.proj (β + α) (ν' i m a) = 0)
    {n : ℕ} (hn : 1 ≤ n) {β α : Wt} {m : M} {a : Λ} (hm : wM.IsHom β m) (ha : wΛ.IsHom α a) :
    wN.proj (β + α + ρ) (interErr F ν ν' n m a) = 0 := by
  unfold interErr
  rw [map_sub, map_sum, map_sum]
  have z1 : ∀ x ∈ antidiagonal n, wN.proj (β + α + ρ) (F x.2 (ν x.1 m a)) = 0 := by
    intro x hx
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have e := (hF x.2).proj_bottom hCp (ConeAt.congr' (hν x.1 β α m a hm ha) (add_zero _))
    rw [e]
    rcases Nat.eq_zero_or_pos x.1 with h0 | h0
    · rw [h0, hν0, (hW.act β α m a hm ha)]
      exact hFb x.2 (by omega) _ _ (hW.act β α m a hm ha)
    · rw [hνb x.1 h0 β α m a hm ha, map_zero, map_zero]
  have z2 : ∀ x ∈ antidiagonal n, wN.proj (β + α + ρ) (ν' x.1 (F x.2 m) a) = 0 := by
    intro x hx
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have e := (hν' x.1).proj_bottom hCp (hF x.2 β m hm) (coneAt_of_isHom ha)
    rw [show β + ρ + α + 0 = β + α + ρ by abel] at e
    rw [e]
    rcases Nat.eq_zero_or_pos x.2 with h0 | h0
    · rw [h0, ha]
      have := hν'b x.1 (by omega) (β + ρ) α (wN.proj (β + ρ) (F 0 m)) a (wN.isHom_proj _ _) ha
      rwa [show β + ρ + α = β + α + ρ by abel] at this
    · rw [hFb x.2 h0 β m hm, LinearMap.map_zero₂, map_zero]
  rw [Finset.sum_eq_zero z1, Finset.sum_eq_zero z2, sub_zero]

variable (P : PosDef GΛ) (L : ActFam P MM) (L' : ActFam P NN)
  (hL : ∀ i, ConeBil (C := C) (G := wM) (G' := wΛ) (G'' := wM) 0 (L.ν i))
  (hL' : ∀ i, ConeBil (C := C) (G := wN) (G' := wΛ) (G'' := wN) 0 (L'.ν i))
  (hLb : ∀ i, 1 ≤ i → ∀ β α m a, wM.IsHom β m → wΛ.IsHom α a → wM.proj (β + α) (L.ν i m a) = 0)
  (hL'b : ∀ i, 1 ≤ i → ∀ β α m a, wN.IsHom β m → wΛ.IsHom α a →
    wN.proj (β + α) (L'.ν i m a) = 0)
  {r : ℤ} {ρ : Wt} (f : M →ₗ[R] N)
  (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
  (hfd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
  (hfc : ∀ β m, wM.IsHom β m → wN.IsHom (β + ρ) (f m))

omit hW in
theorem coneLin_of_shift {g : M →ₗ[R] N} (hg : ∀ β m, wM.IsHom β m → wN.IsHom (β + ρ) (g m)) :
    ConeLin (C := C) (G := wM) (G' := wN) ρ g := fun β m hm ↦ coneAt_of_isHom (hg β m hm)

/-- The map correction with relative weights in the cone minus `0`. -/
def corrMap (D : M →ₗ[R] N) : M →ₗ[R] N := clin C wM wN ρ D - clin ⊥ wM wN ρ D

include hCp hW' hL hL' hLb hL'b hf hfd hfc in
/-- **The degree-by-degree lift of a map with homogeneous choices**, without corrections of
relative weight `0`. -/
theorem exists_partialMap_cone (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM NN 0 (r + t)) (K : ℕ) :
    ∃ F : ℕ → M →ₗ[R] N, F 0 = f ∧
      (∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m)) ∧
        (∀ n, K < n → F n = 0) ∧ (∀ n ≤ K, ∀ m a, interErr F L.ν L'.ν n m a = 0) ∧
        (∀ i, ConeLin (C := C) (G := wM) (G' := wN) ρ (F i)) ∧
        ∀ i, 1 ≤ i → ∀ β m, wM.IsHom β m → wN.proj (β + ρ) (F i m) = 0 := by
  classical
  induction K with
  | zero =>
    obtain ⟨F, hF0, hF, hFK, hFa⟩ := exists_partialMap P L L' f hf hfd hExt 0
    refine ⟨F, hF0, hF, hFK, hFa, fun i ↦ ?_, fun i hi β m _ ↦ ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [hF0]; exact coneLin_of_shift hfc
      · rw [hFK i hi]; intro β m _; exact ConeAt.zero _
    · rw [hFK i hi]; simp
  | succ K ih =>
    obtain ⟨F, hF0, hF, hFK, hFa, hFc, hFb⟩ := ih
    obtain ⟨H, hH, hdH⟩ := hExt (K + 1) (by omega) (interCoch F L.ν L'.ν (K + 1))
      (by simpa using interCoch_good hF L.deg L'.deg (K + 1))
      (interCoch_d P L L' (K + 1) fun l hl ↦ hFa l (by omega))
    let D : M →ₗ[R] N := -H (fun _ ↦ 0)
    have hH0 : ∀ b : ℕ → Λ, H b = H (fun _ ↦ 0) := fun b ↦ by
      rw [hH.tr b]; congr 1
    have hDd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + (r + (K + 1 : ℕ))) (D m) := by
      intro p m hm
      have := hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
      simp only [Finset.sum_range_zero, add_zero] at this
      simp only [D, LinearMap.neg_apply]
      exact NN.gr.isHom_neg (by push_cast at this ⊢; convert this using 1)
    have hDa : ∀ m a, interErr (Function.update F (K + 1) D) L.ν L'.ν (K + 1) m a = 0 := by
      intro m a
      rw [interErr_update L.ν L'.ν (hFK (K + 1) (by omega)) D]
      have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
      simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r,
        interCoch_apply] at h1
      rw [hH0 (Bar.sh _), hH0 (Bar.tr 0 _)] at h1
      simp only [D, LinearMap.neg_apply, map_neg, L.ν_zero, L'.ν_zero, LinearMap.neg_apply]
      simp only [single, Bar.cons_zero] at h1
      rw [← h1]
      abel
    let D' : M →ₗ[R] N := corrMap (C := C) (wM := wM) (wN := wN) (ρ := ρ) D
    refine ⟨Function.update F (K + 1) D', by rw [Function.update_of_ne (by omega), hF0],
      fun i p m hm ↦ ?_, fun n hn ↦ ?_, fun n hn m a ↦ ?_, fun i ↦ ?_, fun i hi β m hm ↦ ?_⟩
    · by_cases hi : i = K + 1
      · subst hi
        rw [Function.update_self]
        have h1 := clin_isHom (C := C) hW hW' (ρ := ρ) hDd p m hm
        have h2 := clin_isHom (C := ⊥) hW hW' (ρ := ρ) hDd p m hm
        change NN.gr.IsHom _ (clin C wM wN ρ D m - clin ⊥ wM wN ρ D m)
        rw [sub_eq_add_neg]
        rw [← add_assoc] at h1 h2
        exact NN.gr.isHom_add h1 (NN.gr.isHom_neg h2)
      · rw [Function.update_of_ne hi]; exact hF i p m hm
    · rw [Function.update_of_ne (by omega), hFK n (by omega)]
    · rcases Nat.lt_or_ge n (K + 1) with hlt | hge
      · rw [interErr_congr (F := F) (F' := Function.update F (K + 1) D') L.ν L'.ν (n := n)
          (fun i hi ↦ Function.update_of_ne (by omega) _ _)]
        exact hFa n (by omega) m a
      · obtain rfl : n = K + 1 := by omega
        refine interErr_eq_zero_of_wt (wΛ := wΛ) (wM := wM) _ L.ν L'.ν (K + 1)
          (fun β α m a hm ha ↦ ?_) m a
        have hE := interErr_coneAt (C := C) hFc hL hL' (K + 1) hm ha
        have hEb := interErr_bottom hCp hFc hL hL' L.ν_zero hW (by rw [hF0]; exact hfc) hFb hLb
          hL'b (n := K + 1) (by omega) hm ha
        have e2 := interErr_update L.ν L'.ν (hFK (K + 1) (by omega)) D m a
        rw [hDa] at e2
        rw [interErr_update L.ν L'.ν (hFK (K + 1) (by omega)) D' m a]
        simp only [L.ν_zero, L'.ν_zero] at e2 ⊢
        have eL : D' (MM.act m a) - NN.act (D' m) a =
            (clin C wM wN ρ D (MM.act m a) - NN.act (clin C wM wN ρ D m) a) -
            (clin ⊥ wM wN ρ D (MM.act m a) - NN.act (clin ⊥ wM wN ρ D m) a) := by
          simp only [D', corrMap, LinearMap.sub_apply, map_sub]; abel
        rw [eL, corrMap_clin hW hW' ρ D hm ha, corrMap_clin (C := ⊥) hW hW' ρ D hm ha, cpart_bot]
        have hLD : D (MM.act m a) - NN.act (D m) a = -interErr F L.ν L'.ν (K + 1) m a := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact e2.symm
        rw [hLD, map_neg, map_neg, cpart_of_coneAt hE, hEb]
        abel
    · by_cases hi : i = K + 1
      · subst hi; rw [Function.update_self]
        intro β m hm
        simp only [D', corrMap, LinearMap.sub_apply]
        exact (coneLin_clin ρ D β m hm).sub (ConeAt.of_bot (coneLin_clin ρ D β m hm))
      · rw [Function.update_of_ne hi]; exact hFc i
    · by_cases hi' : i = K + 1
      · subst hi'; rw [Function.update_self]
        simp only [D', corrMap, LinearMap.sub_apply, map_sub]
        rw [clin_apply_hom ρ D hm, clin_apply_hom ρ D hm, proj_cpart, proj_cpart, sub_self,
          if_pos C.zero_mem, if_pos (AddSubmonoid.zero_mem _), sub_self]
      · rw [Function.update_of_ne hi']; exact hFb i hi β m hm

include hCp hW' hL hL' hLb hL'b hf hfd hfc in
/-- **Proposition 6.5(2) with homogeneous choices.** -/
theorem exists_liftMap_cone (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q)
    (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM NN 0 (r + t)) :
    ∃ F : ℕ → M →ₗ[R] N, F 0 = f ∧
      (∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m)) ∧
        (∀ n m a, interErr F L.ν L'.ν n m a = 0) ∧
        (∀ i, ConeLin (C := C) (G := wM) (G' := wN) ρ (F i)) ∧
        ∀ i, 1 ≤ i → ∀ β m, wM.IsHom β m → wN.proj (β + ρ) (F i m) = 0 := by
  obtain ⟨F, hF0, hF, -, hFa, hFc, hFb⟩ := exists_partialMap_cone hW hCp hW' P L L' hL hL' hLb
    hL'b f hf hfd hfc hExt (degBound MM.gr + degBound NN.gr + r.natAbs)
  refine ⟨F, hF0, hF, fun n m a ↦ ?_, hFc, hFb⟩
  rcases Nat.lt_or_ge (degBound MM.gr + degBound NN.gr + r.natAbs) n with hn | hn
  · refine interErr_eq_zero_of_hom (MM := MM) F L.ν L'.ν n (fun p q m a hm ha ↦ ?_) m a
    by_cases hp : p ∈ MM.gr.supp
    · by_cases hq : q ∈ GΛ.gr.supp
      · refine NN.gr.eq_zero_of_isHom_out (interErr_isHom hF L.deg L'.deg n hm ha) fun hmem ↦ ?_
        have h1 := le_degBound hp
        have h2 := le_degBound hmem
        have h3 := hnn q hq
        rw [abs_le] at h1 h2
        have h4 : (r.natAbs : ℤ) = |r| := Int.natCast_natAbs r
        have h5 := le_abs_self r
        have h6 := neg_abs_le r
        omega
      · rw [GΛ.gr.eq_zero_of_isHom_out ha hq]
        exact (interErrL₁ F L.ν L'.ν n m).map_zero
    · rw [MM.gr.eq_zero_of_isHom_out hm hp]
      exact (interErrL F L.ν L'.ν n a).map_zero
  · exact hFa n hn m a

end Maps

end GExt

end MultiplicativeBasisDeformations
