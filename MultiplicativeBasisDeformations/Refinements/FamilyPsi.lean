import MultiplicativeBasisDeformations.Refinements.FamilyTwist

/-!
# The retained coefficients are nonzero (Proposition 12.8, `a_i ∈ k^*`)

`deformation-refinements.tex`: "Specializing `t_j = ε`, all other parameters zero and
`ε² = 0`, identifies `a_j[p_j]` with `Ψ[μ_j]`. This is nonzero because `Ψ` is injective
(Proposition 7.6). Hence `a_j ≠ 0`."

At `t = 1` the lifts have relative weights in the cone `C` of the `χ_i`, and `χ_j` is an atom of
`C`. The components of relative weight `χ_j` (and internal degree `q_j`) of the lifted actions
and arrows are therefore the square-zero lifts of Lemma 6.6 for `μ_j` (`ν1`, `y1`), i.e. the
specialization `t = ε e_j`; their mesh errors are `λ_j R_j` (`zE_psi`). So `Ψ[μ_j] = λ_j [R_j]`,
and `λ_j ≠ 0` because `μ_j` is not a coboundary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr PathReal

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)} [Fintype Q.nonprojective]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {I : Type} [Fintype I] [DecidableEq I]
  {μ : I → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ} {qd : I → ℕ}
  {H : FamHyp D hfin μ qd}
  {Wt : Type} [AddCommGroup Wt] {W : MeshWt Q Wt} {χ : I → Wt} {coords : Wt →+ (I → ℤ)}
  {hχ : ∀ i, HasChar W hfin D (χ i) (μ i)} {J : D.InjData} {h1 : DegOne D}
  {hco : ∀ i, coords (χ i) = Pi.single i 1} [Infinite k]

/-! ### The cocycle condition -/

omit [Fintype Q.nonprojective] [Infinite k] in
theorem famMul_single (j : I) (s : k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    famMul D μ (Pi.single j s) a b = a * b + s • μ j a b := by
  rw [famMul_apply, Finset.sum_eq_single j (fun i _ hi ↦ by simp [Pi.single_eq_of_ne hi])
    (fun h ↦ absurd (Finset.mem_univ j) h), Pi.single_eq_same]

variable (H) in
include H in
omit [Fintype Q.nonprojective] in
/-- **Each `μ_j` is a Hochschild cocycle**: the linear term of associativity in `t_j`. -/
theorem famHyp_cocycle (j : I) : IsHCocycle (μ j) := by
  intro a b c
  obtain ⟨s0, hs0⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have h0 : s0 ≠ 0 := fun h ↦ hs0 (by simp [h])
  have h1' : s0 ≠ 1 := fun h ↦ hs0 (by simp [h])
  set B := μ j a b * c + μ j (a * b) c - a * μ j b c - μ j a (b * c)
  set C := μ j (μ j a b) c - μ j a (μ j b c)
  have key : ∀ s : k, s • B + (s * s) • C = 0 := by
    intro s
    have := H.assoc (Pi.single j s) a b c
    simp only [famMul_single, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul] at this
    simp only [B, C, smul_sub, smul_add]
    rw [mul_assoc] at this
    linear_combination (norm := module) this
  have e1 := key 1
  have e2 := key s0
  simp only [one_smul, one_mul] at e1
  have hC : C = 0 := by
    have : (s0 * s0 - s0) • C = 0 := by
      have e3 : s0 • B + (s0 * s0) • C - s0 • (B + C) = 0 := by rw [e2, e1, smul_zero, sub_zero]
      rw [← e3]; module
    rcases smul_eq_zero.1 this with h | h
    · exfalso
      have : s0 * (s0 - 1) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.1 this with h' | h'
      · exact h0 h'
      · exact h1' (sub_eq_zero.1 h')
    · exact h
  have hB : B = 0 := by rw [hC, add_zero] at e1; exact e1
  have : a * μ j b c - μ j (a * b) c + μ j a (b * c) - μ j a b * c = -B := by
    simp only [B]; abel
  rw [this, hB, neg_zero]

/-! ### The atoms of the cone -/

omit [Fintype Q.nonprojective] [Infinite k] in
theorem χ_injective (hco : ∀ i, coords (χ i) = Pi.single i 1) : Function.Injective χ := by
  intro i j h
  have := congrFun (hco i) i
  rw [h, hco j] at this
  by_contra hij
  simp [Pi.single_eq_of_ne hij] at this

omit [Fintype Q.nonprojective] [Infinite k] in
/-- **`χ_j` is an atom of the cone.** -/
theorem χ_atom (hco : ∀ i, coords (χ i) = Pi.single i 1) (j : I) :
    ∀ u ∈ cone χ, ∀ v ∈ cone χ, u + v = χ j → u = 0 ∨ v = 0 := by
  intro u hu v hv h
  have hu0 := cone_nonneg hco u hu
  have hv0 := cone_nonneg hco v hv
  have hs : ∀ i, coords u i + coords v i = if i = j then 1 else 0 := by
    intro i
    have := congrFun (congrArg coords h) i
    rw [map_add, Pi.add_apply, hco j] at this
    rw [this]; by_cases hi : i = j <;> simp [hi, Pi.single_apply]
  have hz : ∀ w ∈ cone χ, coords w = 0 → w = 0 := fun w hw hw0 ↦ by
    rw [cone_eq_sum hco w hw, hw0]; simp
  by_cases huj : coords u j = 0
  · left
    refine hz u hu (funext fun i ↦ ?_)
    have := hs i; have := hu0 i; have := hv0 i
    by_cases hi : i = j
    · subst hi; simpa using huj
    · simp only [hi, if_false] at *; simp; omega
  · right
    refine hz v hv (funext fun i ↦ ?_)
    have := hs i; have := hu0 i; have := hv0 i
    by_cases hi : i = j
    · subst hi; simp at *; omega
    · simp only [hi, if_false] at *; simp; omega

omit [Fintype Q.nonprojective] [Infinite k] in
theorem eq_of_χ_sub_mem (hco : ∀ i, coords (χ i) = Pi.single i 1) {i j : I}
    (h : χ j - χ i ∈ cone χ) : i = j := by
  rcases χ_atom hco j (χ i) (AddSubmonoid.subset_closure ⟨i, rfl⟩) _ h (by abel) with h' | h'
  · exact absurd h' (χ_ne_zero hco i)
  · exact χ_injective hco (sub_eq_zero.1 h').symm

/-! ### The `χ_j`-parts of the lifted actions -/

omit [Fintype Q.nonprojective] [Infinite k] in
theorem sum_antidiag_fst {X : Type*} [AddCommMonoid X] (n : ℕ) (f : ℕ × ℕ → X) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, (if x.1 = 0 then f x else 0) = f (0, n) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : (Finset.HasAntidiagonal.antidiagonal n).filter (fun x ↦ x.1 = 0) = {(0, n)} := by
    ext x
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext h2 (by omega)
    · rintro rfl; simp
  rw [this, Finset.sum_singleton]

omit [Fintype Q.nonprojective] [Infinite k] in
theorem sum_antidiag_snd {X : Type*} [AddCommMonoid X] (n : ℕ) (f : ℕ × ℕ → X) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, (if x.2 = 0 then f x else 0) = f (n, 0) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : (Finset.HasAntidiagonal.antidiagonal n).filter (fun x ↦ x.2 = 0) = {(n, 0)} := by
    ext x
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact Prod.ext (by omega) h2
    · rintro rfl; simp
  rw [this, Finset.sum_singleton]

variable (H W hχ J h1 hco) in
/-- **The first-order action** `ν = (ν_{q_j})_{χ_j}`, the `t_j`-linear part of the lifted action. -/
def ν1 (j : I) (X : V) : Rep D.F0 (meshFam Q c X) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c X) :=
  cbil ⊥ (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) (χ j)
    ((act1 H W hχ J h1 hco X).ν (qd j))

theorem ν1_hom (j : I) (X : V) {β α : Wt} {m : Rep D.F0 (meshFam Q c X)} {a : (Alg D.F0)ᵐᵒᵖ}
    (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a) :
    ν1 H W hχ J h1 hco j X m a =
      (grEv W hfin D X).proj (β + α + χ j) ((act1 H W hχ J h1 hco X).ν (qd j) m a) := by
  rw [ν1, cbil_apply_hom _ _ hm ha, cpart_bot]

theorem act_isHom (X : V) {β α : Wt} {m : Rep D.F0 (meshFam Q c X)} {a : (Alg D.F0)ᵐᵒᵖ}
    (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a) :
    (grEv W hfin D X).IsHom (β + α) ((gmodEv D hfin X).act m a) :=
  (wtCompat D hfin W X).act β α m a hm ha

/-- The atom component of `ν_l(ν_{j'}(m, a), b)`. -/
theorem proj_νν (j : I) (X : V) (l j' : ℕ) {β α α' : Wt} {m : Rep D.F0 (meshFam Q c X)}
    {a b : (Alg D.F0)ᵐᵒᵖ} (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a)
    (hb : (grA0 W hfin D).IsHom α' b) :
    (grEv W hfin D X).proj (β + α + α' + χ j)
        ((act1 H W hχ J h1 hco X).ν l ((act1 H W hχ J h1 hco X).ν j' m a) b) =
      (if j' = 0 then (grEv W hfin D X).proj (β + α + α' + χ j)
          ((act1 H W hχ J h1 hco X).ν l ((gmodEv D hfin X).act m a) b) else 0) +
      (if l = 0 then (gmodEv D hfin X).act
          ((grEv W hfin D X).proj (β + α + χ j) ((act1 H W hχ J h1 hco X).ν j' m a)) b else 0) := by
  set A := act1 H W hχ J h1 hco X
  have hx := ConeAt.congr' (act1_cone H W hχ J h1 hco X j' β α m a hm ha) (add_zero _)
  have e := (act1_cone H W hχ J h1 hco X l).proj_atom (cone_pointed hco)
    (AddSubmonoid.subset_closure ⟨j, rfl⟩) (χ_ne_zero hco j) (χ_atom hco j) hx (coneAt_of_isHom hb)
  rw [show β + α + α' + 0 + χ j = β + α + α' + χ j by abel] at e
  rw [e, hb, (grA0 W hfin D).proj_of_isHom hb, if_neg (fun h ↦ χ_ne_zero hco j (by
    have := congrArg (fun z ↦ z - α') h; simp at this; exact this.symm)), LinearMap.map_zero, map_zero, add_zero]
  congr 1
  · by_cases hj : j' = 0
    · subst hj
      rw [if_pos rfl, show A.ν 0 m a = (gmodEv D hfin X).act m a from A.ν_zero m a,
        act_isHom X hm ha]
    · rw [if_neg hj, act1_bottom H W hχ J h1 hco X j' (by omega) hm ha, LinearMap.map_zero₂, map_zero]
  · by_cases hl : l = 0
    · subst hl
      rw [if_pos rfl, show A.ν 0 = (gmodEv D hfin X).act from
        LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ A.ν_zero m a]
      have := act_isHom X ((grEv W hfin D X).isHom_proj (β + α + χ j) (A.ν j' m a)) hb
      rw [show β + α + χ j + α' = β + α + α' + χ j by abel] at this
      exact this
    · rw [if_neg hl]
      have := act1_bottom H W hχ J h1 hco X l (by omega)
        ((grEv W hfin D X).isHom_proj (β + α + χ j) (A.ν j' m a)) hb
      rwa [show β + α + χ j + α' = β + α + α' + χ j by abel] at this

theorem P1μ_eq (l : ℕ) : ((famSplit H 1).posDef (one_isHom D hfin)).μ l = famμ μ qd 1 l :=
  famSplit_μ H 1 l

variable (hχ hco) in
include hχ hco in
theorem P1μ_bottom (l : ℕ) {α α' : Wt} {a b : (Alg D.F0)ᵐᵒᵖ} (ha : (grA0 W hfin D).IsHom α a)
    (hb : (grA0 W hfin D).IsHom α' b) :
    (grA0 W hfin D).proj (α + α') (((famSplit H 1).posDef (one_isHom D hfin)).μ l a b) =
      if l = 0 then a * b else 0 := by
  rw [P1μ_eq]
  by_cases hl : l = 0
  · subst hl
    rw [if_pos rfl]
    have : famμ μ qd 1 0 a b = a * b := by
      simp only [famμ, ite_true, LinearMap.add_apply, LinearMap.mul_apply', LinearMap.coe_sum,
        Finset.sum_apply]
      rw [Finset.sum_eq_zero fun i _ ↦ by rw [if_neg (by have := H.q_pos i; omega)]; rfl, add_zero]
    rw [this]; exact grA0_mul W hfin D ha hb
  · rw [if_neg hl]; exact famμ_bottom W hχ hco l (by omega) α α' a b ha hb

variable (hχ hco) in
include hχ hco in
theorem P1μ_atom (j : I) (l : ℕ) {α α' : Wt} {a b : (Alg D.F0)ᵐᵒᵖ}
    (ha : (grA0 W hfin D).IsHom α a) (hb : (grA0 W hfin D).IsHom α' b) :
    (grA0 W hfin D).proj (α + α' + χ j) (((famSplit H 1).posDef (one_isHom D hfin)).μ l a b) =
      if qd j = l then μ j a b else 0 := by
  rw [P1μ_eq]
  simp only [famμ, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, map_add, map_sum]
  have h0 : (grA0 W hfin D).proj (α + α' + χ j) ((if l = 0 then LinearMap.mul k _ else 0) a b) = 0 := by
    split_ifs
    · rw [LinearMap.mul_apply', (grA0 W hfin D).proj_of_isHom (grA0_mul W hfin D ha hb), if_neg]
      intro h; exact χ_ne_zero hco j (by simpa using h.symm)
    · simp
  rw [h0, zero_add, Finset.sum_eq_single j]
  · by_cases hq : qd j = l
    · rw [if_pos hq, if_pos hq, LinearMap.smul_apply, LinearMap.smul_apply, Pi.one_apply, one_smul,
        (grA0 W hfin D).proj_of_isHom (hχ j α α' a b ha hb), if_pos rfl]
    · rw [if_neg hq, if_neg hq]; simp
  · intro i _ hi
    split_ifs
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, Pi.one_apply, one_smul,
        (grA0 W hfin D).proj_of_isHom (hχ i α α' a b ha hb), if_neg]
      intro h; exact hi (χ_injective hco (add_left_cancel h))
    · simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The atom component of `ν_{j'}(m, μ_l(a, b))`. -/
theorem proj_νμ (j : I) (X : V) (l j' : ℕ) {β α α' : Wt} {m : Rep D.F0 (meshFam Q c X)}
    {a b : (Alg D.F0)ᵐᵒᵖ} (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a)
    (hb : (grA0 W hfin D).IsHom α' b) :
    (grEv W hfin D X).proj (β + α + α' + χ j) ((act1 H W hχ J h1 hco X).ν j' m
        (((famSplit H 1).posDef (one_isHom D hfin)).μ l a b)) =
      (if l = 0 then (grEv W hfin D X).proj (β + α + α' + χ j)
          ((act1 H W hχ J h1 hco X).ν j' m (a * b)) else 0) +
      (if j' = 0 then (gmodEv D hfin X).act m (if qd j = l then μ j a b else 0) else 0) := by
  set A := act1 H W hχ J h1 hco X
  set P := (famSplit H 1).posDef (one_isHom D hfin)
  have hy : ConeAt (cone χ) (grA0 W hfin D) (α + α') (P.μ l a b) := by
    have := (show ConeBil (C := cone χ) (G := grA0 W hfin D) (G' := grA0 W hfin D)
      (G'' := grA0 W hfin D) 0 (P.μ l) by rw [P1μ_eq]; exact famμ_cone W hχ l) α α' a b ha hb
    exact ConeAt.congr' this (add_zero _)
  have e := (act1_cone H W hχ J h1 hco X j').proj_atom (cone_pointed hco)
    (AddSubmonoid.subset_closure ⟨j, rfl⟩) (χ_ne_zero hco j) (χ_atom hco j)
    (coneAt_of_isHom hm) hy
  rw [show β + (α + α') + 0 + χ j = β + α + α' + χ j by abel] at e
  rw [e, hm, (grEv W hfin D X).proj_of_isHom hm, if_neg (fun h ↦ χ_ne_zero hco j (by
    have := congrArg (fun z ↦ z - β) h; simp at this; exact this.symm)), LinearMap.map_zero₂,
    map_zero, add_zero, P1μ_bottom (H := H) hχ hco l ha hb, P1μ_atom (H := H) hχ hco j l ha hb]
  congr 1
  · by_cases hl : l = 0
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl, map_zero, map_zero]
  · by_cases hj : j' = 0
    · subst hj
      rw [if_pos rfl, show (act1 H W hχ J h1 hco X).ν 0 = (gmodEv D hfin X).act from
        LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ (act1 H W hχ J h1 hco X).ν_zero m a]
      split_ifs with hq
      · have := act_isHom X hm (hχ j α α' a b ha hb)
        rwa [show β + (α + α' + χ j) = β + α + α' + χ j by abel] at this
      · simp
    · rw [if_neg hj]
      split_ifs with hq
      · have := act1_bottom H W hχ J h1 hco X j' (by omega) hm (hχ j α α' a b ha hb)
        rwa [show β + (α + α' + χ j) = β + α + α' + χ j by abel] at this
      · simp

/-- **The first-order action satisfies the square-zero equation for `μ_j`.** -/
theorem ν1_eq (j : I) (X : V) (m : Rep D.F0 (meshFam Q c X)) (a b : (Alg D.F0)ᵐᵒᵖ) :
    ν1 H W hχ J h1 hco j X ((gmodEv D hfin X).act m a) b - ν1 H W hχ J h1 hco j X m (a * b) +
      (gmodEv D hfin X).act (ν1 H W hχ J h1 hco j X m a) b =
        (gmodEv D hfin X).act m (μ j a b) := by
  set ν := ν1 H W hχ J h1 hco j X
  set act := (gmodEv D hfin X).act
  -- homogeneous inputs
  have key : ∀ β α α' (m : Rep D.F0 (meshFam Q c X)) (a b : (Alg D.F0)ᵐᵒᵖ),
      (grEv W hfin D X).IsHom β m → (grA0 W hfin D).IsHom α a → (grA0 W hfin D).IsHom α' b →
      ν (act m a) b - ν m (a * b) + act (ν m a) b - act m (μ j a b) = 0 := by
    intro β α α' m a b hm ha hb
    have hA := (act1 H W hχ J h1 hco X).assoc (qd j) m a b
    have hP := congrArg ((grEv W hfin D X).proj (β + α + α' + χ j)) hA
    rw [map_zero] at hP
    unfold assocErr at hP
    rw [map_sub, map_sum, map_sum] at hP
    simp only [proj_νν j X _ _ hm ha hb, proj_νμ j X _ _ hm ha hb, Finset.sum_add_distrib] at hP
    rw [sum_antidiag_fst (f := fun x ↦ (grEv W hfin D X).proj (β + α + α' + χ j)
        ((act1 H W hχ J h1 hco X).ν x.2 ((gmodEv D hfin X).act m a) b)),
      sum_antidiag_snd (f := fun x ↦ (gmodEv D hfin X).act ((grEv W hfin D X).proj (β + α + χ j)
        ((act1 H W hχ J h1 hco X).ν x.1 m a)) b),
      sum_antidiag_snd (f := fun x ↦ (grEv W hfin D X).proj (β + α + α' + χ j)
        ((act1 H W hχ J h1 hco X).ν x.1 m (a * b))),
      sum_antidiag_fst (f := fun x ↦ (gmodEv D hfin X).act m
        (if qd j = x.2 then μ j a b else 0)), if_pos rfl] at hP
    have e1 : ν (act m a) b = (grEv W hfin D X).proj (β + α + α' + χ j)
        ((act1 H W hχ J h1 hco X).ν (qd j) ((gmodEv D hfin X).act m a) b) := by
      rw [ν1_hom j X (act_isHom X hm ha) hb]
    have e2 : ν m a = (grEv W hfin D X).proj (β + α + χ j)
        ((act1 H W hχ J h1 hco X).ν (qd j) m a) := ν1_hom j X hm ha
    have e3 : ν m (a * b) = (grEv W hfin D X).proj (β + α + α' + χ j)
        ((act1 H W hχ J h1 hco X).ν (qd j) m (a * b)) := by
      rw [ν1_hom j X hm (grA0_mul W hfin D ha hb), add_assoc β α α']
    rw [e1, e2, e3]
    dsimp only at hP
    rw [← hP]
    abel
  -- all inputs
  rw [← sub_eq_zero]
  have hm : ∀ β m, (grEv W hfin D X).IsHom β m → ∀ a b,
      ν (act m a) b - ν m (a * b) + act (ν m a) b - act m (μ j a b) = 0 := by
    intro β m hm
    let g : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c X) :=
      LinearMap.mk₂ k (fun a b ↦ ν (act m a) b - ν m (a * b) + act (ν m a) b - act m (μ j a b))
        (fun a a' b ↦ by simp only [map_add, LinearMap.add_apply, add_mul]; abel)
        (fun t a b ↦ by simp only [map_smul, LinearMap.smul_apply, smul_mul_assoc, smul_sub,
          smul_add])
        (fun a b b' ↦ by simp only [map_add, mul_add]; abel)
        (fun t a b ↦ by simp only [map_smul, mul_smul_comm, smul_sub, smul_add])
    have := bil_ext_of_hom (G := grA0 W hfin D) (G' := grA0 W hfin D) (φ := g) (ψ := 0)
      fun α α' a b ha hb ↦ key β α α' m a b hm ha hb
    intro a b
    exact LinearMap.congr_fun (LinearMap.congr_fun this a) b
  let f : Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c X) :=
    { toFun := fun m ↦ ν (act m a) b - ν m (a * b) + act (ν m a) b - act m (μ j a b)
      map_add' := fun m m' ↦ by simp only [map_add, LinearMap.add_apply]; abel
      map_smul' := fun t m ↦ by
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_sub, smul_add] }
  have := (grEv W hfin D X).ext_of_hom (f := f) (f' := 0) fun β m hm' ↦ hm β m hm' a b
  exact LinearMap.congr_fun this m

/-- The first-order lifted action as a square-zero lift for `μ_j`. -/
def L1 (j : I) (X : V) : ActLift (μ j) (qd j : ℤ) (gmodEv D hfin X) :=
  ActLift.ofBilin (gmodEv D hfin X) (ν1 H W hχ J h1 hco j X)
    (fun p d m a hm ha ↦ isShift_cbil' (C := ⊥) (wtCompat D hfin W X) (χ j)
      ((act1 H W hχ J h1 hco X).deg (qd j)) p d m a hm ha)
    (ν1_eq j X)

theorem L1_act (j : I) (X : V) (m : Rep D.F0 (meshFam Q c X)) (a : (Alg D.F0)ᵐᵒᵖ) :
    (L1 (H := H) (W := W) (hχ := hχ) (J := J) (h1 := h1) (hco := hco) j X).act m a =
      ν1 H W hχ J h1 hco j X m a := rfl

/-! ### Joint homogeneity -/

omit [Fintype Q.nonprojective] [Infinite k] in
theorem a0Proj_zproj (γ : Wt) (d : ℤ) (v : (Alg D.F0)ᵐᵒᵖ) :
    (grA0 W hfin D).proj γ ((galgA0 D hfin).gr.proj d v) =
      (galgA0 D hfin).gr.proj d ((grA0 W hfin D).proj γ v) := by
  conv_rhs => rw [(galgA0 D hfin).gr.sum v, map_sum, map_sum]
  have hhom : ∀ e, (galgA0 D hfin).gr.IsHom e ((grA0 W hfin D).proj γ ((galgA0 D hfin).gr.proj e v)) :=
    fun e ↦ a0Proj_zgr W hfin D ((galgA0 D hfin).gr.isHom_proj e v)
  by_cases hd : d ∈ (galgA0 D hfin).gr.supp
  · rw [Finset.sum_eq_single d]
    · rw [(galgA0 D hfin).gr.proj_of_isHom (hhom d), if_pos rfl]
    · intro e _ he; rw [(galgA0 D hfin).gr.proj_of_isHom (hhom e), if_neg he]
    · intro h; exact absurd hd h
  · rw [(galgA0 D hfin).gr.proj_out d hd]
    simp

theorem zproj_wHom_ev {X : V} {β : Wt} {v : Rep D.F0 (meshFam Q c X)}
    (hv : (grEv W hfin D X).IsHom β v) (p : ℤ) :
    (grEv W hfin D X).IsHom β ((zgrEv D hfin X).proj p v) := by
  unfold MGr.IsHom
  rw [evProj_zproj D hfin W, hv]

omit [Fintype Q.nonprojective] [Infinite k] in
theorem zproj_wHom_A0 {α : Wt} {v : (Alg D.F0)ᵐᵒᵖ} (hv : (grA0 W hfin D).IsHom α v) (p : ℤ) :
    (grA0 W hfin D).IsHom α ((galgA0 D hfin).gr.proj p v) := by
  unfold MGr.IsHom
  rw [a0Proj_zproj, hv]

/-- Linear maps agreeing on jointly homogeneous vectors agree. -/
theorem wz_ext_lin {y x : V} {f g : Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (h : ∀ β p v, (grEv W hfin D y).IsHom β v → (zgrEv D hfin y).IsHom p v → f v = g v) :
    f = g :=
  (grEv W hfin D y).ext_of_hom fun β v hv ↦ by
    rw [(zgrEv D hfin y).sum v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun p _ ↦ h β p _ (zproj_wHom_ev hv p) ((zgrEv D hfin y).isHom_proj p v)

/-- Bilinear maps agreeing on jointly homogeneous pairs agree. -/
theorem wz_ext_bil {y x : V}
    {f g : Rep D.F0 (meshFam Q c y) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c x)}
    (h : ∀ β p α d v a, (grEv W hfin D y).IsHom β v → (zgrEv D hfin y).IsHom p v →
      (grA0 W hfin D).IsHom α a → (galgA0 D hfin).gr.IsHom d a → f v a = g v a) : f = g :=
  bil_ext_of_hom (G := grEv W hfin D y) (G' := grA0 W hfin D) fun β α v a hv ha ↦ by
    rw [(zgrEv D hfin y).sum v, (galgA0 D hfin).gr.sum a]
    simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      h β _ α _ _ _ (zproj_wHom_ev hv _) ((zgrEv D hfin y).isHom_proj _ v)
        (zproj_wHom_A0 ha _) ((galgA0 D hfin).gr.isHom_proj _ a)

omit [Fintype Q.nonprojective] [Infinite k] in
/-- A map raising the degree by exactly `s` commutes with the degree projections. -/
theorem zproj_shift {Y Z : Type*} [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
    {gY : ZGr (R := k) Y} {gZ : ZGr (R := k) Z} {s : ℤ} {u : Y →ₗ[k] Z}
    (hu : ∀ e v, gY.IsHom e v → gZ.IsHom (e + s) (u v)) (e : ℤ) (v : Y) :
    gZ.proj (e + s) (u v) = u (gY.proj e v) := by
  conv_lhs => rw [gY.sum v, map_sum, map_sum]
  by_cases he : e ∈ gY.supp
  · rw [Finset.sum_eq_single e]
    · rw [gZ.proj_of_isHom (hu e _ (gY.isHom_proj e v)), if_pos rfl]
    · intro e' _ he'
      rw [gZ.proj_of_isHom (hu e' _ (gY.isHom_proj e' v)), if_neg (by omega)]
    · intro h; exact absurd he h
  · rw [gY.proj_out e he, LinearMap.zero_apply, map_zero]
    refine Finset.sum_eq_zero fun e' he' ↦ ?_
    rw [gZ.proj_of_isHom (hu e' _ (gY.isHom_proj e' v)), if_neg]
    intro h; exact he (by rw [show e = e' by omega]; exact he')

/-! ### The total lifted action: bottom part and degree components -/

theorem tot_bottom (X : V) {β α : Wt} {m : Rep D.F0 (meshFam Q c X)} {a : (Alg D.F0)ᵐᵒᵖ}
    (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a) :
    (grEv W hfin D X).proj (β + α) ((act1 H W hχ J h1 hco X).tot m a) =
      (gmodEv D hfin X).act m a := by
  simp only [ActFam.tot, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  rw [Finset.sum_eq_single 0]
  · rw [show (act1 H W hχ J h1 hco X).ν 0 m a = (gmodEv D hfin X).act m a from
      (act1 H W hχ J h1 hco X).ν_zero m a, act_isHom X hm ha]
  · intro n _ hn; exact act1_bottom H W hχ J h1 hco X n (by omega) hm ha
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem tot_wz (X : V) (δ : Wt) {p d : ℤ} {m : Rep D.F0 (meshFam Q c X)} {a : (Alg D.F0)ᵐᵒᵖ}
    (hm : (zgrEv D hfin X).IsHom p m) (ha : (galgA0 D hfin).gr.IsHom d a) (n : ℕ) :
    (zgrEv D hfin X).proj (p + d + n) ((grEv W hfin D X).proj δ ((act1 H W hχ J h1 hco X).tot m a)) =
      (grEv W hfin D X).proj δ ((act1 H W hχ J h1 hco X).ν n m a) := by
  set A := act1 H W hχ J h1 hco X
  have hh : ∀ n' : ℕ, (zgrEv D hfin X).IsHom (p + d + n') ((grEv W hfin D X).proj δ (A.ν n' m a)) :=
    fun n' ↦ evProj_zgr W hfin D (A.deg n' p d m a hm ha)
  simp only [ActFam.tot, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  by_cases hn : n ∈ Finset.range (2 * degBound (gmodEv D hfin X).gr + 1)
  · rw [Finset.sum_eq_single n]
    · rw [(zgrEv D hfin X).proj_of_isHom (hh n), if_pos rfl]
    · intro n' _ hn'
      rw [(zgrEv D hfin X).proj_of_isHom (hh n'), if_neg (by omega)]
    · intro h; exact absurd hn h
  · have h0 : A.ν n = 0 := shift_eq_zero (Split.ofLen_nonneg _) (A.deg n)
      (by have := Finset.mem_range.not.1 hn; omega)
    rw [h0, LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
    refine Finset.sum_eq_zero fun n' _ ↦ ?_
    rw [(zgrEv D hfin X).proj_of_isHom (hh n'), if_neg]
    intro h
    exact hn (by rw [show n = n' by omega]; assumption)

/-! ### The first-order parts of the lifted arrows -/

/-- **The first-order arrow** `g_a`: the part of relative weight `χ_j` and internal degree
`1 + q_j` of the lifted arrow. -/
def y1 (A : ArrowL H W hχ J h1 hco) (j : I) {y x : V} (a : y ⟶ x) :
    Rep D.F0 (meshFam Q c y) →ₗ[k] Rep D.F0 (meshFam Q c x) :=
  ZGr.comp (zgrEv D hfin y) (zgrEv D hfin x) (1 + qd j)
    (clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.w a + χ j) (toLin (A.g a)))

theorem y1_hom (A : ArrowL H W hχ J h1 hco) (j : I) {y x : V} (a : y ⟶ x) {β : Wt} {p : ℤ}
    {v : Rep D.F0 (meshFam Q c y)} (hv : (grEv W hfin D y).IsHom β v)
    (hp : (zgrEv D hfin y).IsHom p v) :
    y1 A j a v = (zgrEv D hfin x).proj (p + (1 + qd j))
      ((grEv W hfin D y |>.proj β v |> fun _ ↦ (grEv W hfin D x).proj (β + (W.w a + χ j))
        (toLin (A.g a) v))) := by
  rw [y1, ZGr.comp_hom _ _ _ hp, clin_bot_apply _ _ hv]

/-- **The first-order arrows satisfy the square-zero linearity** of Lemma 6.6. -/
theorem y1_lift (A : ArrowL H W hχ J h1 hco) (j : I) {y x : V} (a : y ⟶ x)
    (m : Rep D.F0 (meshFam Q c y)) (b : (Alg D.F0)ᵐᵒᵖ) :
    y1 A j a ((gmodEv D hfin y).act m b) - (gmodEv D hfin x).act (y1 A j a m) b =
      ν1 H W hχ J h1 hco j x (fA D a m) b - fA D a (ν1 H W hχ J h1 hco j y m b) := by
  rw [← sub_eq_zero]
  let F : Rep D.F0 (meshFam Q c y) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c x) :=
    LinearMap.mk₂ k (fun m b ↦ y1 A j a ((gmodEv D hfin y).act m b) -
        (gmodEv D hfin x).act (y1 A j a m) b -
        (ν1 H W hχ J h1 hco j x (fA D a m) b - fA D a (ν1 H W hχ J h1 hco j y m b)))
      (fun m m' b ↦ by simp only [map_add, LinearMap.add_apply]; abel)
      (fun t m b ↦ by simp only [map_smul, LinearMap.smul_apply, smul_sub])
      (fun m b b' ↦ by simp only [map_add, LinearMap.add_apply]; abel)
      (fun t m b ↦ by simp only [map_smul, LinearMap.smul_apply, smul_sub])
  suffices hF : F = 0 from LinearMap.congr_fun (LinearMap.congr_fun hF m) b
  refine wz_ext_bil (W := W) (hfin := hfin) fun β p α d m b hmw hmz hbw hbz ↦ ?_
  simp only [F, LinearMap.mk₂_apply, LinearMap.zero_apply]
  set G := toLin (A.g a)
  set T := (act1 H W hχ J h1 hco y).tot
  set T' := (act1 H W hχ J h1 hco x).tot with hT'
  have hχC : χ j ∈ cone χ := AddSubmonoid.subset_closure ⟨j, rfl⟩
  have B1 : G (T m b) = T' (G m) b := toLin_act1 (A.g a) m b
  -- the left side
  have hx : ConeAt (cone χ) (grEv W hfin D y) (β + α) (T m b) :=
    ConeAt.congr' (act1_tot_cone (H := H) (hχ := hχ) (J := J) (h1 := h1) (hco := hco) y β α m b hmw hbw) (add_zero _)
  have eL := (A.cone a).proj_atom (cone_pointed hco) hχC (χ_ne_zero hco j) (χ_atom hco j) hx
  rw [tot_bottom y hmw hbw] at eL
  have hact : (grEv W hfin D y).IsHom (β + α) ((gmodEv D hfin y).act m b) := act_isHom y hmw hbw
  have hz := (grEv W hfin D y).isHom_proj (β + α + χ j) (T m b)
  have t1 : (grEv W hfin D x).proj (β + α + W.w a + χ j) (G ((gmodEv D hfin y).act m b)) =
      clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.w a + χ j) G ((gmodEv D hfin y).act m b) := by
    rw [clin_bot_apply _ _ hact, show β + α + (W.w a + χ j) = β + α + W.w a + χ j by abel]
  have t2 : (grEv W hfin D x).proj (β + α + W.w a + χ j)
      (G ((grEv W hfin D y).proj (β + α + χ j) (T m b))) =
      fA D a ((grEv W hfin D y).proj (β + α + χ j) (T m b)) := by
    rw [show fA D a = rs D (arrowMor c a) from rfl, ← A.bot a, clin_bot_apply _ _ hz,
      show β + α + χ j + W.w a = β + α + W.w a + χ j by abel]
  rw [t1, t2] at eL
  -- the right side
  have hGm : ConeAt (cone χ) (grEv W hfin D x) (β + W.w a) (G m) := A.cone a β m hmw
  have eR := (act1_tot_cone (H := H) (hχ := hχ) (J := J) (h1 := h1) (hco := hco) x).proj_atom (cone_pointed hco) hχC (χ_ne_zero hco j) (χ_atom hco j)
    hGm (coneAt_of_isHom hbw)
  rw [hbw, (grA0 W hfin D).proj_of_isHom hbw, if_neg (fun h ↦ χ_ne_zero hco j (by
    have := congrArg (fun z ↦ z - α) h; simp at this; exact this.symm)), LinearMap.map_zero,
    map_zero, add_zero] at eR
  have hbotm : (grEv W hfin D x).proj (β + W.w a) (G m) = fA D a m := by
    rw [← clin_bot_apply _ _ hmw, A.bot]; rfl
  have hY : (grEv W hfin D x).IsHom (β + W.w a + χ j)
      ((grEv W hfin D x).proj (β + W.w a + χ j) (G m)) := (grEv W hfin D x).isHom_proj _ _
  have tb := tot_bottom (H := H) (hχ := hχ) (J := J) (h1 := h1) (hco := hco) x hY hbw
  rw [show β + W.w a + χ j + α = β + W.w a + α + χ j by abel] at tb
  rw [hbotm, tb, add_zero] at eR
  rw [← hT'] at eR
  -- combine at the weight `β + α + w_a + χ_j`
  have hW : (grEv W hfin D x).proj (β + α + W.w a + χ j) (G (T m b)) =
      (grEv W hfin D x).proj (β + α + W.w a + χ j) (T' (G m) b) := by rw [B1]
  rw [eL, show β + α + W.w a + χ j = β + W.w a + α + χ j by abel, eR] at hW
  rw [show β + W.w a + α + χ j = β + α + W.w a + χ j by abel] at hW
  -- the internal degree `p + d + 1 + q_j`
  have hZ := congrArg ((zgrEv D hfin x).proj (p + d + (1 + qd j))) hW
  simp only [map_add] at hZ
  have z1 : (zgrEv D hfin x).proj (p + d + (1 + qd j))
      (clin ⊥ (grEv W hfin D y) (grEv W hfin D x) (W.w a + χ j) G ((gmodEv D hfin y).act m b)) =
      y1 A j a ((gmodEv D hfin y).act m b) := by
    rw [y1, ZGr.comp_hom (zgrEv D hfin y) (zgrEv D hfin x) _
      (show (zgrEv D hfin y).IsHom (p + d) _ from (gmodEv D hfin y).act_hom _ _ _ _ hmz hbz)]
  have z2 : (zgrEv D hfin x).proj (p + d + (1 + qd j))
      (fA D a ((grEv W hfin D y).proj (β + α + χ j) (T m b))) =
      fA D a (ν1 H W hχ J h1 hco j y m b) := by
    rw [show p + d + (1 + (qd j : ℤ)) = p + d + qd j + 1 by ring,
      zproj_shift (fun e v hv ↦ fA_deg D hfin a hv), tot_wz y _ hmz hbz, ν1_hom j y hmw hbw]
  have z3 : (zgrEv D hfin x).proj (p + d + (1 + qd j))
      ((grEv W hfin D x).proj (β + α + W.w a + χ j) (T' (fA D a m) b)) =
      ν1 H W hχ J h1 hco j x (fA D a m) b := by
    rw [show p + d + (1 + (qd j : ℤ)) = p + 1 + d + qd j by ring,
      tot_wz x _ (fA_deg D hfin a hmz) hbz,
      ν1_hom j x (fA_shift W hfin D a β m hmw) hbw, show β + W.w a + α + χ j = β + α + W.w a + χ j by abel]
  have z4 : (zgrEv D hfin x).proj (p + d + (1 + qd j))
      ((gmodEv D hfin x).act ((grEv W hfin D x).proj (β + W.w a + χ j) (G m)) b) =
      (gmodEv D hfin x).act (y1 A j a m) b := by
    have hs := zproj_shift (gY := zgrEv D hfin x) (gZ := zgrEv D hfin x)
      (u := ((gmodEv D hfin x).act).flip b)
      (fun e v hv ↦ (gmodEv D hfin x).act_hom _ _ _ _ hv hbz) (p + (1 + qd j))
      ((grEv W hfin D x).proj (β + W.w a + χ j) (G m))
    simp only [LinearMap.flip_apply] at hs
    rw [show p + d + (1 + (qd j : ℤ)) = p + (1 + qd j) + d by ring, hs, y1,
      ZGr.comp_hom (zgrEv D hfin y) (zgrEv D hfin x) _ hmz, clin_bot_apply _ _ hmw,
      show β + (W.w a + χ j) = β + W.w a + χ j by abel]
  rw [z1, z2, z3, z4] at hZ
  rw [show y1 A j a ((gmodEv D hfin y).act m b) - (gmodEv D hfin x).act (y1 A j a m) b -
      (ν1 H W hχ J h1 hco j x (fA D a m) b - fA D a (ν1 H W hχ J h1 hco j y m b)) =
      (y1 A j a ((gmodEv D hfin y).act m b) + fA D a (ν1 H W hχ J h1 hco j y m b)) -
      (ν1 H W hχ J h1 hco j x (fA D a m) b + (gmodEv D hfin x).act (y1 A j a m) b) by abel, hZ,
    sub_self]

/-! ### The lift data for `μ_j` and its mesh errors -/

/-- **The first-order lift data for `μ_j`**: the specialization `t = ε e_j` of the lifts. -/
def LdPsi (A : ArrowL H W hχ J h1 hco) (j : I) : LiftData D hfin (qd j) (μ j) where
  L X := L1 (H := H) (W := W) (hχ := hχ) (J := J) (h1 := h1) (hco := hco) j X
  g a := y1 A j a
  lift a := ⟨fun m b ↦ fA_act D a m b, fun m b ↦ by rw [L1_act, L1_act]; exact y1_lift A j a m b⟩
  deg a p m hm := ZGr.comp_isHom (zgrEv D hfin _) (zgrEv D hfin _) _ hm

variable {Rw : I → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1}
  (hlen : ∀ i, (Rw i).2.length = qd i + 2) (hwt : ∀ i, W.pw (Rw i).2 = W.ν (Rw i).1 + χ i)

include hlen hwt in
/-- **The mesh errors of the first-order lift data are `λ_j R_j`.** -/
theorem zE_psi (A : ArrowL H W hχ J h1 hco) (lam : I → k) (hA : ∀ x, errE Rw A lam x = 0)
    (j : I) (x : Q.nonprojective) :
    zE (LdPsi A j) x = lam j • rs D (row c (Rw j).1 (Rw j).2 x) := by
  have hχC : ∀ i, χ i ∈ cone χ := fun i ↦ AddSubmonoid.subset_closure ⟨i, rfl⟩
  have hrel : toLin (realizeR k A.g _ _ (meshRelation c x)) =
      ∑ i, lam i • toLin (realizeR k A.g _ _ (rowQ (k := k) Rw i x)) := by
    rw [sub_eq_zero.1 (hA x), toLin_sum]; simp only [toLin_smul]
  refine wz_ext_lin (W := W) (hfin := hfin) fun β p v hvw hvz ↦ ?_
  have hW := congrArg (fun u ↦ (zgrEv D hfin x.1).proj (p + (qd j + 2))
    ((grEv W hfin D x.1).proj (β + W.ν x + χ j) (u v))) hrel
  -- the right side: only the row `j` contributes, through its bottom part
  have hR : ∀ i, (zgrEv D hfin x.1).proj (p + (qd j + 2)) ((grEv W hfin D x.1).proj
      (β + W.ν x + χ j) ((lam i • toLin (realizeR k A.g _ _ (rowQ (k := k) Rw i x))) v)) =
      if i = j then lam j • rs D (row c (Rw j).1 (Rw j).2 x) v else 0 := by
    intro i
    have hr := realize_props A (rowQ_mem (W := W) (k := k) hlen hwt i x)
    rw [LinearMap.smul_apply, map_smul, map_smul]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, show β + W.ν x + χ i = β + (W.ν x + χ i) by abel, ← clin_bot_apply _ _ hvw,
        hr.2.2.2, img_rowQ]
      congr 1
      have hdeg : row c (Rw i).1 (Rw i).2 x ∈ degreePart c (qd i + 2) _ _ := by
        by_cases hx : x = (Rw i).1
        · subst hx; simp only [row, Pi.single_eq_same]; rw [← hlen i]; exact pathMor_mem_degreePart c _
        · simp only [row, Pi.single_eq_of_ne hx]; exact zero_mem _
      have := repMap_isHom (D := D) hfin hdeg hvz
      rw [(zgrEv D hfin x.1).proj_of_isHom (by exact_mod_cast this), if_pos (by push_cast; ring)]
    · rw [if_neg hij, hr.2.2.1 β v hvw _ (fun h ↦ hij (eq_of_χ_sub_mem hco (by
        rwa [show β + W.ν x + χ j - (β + (W.ν x + χ i)) = χ j - χ i by abel] at h))),
        map_zero, smul_zero]
  rw [LinearMap.sum_apply, map_sum, map_sum] at hW
  simp only [hR, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hW
  -- the left side: the first-order parts
  rw [realize_meshRelation, toLin_sum] at hW
  simp only [toLin_smul, toLin_comp, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, map_sum, map_smul] at hW
  rw [LinearMap.smul_apply, ← hW]
  simp only [zE, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  set m' := Q.mate x a.1 a.2
  set Gm := toLin (A.g m')
  set Ga := toLin (A.g a.2)
  have hx' : ConeAt (cone χ) (grEv W hfin D a.1) (β + W.w m') (Gm v) := A.cone m' β v hvw
  have e := (A.cone a.2).proj_atom (cone_pointed hco) (hχC j) (χ_ne_zero hco j) (χ_atom hco j) hx'
  rw [show β + W.w m' + W.w a.2 + χ j = β + W.ν x + χ j by rw [add_assoc β, W.mesh x a]] at e
  rw [e, map_add]
  have hb1 : (grEv W hfin D a.1).proj (β + W.w m') (Gm v) = fA D m' v := by
    rw [← clin_bot_apply _ _ hvw, A.bot]; rfl
  have hY : (grEv W hfin D a.1).IsHom (β + W.w m' + χ j)
      ((grEv W hfin D a.1).proj (β + W.w m' + χ j) (Gm v)) := (grEv W hfin D a.1).isHom_proj _ _
  have hfw := fA_shift W hfin D m' β v hvw
  have t1 : (zgrEv D hfin x.1).proj (p + (qd j + 2)) ((grEv W hfin D x.1).proj (β + W.ν x + χ j)
      (Ga (fA D m' v))) = y1 A j a.2 (fA D m' v) := by
    rw [y1, ZGr.comp_hom (zgrEv D hfin a.1) (zgrEv D hfin x.1) _ (fA_deg D hfin m' hvz),
      clin_bot_apply _ _ hfw,
      show β + W.w m' + (W.w a.2 + χ j) = β + W.ν x + χ j by
        rw [← add_assoc, add_assoc β, W.mesh x a],
      show p + 1 + (1 + (qd j : ℤ)) = p + (qd j + 2) by ring]
  have t2 : (zgrEv D hfin x.1).proj (p + (qd j + 2)) ((grEv W hfin D x.1).proj (β + W.ν x + χ j)
      (Ga ((grEv W hfin D a.1).proj (β + W.w m' + χ j) (Gm v)))) = fA D a.2 (y1 A j m' v) := by
    rw [← show β + W.w m' + χ j + W.w a.2 = β + W.ν x + χ j by
        rw [add_right_comm (β + W.w m'), add_assoc β, W.mesh x a],
      ← clin_bot_apply _ _ hY, A.bot,
      show p + (qd j + 2 : ℤ) = p + (1 + qd j) + 1 by ring,
      show rs D (arrowMor c a.2) = fA D a.2 from rfl,
      zproj_shift (fun e w hw ↦ fA_deg D hfin a.2 hw),
      y1, ZGr.comp_hom (zgrEv D hfin _) (zgrEv D hfin _) _ hvz, clin_bot_apply _ _ hvw,
      show β + (W.w m' + χ j) = β + W.w m' + χ j by abel]
  rw [hb1, t1, t2, add_comm]
  rfl

include hlen hwt in
/-- **`Ψ[μ_j] = λ_j [R_j]`.** -/
theorem Ψc_psi (A : ArrowL H W hχ J h1 hco) (lam : I → k) (hA : ∀ x, errE Rw A lam x = 0)
    (j : I) :
    Ψc (LdPsi A j) = lam j • Submodule.Quotient.mk (row c (Rw j).1 (Rw j).2) := by
  rw [Ψc, ← Submodule.Quotient.mk_smul]
  congr 1
  funext x
  apply rs_inj (D := D)
  rw [Pi.smul_apply, rs_smul, ← zE_psi hlen hwt A lam hA j x]
  exact (zhat_spec _ x).symm

include hlen hwt in
/-- **The retained coefficients are nonzero** (`a_j ∈ k^*`), when `μ_j` is not a coboundary. -/
theorem lam_ne_zero (A : ArrowL H W hχ J h1 hco) (lam : I → k) (hA : ∀ x, errE Rw A lam x = 0)
    (j : I)
    (hnc : ¬ ∃ Hc : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
      (∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + qd j) (Hc a)) ∧
        μ j = hcobdry Hc) :
    lam j ≠ 0 := by
  intro h0
  apply hnc
  refine eq_hcobdry_of_Ψc_eq_zero J h1 (famHyp_cocycle H j) (H.deg j) (LdPsi A j) ?_
  rw [Ψc_psi hlen hwt A lam hA j, h0, zero_smul]

end MeshWalk

end MultiplicativeBasisDeformations
