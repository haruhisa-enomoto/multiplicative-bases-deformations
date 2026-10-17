import MultiplicativeBasisDeformations.Refinements.TwistLifting
import MultiplicativeBasisDeformations.Refinements.FibreAlgebra
import MultiplicativeBasisDeformations.Refinements.LiftedMesh
import MultiplicativeBasisDeformations.Foundations.WeightLift

/-!
# Polynomial lifts of the evaluated modules (Proposition 12.8, first part)

`deformation-refinements.tex`: for the family `m + Σ_i t_i μ_i`, "keep the underlying
modules `M_i ⊗ K` and their vertex actions fixed", and lift the actions degree by degree, with the
choices made separately in each degree and weight; all entries are polynomials.

Here: the fibre at `t` is the algebra `Fib (famMul t)` with its length filtration (`famPF`), split
by the identity (`famSplit`); its deformation terms are `[q = 0]·m + Σ_{q_i = q} t_i μ_i`
(`famSplit_μ`). The lifted actions at `t = 1` are chosen with relative weights in the monoid of
the `χ_i` (`exists_actFam_cone`), and their twists are lifts for every fibre (`famLifts`), which
are polynomial in `t` and specialize to the chosen lifts at `t = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration MGr

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {I : Type} [Fintype I] [DecidableEq I]
  (μ : I → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (qd : I → ℕ)

/-- **The family** `m + Σ_i t_i μ_i`. -/
def famMul (t : I → k) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  LinearMap.mul k _ + ∑ i, t i • μ i

/-- The hypotheses on the family: positive internal degrees, normalized, associative for every
value of the parameters. -/
structure FamHyp : Prop where
  q_pos : ∀ i, 1 ≤ qd i
  deg : ∀ i, HDeg (galgA0 D hfin) (μ i) (qd i)
  one_left : ∀ i a, μ i 1 a = 0
  one_right : ∀ i a, μ i a 1 = 0
  assoc : ∀ t a b c, famMul D μ t (famMul D μ t a b) c = famMul D μ t a (famMul D μ t b c)

variable {D hfin μ qd} (H : FamHyp D hfin μ qd)

theorem famMul_apply (t : I → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    famMul D μ t a b = a * b + ∑ i, t i • μ i a b := by
  simp [famMul, LinearMap.sum_apply]

include H in
/-- The fibre product as an associative product. -/
def famAM (t : I → k) : AssocMul k (Alg D.F0)ᵐᵒᵖ where
  mm := famMul D μ t
  assoc := H.assoc t
  one_left a := by rw [famMul_apply]; simp [H.one_left]
  one_right a := by rw [famMul_apply]; simp [H.one_right]

theorem len_isHom_of_hdeg {i : I} (h : HDeg (galgA0 D hfin) (μ i) (qd i)) {d e : ℕ}
    {a b : (Alg D.F0)ᵐᵒᵖ} (ha : (lenA0 D hfin).IsHom d a) (hb : (lenA0 D hfin).IsHom e b) :
    (lenA0 D hfin).IsHom (d + e + qd i) (μ i a b) := by
  have := h d e a b ((ZGr.ofLen_isHom _ d a).2 ha) ((ZGr.ofLen_isHom _ e b).2 hb)
  exact (ZGr.ofLen_isHom _ (d + e + qd i) _).1 (by push_cast; exact this)

include H in
theorem famHdef (t : I → k) : ∀ d e a b, (lenA0 D hfin).IsHom d a → (lenA0 D hfin).IsHom e b →
    (lenA0 D hfin).Ge (d + e + 1) ((famAM H t).mm a b - a * b) := by
  intro d e a b ha hb
  change (lenA0 D hfin).Ge (d + e + 1) (famMul D μ t a b - a * b)
  rw [famMul_apply, add_sub_cancel_left]
  exact (lenA0 D hfin).geSub (d + e + 1) |>.sum_mem fun i _ ↦
    (lenA0 D hfin).ge_smul _ ((lenA0 D hfin).ge_mono (by have := H.q_pos i; omega)
      ((lenA0 D hfin).ge_of_isHom (len_isHom_of_hdeg (H.deg i) ha hb)))

/-- **The fibre at `t`** as a positive filtered deformation of `A₀`. -/
def famPF (t : I → k) : PosFiltration (lenA0 D hfin) (Fib (famAM H t)) :=
  Fib.posFiltration (lenA0 D hfin) (famHdef H t)

/-- **The identity splitting of a fibre.** -/
def famSplit (t : I → k) : Split (famPF H t) where
  φ := (Fib.toΛ (famAM H t)).symm
  one := rfl
  σφ d a ha := ha
  F_eq d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨Fib.toΛ (famAM H t) x, hx, rfl⟩

theorem famSplit_star (t : I → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    (famSplit H t).star a b = famMul D μ t a b := rfl

variable (μ qd) in
/-- The degree-`q` term of the fibre product: `[q = 0]·m + Σ_{q_i = q} t_i μ_i`. -/
def famμ (t : I → k) (q : ℕ) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  (if q = 0 then LinearMap.mul k _ else 0) + ∑ i, if qd i = q then t i • μ i else 0

/-- Bilinear maps on `A₀` agreeing on homogeneous elements agree. -/
theorem lenBil_ext {f g : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (h : ∀ d e a b, (lenA0 D hfin).IsHom d a → (lenA0 D hfin).IsHom e b → f a b = g a b) :
    f = g := by
  refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
  rw [(lenA0 D hfin).sum a, (lenA0 D hfin).sum b]
  simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦
    h _ _ _ _ ((lenA0 D hfin).isHom_proj _ _) ((lenA0 D hfin).isHom_proj _ _)

theorem famSplit_μ (t : I → k) (q : ℕ) : (famSplit H t).μ q = famμ μ qd t q := by
  refine lenBil_ext (hfin := hfin) fun d e a b ha hb ↦ ?_
  rw [(famSplit H t).μ_hom ha hb, famSplit_star, famMul_apply, map_add, map_sum]
  simp only [famμ, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul]
  congr 1
  · rw [(lenA0 D hfin).proj_of_isHom ((lenA0 D hfin).isHom_mul ha hb)]
    split_ifs with h1 h2 h2 <;> simp_all
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(lenA0 D hfin).proj_of_isHom (len_isHom_of_hdeg (H.deg i) ha hb)]
    split_ifs with h1 h2 h2 <;> simp_all

/-! ### Weights -/

variable {Wt : Type} [AddCommGroup Wt] (W : MeshWt Q Wt) (χ : I → Wt) (coords : Wt →+ (I → ℤ))

/-- The monoid spanned by the characters `χ_i`. -/
abbrev cone : AddSubmonoid Wt := AddSubmonoid.closure (Set.range χ)

variable {χ coords}

theorem cone_nonneg (hco : ∀ i, coords (χ i) = Pi.single i 1) :
    ∀ γ ∈ cone χ, ∀ i, 0 ≤ coords γ i := by
  intro γ hγ
  induction hγ using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro i; rw [hco j]; by_cases h : i = j <;> simp [h]
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [map_add, Pi.add_apply]; exact add_nonneg (hx i) (hy i)

theorem cone_eq_sum (hco : ∀ i, coords (χ i) = Pi.single i 1) :
    ∀ γ ∈ cone χ, γ = ∑ i, (coords γ i).toNat • χ i := by
  intro γ hγ
  induction hγ using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [hco j, Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [Pi.single_apply, hi]
    · simp
  | zero => simp
  | add x y hx' hy' hx hy =>
    have hx0 := cone_nonneg hco x hx'
    have hy0 := cone_nonneg hco y hy'
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_add, Pi.add_apply, ← add_smul, Int.toNat_add (hx0 i) (hy0 i)]

theorem cone_pointed (hco : ∀ i, coords (χ i) = Pi.single i 1) :
    ∀ γ ∈ cone χ, ∀ δ ∈ cone χ, γ + δ = 0 → γ = 0 := by
  intro γ hγ δ hδ h
  have h1 := cone_nonneg hco γ hγ
  have h2 := cone_nonneg hco δ hδ
  have h3 : coords γ = 0 := by
    funext i
    have := congrFun (congrArg coords h) i
    rw [map_add, map_zero] at this
    simp only [Pi.add_apply, Pi.zero_apply] at this
    have := h1 i; have := h2 i
    simp only [Pi.zero_apply]; omega
  rw [cone_eq_sum hco γ hγ, h3]
  simp

theorem χ_ne_zero (hco : ∀ i, coords (χ i) = Pi.single i 1) (i : I) : χ i ≠ 0 := by
  intro h
  have := congrFun (hco i) i
  rw [h, map_zero] at this
  simp at this

theorem ch_χ (hco : ∀ i, coords (χ i) = Pi.single i 1) (t : I → k) (i : I) :
    MGr.ch coords t (χ i) = t i := by
  simp only [MGr.ch, mono, hco i]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

theorem ch_zero' (t : I → k) : MGr.ch coords t (0 : Wt) = 1 := by simp [MGr.ch, mono]

variable (D hfin)

/-- **The weight gradings of `A₀` and of the evaluated modules are compatible.** -/
theorem wtCompat (X : V) : WtCompat (gmodEv D hfin X) (grA0 W hfin D) (grEv W hfin D X) where
  mul _ _ _ _ ha hb := grA0_mul W hfin D ha hb
  act β α m a hm ha := act_shift W hfin D ha X β m hm
  projM _ _ _ hm := evProj_zgr W hfin D hm
  projΛ _ _ _ ha := a0Proj_zgr W hfin D ha

variable {D hfin}

/-- A weighted sum of the components of a homogeneous element. -/
theorem sum_smul_proj_hom {N : Type*} [AddCommGroup N] [Module k N] (G : MGr k Wt N) (f : Wt → k)
    {γ : Wt} {x : N} (hx : G.IsHom γ x) : ∑ δ ∈ G.supp, f δ • G.proj δ x = f γ • x := by
  by_cases hγ : γ ∈ G.supp
  · rw [Finset.sum_eq_single γ]
    · rw [hx]
    · intro δ _ hδ; rw [G.proj_of_isHom hx, if_neg (Ne.symm hδ), smul_zero]
    · intro h; exact absurd hγ h
  · rw [G.eq_zero_of_isHom_out hx hγ]; simp

variable (hχ : ∀ i, HasChar W hfin D (χ i) (μ i))

include hχ in
/-- **The deformation terms have relative weights in the cone.** -/
theorem famμ_cone (q : ℕ) : ConeBil (C := cone χ) (G := grA0 W hfin D) (G' := grA0 W hfin D)
    (G'' := grA0 W hfin D) 0 (famμ μ qd 1 q) := by
  intro α β a b ha hb
  simp only [famμ, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply]
  refine ConeAt.add ?_ (ConeAt.sum _ fun i _ ↦ ?_)
  · split_ifs
    · exact coneAt_of_isHom (by rw [add_zero]; exact grA0_mul W hfin D ha hb)
    · exact ConeAt.zero _
  · split_ifs
    · rw [LinearMap.smul_apply, LinearMap.smul_apply]
      refine ConeAt.smul _ ((coneAt_of_isHom (hχ i α β a b ha hb)).mono ?_)
      rw [show α + β + χ i - (α + β + 0) = χ i by abel]
      exact AddSubmonoid.subset_closure ⟨i, rfl⟩
    · exact ConeAt.zero _

include hχ in
/-- **The positive-degree deformation terms have no relative weight `0`.** -/
theorem famμ_bottom (hco : ∀ i, coords (χ i) = Pi.single i 1) (q : ℕ) (hq : 1 ≤ q) :
    ∀ α β a b, (grA0 W hfin D).IsHom α a → (grA0 W hfin D).IsHom β b →
      (grA0 W hfin D).proj (α + β) (famμ μ qd 1 q a b) = 0 := by
  intro α β a b ha hb
  simp only [famμ, if_neg (show q ≠ 0 by omega), zero_add, LinearMap.coe_sum, Finset.sum_apply,
    map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  split_ifs
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      (grA0 W hfin D).proj_of_isHom (hχ i α β a b ha hb), if_neg, smul_zero]
    intro h
    exact χ_ne_zero hco i (by simpa using h)
  · simp

include hχ in
/-- **Twisting the fibre at `1` gives the fibre at `t`.** -/
theorem twb_famμ (hco : ∀ i, coords (χ i) = Pi.single i 1) (t : I → k) (q : ℕ) :
    twb coords (grA0 W hfin D) (grA0 W hfin D) (grA0 W hfin D) t 0 (famμ μ qd 1 q) =
      famμ μ qd t q := by
  refine bil_ext_of_hom (G := grA0 W hfin D) (G' := grA0 W hfin D) fun α β a b ha hb ↦ ?_
  rw [twb_hom _ _ _ t 0 _ ha hb]
  simp only [famμ, LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, map_add, map_sum,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · split_ifs
    · simp only [LinearMap.mul_apply']
      rw [sum_smul_proj_hom _ (fun δ ↦ MGr.ch coords t (δ - α - β - 0)) (grA0_mul W hfin D ha hb)]
      simp [ch_zero']
    · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs
    · simp only [LinearMap.smul_apply, map_smul, Pi.one_apply, one_smul]
      rw [sum_smul_proj_hom _ (fun δ ↦ MGr.ch coords t (δ - α - β - 0)) (hχ i α β a b ha hb)]
      simp only [show α + β + χ i - α - β - 0 = χ i by abel, ch_χ hco]
    · simp

/-! ### Lifted actions -/

theorem isShift_twb {X : V} (t : I → k) {n : ℤ}
    {φ : Rep D.F0 (meshFam Q c X) →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] Rep D.F0 (meshFam Q c X)}
    (hφ : IsShift (gmodEv D hfin X) n φ) :
    IsShift (gmodEv D hfin X) n
      (twb coords (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) t 0 φ) := by
  intro p q m a hm ha
  unfold twb
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply]
  exact ZGr.isHom_sum _ _ _ fun β _ ↦ ZGr.isHom_sum _ _ _ fun α _ ↦ ZGr.isHom_sum _ _ _ fun δ _ ↦
    ZGr.isHom_smul _ _ ((wtCompat D hfin W X).projM δ _ _
      (hφ p q _ _ ((wtCompat D hfin W X).projM β p m hm) ((wtCompat D hfin W X).projΛ α q a ha)))

theorem twb_act (X : V) (t : I → k) :
    twb coords (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) t 0 (gmodEv D hfin X).act =
      (gmodEv D hfin X).act := by
  refine bil_ext_of_hom (G := grEv W hfin D X) (G' := grA0 W hfin D) fun β α m a hm ha ↦ ?_
  rw [twb_hom _ _ _ t 0 _ hm ha,
    sum_smul_proj_hom _ (fun δ ↦ MGr.ch coords t (δ - β - α - 0))
      ((wtCompat D hfin W X).act β α m a hm ha)]
  simp [ch_zero']

variable (J : D.InjData) (h1 : DegOne D)

variable (hco : ∀ i, coords (χ i) = Pi.single i 1)

include hχ J h1 hco in
/-- **Homogeneous lifted actions at `t = 1`**, without corrections of relative weight `0`. -/
theorem exists_actFam_one (X : V) :
    ∃ A : ActFam ((famSplit H 1).posDef (one_isHom D hfin)) (gmodEv D hfin X),
      (∀ n, ConeBil (C := cone χ) (G := grEv W hfin D X) (G' := grA0 W hfin D)
        (G'' := grEv W hfin D X) 0 (A.ν n)) ∧
      ∀ n, 1 ≤ n → ∀ β α m a, (grEv W hfin D X).IsHom β m → (grA0 W hfin D).IsHom α a →
        (grEv W hfin D X).proj (β + α) (A.ν n m a) = 0 :=
  exists_actFam_cone (gmodEv D hfin X) (wtCompat D hfin W X) (cone_pointed hco) _
    (fun q ↦ by
      change ConeBil _ ((famSplit H 1).μ q)
      rw [famSplit_μ]; exact famμ_cone W hχ q)
    (fun q hq ↦ by
      change ∀ α α' a b, _ → _ → (grA0 W hfin D).proj (α + α') ((famSplit H 1).μ q a b) = 0
      rw [famSplit_μ]; exact famμ_bottom W hχ hco q hq)
    (Split.ofLen_nonneg _)
    (fun t ht ↦ extVanish_ev D hfin J h1 1 X X t (Or.inr (by push_cast; omega)))

/-- The chosen homogeneous lifted action at `t = 1`. -/
def act1 (X : V) : ActFam ((famSplit H 1).posDef (one_isHom D hfin)) (gmodEv D hfin X) :=
  (exists_actFam_one H W hχ J h1 hco X).choose

theorem act1_cone (X : V) (n : ℕ) : ConeBil (C := cone χ) (G := grEv W hfin D X)
    (G' := grA0 W hfin D) (G'' := grEv W hfin D X) 0 ((act1 H W hχ J h1 hco X).ν n) :=
  (exists_actFam_one H W hχ J h1 hco X).choose_spec.1 n

theorem act1_bottom (X : V) (n : ℕ) (hn : 1 ≤ n) {β α : Wt} {m : Rep D.F0 (meshFam Q c X)}
    {a : (Alg D.F0)ᵐᵒᵖ} (hm : (grEv W hfin D X).IsHom β m) (ha : (grA0 W hfin D).IsHom α a) :
    (grEv W hfin D X).proj (β + α) ((act1 H W hχ J h1 hco X).ν n m a) = 0 :=
  (exists_actFam_one H W hχ J h1 hco X).choose_spec.2 n hn β α m a hm ha

variable [Infinite k]

/-- **The twisted lifted action at the fibre `t`.** -/
def famAct (t : I → k) (X : V) :
    ActFam ((famSplit H t).posDef (one_isHom D hfin)) (gmodEv D hfin X) where
  ν n := twb coords (grEv W hfin D X) (grA0 W hfin D) (grEv W hfin D X) t 0
    ((act1 H W hχ J h1 hco X).ν n)
  ν_zero m a := by
    have h0 : (act1 H W hχ J h1 hco X).ν 0 = (gmodEv D hfin X).act :=
      LinearMap.ext fun m ↦ LinearMap.ext fun a ↦ (act1 H W hχ J h1 hco X).ν_zero m a
    rw [h0, twb_act W X t]
  deg n := isShift_twb W t ((act1 H W hχ J h1 hco X).deg n)
  assoc n m a b := by
    have hμ : ((famSplit H t).posDef (one_isHom D hfin)).μ = fun j ↦
        twb coords (grA0 W hfin D) (grA0 W hfin D) (grA0 W hfin D) t 0
          (((famSplit H 1).posDef (one_isHom D hfin)).μ j) := by
      funext j
      change (famSplit H t).μ j = twb coords _ _ _ t 0 ((famSplit H 1).μ j)
      rw [famSplit_μ, famSplit_μ, twb_famμ W hχ hco]
    rw [hμ]
    refine assocErr_twb (cone_nonneg hco) (act1_cone H W hχ J h1 hco X) (fun j ↦ ?_)
      ((act1 H W hχ J h1 hco X).assoc n) t m a b
    change ConeBil _ ((famSplit H 1).μ j)
    rw [famSplit_μ]; exact famμ_cone W hχ j

/-- **Polynomial lifts of the evaluated modules**: filtered lifts for every fibre. -/
def famLifts (t : I → k) : Lifts D hfin (famPF H t) :=
  ⟨fun X ↦ (famSplit H t).fLift (famAct H W hχ J h1 hco t X)⟩

end MeshWalk

end MultiplicativeBasisDeformations
