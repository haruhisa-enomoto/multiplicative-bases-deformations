module

public import MultiplicativeBasisDeformations.Foundations.LiftedEvaluation
public import MultiplicativeBasisDeformations.Foundations.NormedBasis

/-!
# A multiplicative basis of `A₀` from homogeneous vectors

Proposition 4.14 (`scalar-normalization.tex`): the invariant basis
"descends to one vector on each homogeneous ray line of `A₀`: such a line lies
in one deck degree […]. Products lift uniquely, so every nonzero coefficient
downstairs is one."

For a graded family whose nonzero homogeneous pieces `A(x, y)_g` are lines
spanned by chosen vectors `b(x, y, g)` closed under composition up to zero,
with identities `b(x, x, 1) = 𝟙`, the matrix units of the `b(x, y, g)` form a
basis of `(Alg F)ᵒᵖ` (`basisA0`) which is multiplicative and contains the
idempotents of the labels (`basisA0_isMultiplicative`, `basisA0_idempotents`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}

/-! ### Matrix units of the category algebra -/

/-- The matrix unit of a morphism `f : F x → F y`. -/
def unitM (x y : ι) (f : F x ⟶ F y) : Alg F := fun p q ↦ idTo p x ≫ f ≫ idTo y q

theorem unitM_apply (x y : ι) (f : F x ⟶ F y) (p q : ι) :
    unitM x y f p q = idTo p x ≫ f ≫ idTo y q := rfl

theorem unitM_self (x y : ι) (f : F x ⟶ F y) : unitM x y f x y = f := by
  rw [unitM_apply, idTo_self, idTo_self, Category.id_comp, Category.comp_id]

theorem unitM_add (x y : ι) (f f' : F x ⟶ F y) : unitM x y (f + f') = unitM x y f + unitM x y f' := by
  apply CatAlg.ext; intro p q
  simp only [unitM_apply, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem unitM_smul (x y : ι) (c : k) (f : F x ⟶ F y) : unitM x y (c • f) = c • unitM x y f := by
  apply CatAlg.ext; intro p q
  simp only [unitM_apply, Linear.smul_comp, Linear.comp_smul]
  rfl

theorem unitM_zero (x y : ι) : unitM x y (0 : F x ⟶ F y) = 0 := by
  apply CatAlg.ext; intro p q
  simp only [unitM_apply, Limits.zero_comp, Limits.comp_zero]
  rfl

theorem unitM_mul (x y z : ι) (f : F x ⟶ F y) (f' : F y ⟶ F z) :
    unitM x y f * unitM y z f' = unitM x z (f ≫ f') := by
  apply CatAlg.ext; intro p r
  rw [mul_apply]
  simp only [unitM_apply, Category.assoc]
  simp_rw [← Preadditive.comp_sum]
  congr 2
  rw [sum_idTo_comp (F := F) y (fun q ↦ idTo q y ≫ f' ≫ idTo z r), idTo_self, Category.id_comp]

theorem unitM_mul_ne {x y y' z : ι} (h : y ≠ y') (f : F x ⟶ F y) (f' : F y' ⟶ F z) :
    unitM x y f * unitM y' z f' = 0 := by
  apply CatAlg.ext; intro p r
  rw [mul_apply]
  simp only [unitM_apply, Category.assoc]
  simp_rw [← Preadditive.comp_sum]
  rw [sum_idTo_comp (F := F) y (fun q ↦ idTo q y' ≫ f' ≫ idTo z r), idTo_ne h,
    Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]
  rfl

theorem eq_sum_unitM (a : Alg F) : a = ∑ x, ∑ y, unitM x y (a x y) := by
  apply CatAlg.ext; intro p q
  rw [sum_apply]
  simp_rw [sum_apply, unitM_apply]
  simp_rw [← Preadditive.comp_sum]
  rw [sum_idTo_comp (F := F) p (fun x ↦ ∑ y, a x y ≫ idTo y q)]
  exact (sum_comp_idTo (F := F) q (fun y ↦ a p y)).symm

/-! ### The basis -/

variable {G : Type} [Group G] [DecidableEq G] (D : HomGrading (k := k) F G)
  [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
  (b : ∀ x y : ι, G → (F x ⟶ F y))
  (hmem : ∀ x y g, b x y g ∈ D.part g x y)
  (hspan : ∀ x y g (f : F x ⟶ F y), f ∈ D.part g x y → ∃ c : k, f = c • b x y g)
  (hne : ∀ x y g, D.part g x y ≠ ⊥ → b x y g ≠ 0)

/-- The nonzero homogeneous pieces. -/
abbrev Idx := {t : ι × ι × G // D.part t.2.2 t.1 t.2.1 ≠ ⊥}

variable {D}

/-- The basis vector of a nonzero piece. -/
def vecA0 (t : Idx D) : (Alg F)ᵐᵒᵖ := MulOpposite.op (unitM t.1.1 t.1.2.1 (b t.1.1 t.1.2.1 t.1.2.2))

include hmem in
/-- The coordinate functional of a piece kills the other basis vectors. -/
theorem proj_vecA0 (t t₀ : Idx D) :
    D.proj t₀.1.2.2 t₀.1.1 t₀.1.2.1 ((vecA0 b t).unop t₀.1.1 t₀.1.2.1) =
      if t = t₀ then b t₀.1.1 t₀.1.2.1 t₀.1.2.2 else 0 := by
  obtain ⟨⟨x', y', g'⟩, ht⟩ := t
  obtain ⟨⟨x, y, g⟩, ht₀⟩ := t₀
  change D.proj g x y (unitM x' y' (b x' y' g') x y) = _
  by_cases hx : x' = x
  · subst hx
    by_cases hy : y' = y
    · subst hy
      rw [unitM_self, HomGrading.proj_of_isHom D ((HomGrading.mem_part_iff D).1 (hmem x' y' g'))]
      by_cases hg : g' = g
      · subst hg; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hg, if_neg]
        intro h
        exact hg (congrArg (fun t : Idx D ↦ t.1.2.2) h)
    · rw [unitM_apply, idTo_ne hy, Limits.comp_zero, Limits.comp_zero, map_zero, if_neg]
      intro h
      exact hy (congrArg (fun t : Idx D ↦ t.1.2.1) h)
  · rw [unitM_apply, idTo_ne (Ne.symm hx), Limits.zero_comp, map_zero, if_neg]
    intro h
    exact hx (congrArg (fun t : Idx D ↦ t.1.1) h)

include hmem hne in
theorem linearIndependent_vecA0 : LinearIndependent k (vecA0 (D := D) b) := by
  classical
  rw [linearIndependent_iff']
  intro s c hs t₀ ht₀
  have h1 : D.proj t₀.1.2.2 t₀.1.1 t₀.1.2.1 ((∑ i ∈ s, c i • vecA0 b i).unop t₀.1.1 t₀.1.2.1) =
      ∑ i ∈ s, c i • D.proj t₀.1.2.2 t₀.1.1 t₀.1.2.1 ((vecA0 b i).unop t₀.1.1 t₀.1.2.1) := by
    rw [Finset.unop_sum, sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [MulOpposite.unop_smul]
    exact map_smul _ _ _
  rw [hs] at h1
  simp_rw [proj_vecA0 b hmem] at h1
  rw [Finset.sum_eq_single t₀ (fun i _ hi ↦ by rw [if_neg hi, smul_zero]) (fun h' ↦ absurd ht₀ h'),
    if_pos rfl] at h1
  have h : c t₀ • b t₀.1.1 t₀.1.2.1 t₀.1.2.2 = 0 := by
    rw [← h1]
    exact map_zero (D.proj t₀.1.2.2 t₀.1.1 t₀.1.2.1)
  exact (smul_eq_zero.1 h).resolve_right (hne _ _ _ t₀.2)

include hspan in
theorem span_vecA0 : ⊤ ≤ Submodule.span k (Set.range (vecA0 (D := D) b)) := by
  classical
  rintro a -
  rw [← MulOpposite.op_unop a, eq_sum_unitM a.unop, Finset.op_sum]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  rw [Finset.op_sum]
  refine Submodule.sum_mem _ fun y _ ↦ ?_
  rw [D.eq_sum_degs (a.unop x y)]
  have hU : ∀ (s : Finset G) (f : G → (F x ⟶ F y)),
      unitM x y (∑ g ∈ s, f g) = ∑ g ∈ s, unitM x y (f g) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [unitM_zero]
    | insert g s hg ih => rw [Finset.sum_insert hg, Finset.sum_insert hg, unitM_add, ih]
  rw [hU, Finset.op_sum]
  refine Submodule.sum_mem _ fun g _ ↦ ?_
  by_cases hp : D.part g x y = ⊥
  · have : D.proj g x y (a.unop x y) = 0 := by
      have hm : D.proj g x y (a.unop x y) ∈ D.part g x y := ⟨_, rfl⟩
      rwa [hp, Submodule.mem_bot] at hm
    rw [this, unitM_zero, MulOpposite.op_zero]
    exact Submodule.zero_mem _
  · obtain ⟨c, hc⟩ := hspan x y g _ ⟨_, rfl⟩
    rw [hc, unitM_smul, MulOpposite.op_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨⟨(x, y, g), hp⟩, rfl⟩)

/-- **The basis of `A₀`** given by the chosen homogeneous vectors. -/
def basisA0 : Module.Basis (Idx D) k (Alg F)ᵐᵒᵖ :=
  Module.Basis.mk (linearIndependent_vecA0 b hmem hne) (span_vecA0 b hspan)

theorem basisA0_apply (t : Idx D) : basisA0 b hmem hspan hne t = vecA0 b t :=
  Module.Basis.mk_apply _ _ _

variable (hmul : ∀ x y z g h, b x y g ≫ b y z h = 0 ∨ b x y g ≫ b y z h = b x z (g * h))

include hmul in
/-- **The basis of `A₀` is multiplicative.** -/
theorem basisA0_isMultiplicative : IsMultiplicativeBasis (basisA0 b hmem hspan hne) := by
  intro i j
  rw [basisA0_apply, basisA0_apply]
  obtain ⟨⟨x, y, g⟩, hi⟩ := i
  obtain ⟨⟨x', y', g'⟩, hj⟩ := j
  change MulOpposite.op (unitM x y (b x y g)) * MulOpposite.op (unitM x' y' (b x' y' g')) = 0 ∨ _
  rw [← MulOpposite.op_mul]
  by_cases hyx : y' = x
  · subst hyx
    rw [unitM_mul]
    rcases hmul x' y' y g' g with h0 | h1
    · left; rw [h0, unitM_zero, MulOpposite.op_zero]
    · by_cases hz : b x' y' g' ≫ b y' y g = 0
      · left; rw [hz, unitM_zero, MulOpposite.op_zero]
      · right
        have hp : D.part (g' * g) x' y ≠ ⊥ := by
          intro hb
          apply hz
          have := hmem x' y (g' * g)
          rw [hb, Submodule.mem_bot] at this
          rw [h1, this]
        refine ⟨⟨(x', y, g' * g), hp⟩, ?_⟩
        rw [basisA0_apply]
        change MulOpposite.op (unitM y' y (b y' y g)) * MulOpposite.op (unitM x' y' (b x' y' g')) =
          MulOpposite.op (unitM x' y (b x' y (g' * g)))
        rw [← MulOpposite.op_mul, unitM_mul, h1]
  · left
    rw [unitM_mul_ne hyx, MulOpposite.op_zero]

variable (hid : ∀ x, b x x 1 = 𝟙 (F x)) (hid0 : ∀ x, 𝟙 (F x) ≠ 0)

include hmem hid hid0 in
theorem part_one_ne_bot (x : ι) : D.part 1 x x ≠ ⊥ := by
  intro h
  apply hid0 x
  have := hmem x x 1
  rw [h, Submodule.mem_bot, hid] at this
  exact this

/-- The identity piece of a label. -/
def idIdx (x : ι) : Idx D := ⟨(x, x, 1), part_one_ne_bot b hmem hid hid0 x⟩

theorem basisA0_idIdx (x : ι) :
    basisA0 b hmem hspan hne (idIdx b hmem hid hid0 x) = MulOpposite.op (unitM x x (𝟙 (F x))) := by
  rw [basisA0_apply]
  change MulOpposite.op (unitM x x (b x x 1)) = _
  rw [hid]

theorem sum_unitM_id : ∑ x, unitM x x (𝟙 (F x)) = (1 : Alg F) := by
  apply CatAlg.ext; intro p q
  rw [sum_apply]
  simp only [unitM_apply, Category.id_comp]
  rw [one_apply]
  exact sum_idTo_comp (F := F) p (fun x ↦ idTo x q)

/-- **The labels give a complete set of orthogonal idempotents.** -/
theorem idIdx_complete :
    CompleteOrthogonalIdempotents
      (fun x : ι ↦ basisA0 b hmem hspan hne (idIdx b hmem hid hid0 x)) := by
  refine ⟨⟨fun x ↦ ?_, fun x y hxy ↦ ?_⟩, ?_⟩
  · rw [basisA0_idIdx]
    change MulOpposite.op (unitM x x (𝟙 (F x))) * MulOpposite.op (unitM x x (𝟙 (F x))) = _
    rw [← MulOpposite.op_mul, unitM_mul, Category.id_comp]
  · dsimp only
    rw [basisA0_idIdx, basisA0_idIdx, ← MulOpposite.op_mul, unitM_mul_ne (Ne.symm hxy),
      MulOpposite.op_zero]
  · simp_rw [basisA0_idIdx]
    rw [← Finset.op_sum, sum_unitM_id, MulOpposite.op_one]

omit hfd in
theorem eq_unitM_of_corner {x : ι} {a : Alg F} (h1 : a * unitM x x (𝟙 (F x)) = a)
    (h2 : unitM x x (𝟙 (F x)) * a = a) : a = unitM x x (a x x) := by
  have e1 : ∀ p q, a p q = a p x ≫ idTo x q := fun p q ↦ by
    conv_lhs => rw [← h1]
    rw [mul_apply]
    simp only [unitM_apply, Category.id_comp]
    simp_rw [← Category.assoc]
    rw [← Preadditive.sum_comp, sum_comp_idTo (F := F) x (fun r ↦ a p r)]
  have e2 : ∀ p q, a p q = idTo p x ≫ a x q := fun p q ↦ by
    conv_lhs => rw [← h2]
    rw [mul_apply]
    simp only [unitM_apply, Category.id_comp, Category.assoc]
    simp_rw [← Preadditive.comp_sum]
    rw [sum_idTo_comp (F := F) x (fun j ↦ a j q)]
  apply CatAlg.ext; intro p q
  rw [unitM_apply, e1 p q, e2 p x, Category.assoc]

/-- **The label idempotents are primitive** when the endomorphism rings have
no nontrivial idempotents. -/
theorem idIdx_primitive (hloc : ∀ (x : ι) (φ : F x ⟶ F x), φ ≫ φ = φ → φ = 0 ∨ φ = 𝟙 (F x))
    (x : ι) : IsPrimitiveIdempotent (basisA0 b hmem hspan hne (idIdx b hmem hid hid0 x)) := by
  refine ⟨(idIdx_complete b hmem hspan hne hid hid0).idem x, ?_, ?_⟩
  · rw [basisA0_idIdx]
    intro h
    apply hid0 x
    have := congrArg (fun a : (Alg F)ᵐᵒᵖ ↦ a.unop x x) h
    simpa [unitM_self] using this
  · intro f hf h1 h2
    rw [basisA0_idIdx] at h1 h2 ⊢
    obtain ⟨a, rfl⟩ : ∃ a : Alg F, MulOpposite.op a = f := ⟨f.unop, rfl⟩
    rw [← MulOpposite.op_mul, MulOpposite.op_inj] at h1 h2
    have ha := eq_unitM_of_corner h1 h2
    have hidem : a x x ≫ a x x = a x x := by
      have := congrArg (fun c : (Alg F)ᵐᵒᵖ ↦ c.unop x x) hf.eq
      change (a * a) x x = a x x at this
      rw [ha, unitM_mul, unitM_self, unitM_self] at this
      rwa [ha] at this ⊢
    rcases hloc x _ hidem with h0 | h0
    · left; rw [ha, h0, unitM_zero, MulOpposite.op_zero]
    · right; rw [ha, h0]

end CatAlg

end MultiplicativeBasisDeformations
