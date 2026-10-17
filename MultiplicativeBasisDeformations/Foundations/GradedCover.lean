import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners

/-!
# Graded covering categories and Lemma 4.7

Definition 4.5 (`def:graded-covering-category`, `scalar-normalization.tex:255–262`):
for an algebra graded by a group `𝒢`, with chosen primitive idempotents of
identity degree, the graded covering category has objects `(x, g)` and
morphisms `B(x, y)_{g⁻¹h}` from `(x, g)` to `(y, h)`.

We work with a family `F : ι → C` in a `k`-linear category whose Hom spaces
are `𝒢`-graded compatibly with composition (`HomGrading`); the algebra is
`B = (Alg F)ᵒᵖ`. A finite full subcategory of the graded covering category,
with objects `s p = (x_p, g_p)`, has the category algebra `cov s`: the
subalgebra of `(Alg (F ∘ x))ᵒᵖ` of the matrices with `(p, q)`-entry in degree
`g_p⁻¹ g_q`.

Lemma 4.7 (`lem:homogeneous-projection`, lines 305–320): "Projection
`π : B' → H` onto the indicated homogeneous components is an `H`-bimodule
retraction. Indeed, for `p ∈ H(i,j)`, `q ∈ H(l,m)` and `b ∈ B'(j,l)`,
cancellation of the degrees of `p` and `q` in the grading group gives
`π(pbq) = p π(b) q`. Lemma 4.6 therefore applies with `C = D = H`."
(`isRepresentationFinite_cov`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → 𝒞) (G : Type) [Group G] [DecidableEq G]

/-- A grading of the Hom spaces of a family by a group, compatible with
composition, with identities in degree one. -/
structure HomGrading where
  proj : G → ∀ x y : ι, (F x ⟶ F y) →ₗ[k] (F x ⟶ F y)
  proj_proj : ∀ (g h : G) (x y : ι) (f : F x ⟶ F y),
    proj g x y (proj h x y f) = if h = g then proj h x y f else 0
  sum : ∀ (x y : ι) (f : F x ⟶ F y), ∃ s : Finset G, f = ∑ g ∈ s, proj g x y f
  proj_comp : ∀ (g a b : G) (x y z : ι) (f : F x ⟶ F y) (f' : F y ⟶ F z),
    proj g x z (proj a x y f ≫ proj b y z f') =
      if a * b = g then proj a x y f ≫ proj b y z f' else 0
  proj_id : ∀ (g : G) (x : ι), proj g x x (𝟙 (F x)) = if 1 = g then 𝟙 (F x) else 0

variable {F G} (D : HomGrading (k := k) F G)

namespace HomGrading

/-- A homogeneous morphism of degree `g`. -/
def IsHom (g : G) {x y : ι} (f : F x ⟶ F y) : Prop := D.proj g x y f = f

theorem isHom_proj (g : G) {x y : ι} (f : F x ⟶ F y) : D.IsHom g (D.proj g x y f) := by
  unfold IsHom; rw [D.proj_proj, if_pos rfl]

theorem proj_of_isHom {g h : G} {x y : ι} {f : F x ⟶ F y} (hf : D.IsHom h f) :
    D.proj g x y f = if h = g then f else 0 := by
  rw [← hf, D.proj_proj, hf]

theorem isHom_zero (g : G) {x y : ι} : D.IsHom g (0 : F x ⟶ F y) := map_zero _

theorem isHom_add {g : G} {x y : ι} {f f' : F x ⟶ F y} (hf : D.IsHom g f) (hf' : D.IsHom g f') :
    D.IsHom g (f + f') := by
  unfold IsHom at *; rw [map_add, hf, hf']

theorem isHom_smul {g : G} {x y : ι} (c : k) {f : F x ⟶ F y} (hf : D.IsHom g f) :
    D.IsHom g (c • f) := by
  unfold IsHom at *; rw [map_smul, hf]

theorem isHom_sum {g : G} {x y : ι} {κ : Type*} (s : Finset κ) {f : κ → (F x ⟶ F y)}
    (hf : ∀ i ∈ s, D.IsHom g (f i)) : D.IsHom g (∑ i ∈ s, f i) := by
  unfold IsHom at *
  rw [map_sum]
  exact Finset.sum_congr rfl hf

theorem proj_comp_of_isHom {g a b : G} {x y z : ι} {f : F x ⟶ F y} {f' : F y ⟶ F z}
    (hf : D.IsHom a f) (hf' : D.IsHom b f') :
    D.proj g x z (f ≫ f') = if a * b = g then f ≫ f' else 0 := by
  rw [← hf, ← hf', D.proj_comp]

theorem isHom_comp {a b : G} {x y z : ι} {f : F x ⟶ F y} {f' : F y ⟶ F z}
    (hf : D.IsHom a f) (hf' : D.IsHom b f') : D.IsHom (a * b) (f ≫ f') := by
  unfold IsHom; rw [D.proj_comp_of_isHom hf hf', if_pos rfl]

theorem isHom_id (x : ι) : D.IsHom 1 (𝟙 (F x)) := by
  unfold IsHom; rw [D.proj_id, if_pos rfl]

/-- **Cancellation of degrees**: `π(p b q) = p π(b) q` for homogeneous `p`, `q`. -/
theorem proj_sandwich {g a b : G} {x y z t : ι} {f : F x ⟶ F y} {f' : F z ⟶ F t}
    (hf : D.IsHom a f) (hf' : D.IsHom b f') (m : F y ⟶ F z) :
    D.proj g x t (f ≫ m ≫ f') = f ≫ D.proj (a⁻¹ * g * b⁻¹) y z m ≫ f' := by
  obtain ⟨s, hs⟩ := D.sum y z m
  have hm : ∀ h ∈ s, D.proj g x t (f ≫ D.proj h y z m ≫ f') =
      if h = a⁻¹ * g * b⁻¹ then f ≫ D.proj h y z m ≫ f' else 0 := by
    intro h _
    rw [D.proj_comp_of_isHom hf (D.isHom_comp (D.isHom_proj h m) hf')]
    congr 1
    apply propext
    constructor
    · rintro rfl; group
    · rintro rfl; group
  have hp : D.proj (a⁻¹ * g * b⁻¹) y z m =
      ∑ h ∈ s, if h = a⁻¹ * g * b⁻¹ then D.proj h y z m else 0 := by
    conv_lhs => rw [hs]
    rw [map_sum]
    exact Finset.sum_congr rfl fun h _ ↦ D.proj_proj _ _ _ _ _
  conv_lhs => rw [hs, Preadditive.sum_comp, Preadditive.comp_sum, map_sum]
  rw [Finset.sum_congr rfl hm, hp, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  split_ifs <;> simp

end HomGrading

/-! ### The covering subalgebras -/

variable {κ : Type} [Fintype κ] [DecidableEq κ] (s : κ → ι × G)

/-- The labels of a finite set of objects of the graded covering category. -/
abbrev lab : κ → ι := fun p ↦ (s p).1

/-- **The category algebra of a finite full subcategory of the graded covering
category**: entries `(p, q)` of degree `g_p⁻¹ g_q`. -/
def cov : Subalgebra k (Alg (F ∘ lab s))ᵐᵒᵖ where
  carrier := {a | ∀ p q, D.IsHom ((s p).2⁻¹ * (s q).2) (a.unop p q)}
  mul_mem' {a b} ha hb p q := by
    change D.IsHom _ (∑ r, b.unop p r ≫ a.unop r q)
    refine D.isHom_sum _ fun r _ ↦ ?_
    have := D.isHom_comp (hb p r) (ha r q)
    rwa [show (s p).2⁻¹ * (s r).2 * ((s r).2⁻¹ * (s q).2) = (s p).2⁻¹ * (s q).2 by group] at this
  one_mem' p q := by
    change D.IsHom _ (idTo (F := F ∘ lab s) p q)
    by_cases h : p = q
    · subst h
      rw [idTo_self, inv_mul_cancel]
      exact D.isHom_id _
    · rw [idTo_ne h]; exact D.isHom_zero _
  add_mem' {a b} ha hb p q := D.isHom_add (ha p q) (hb p q)
  zero_mem' p q := D.isHom_zero _
  algebraMap_mem' c p q := by
    change D.IsHom _ ((algebraMap k (Alg (F ∘ lab s)) c) p q)
    rw [Algebra.algebraMap_eq_smul_one]
    change D.IsHom _ (c • idTo (F := F ∘ lab s) p q)
    refine D.isHom_smul c ?_
    by_cases h : p = q
    · subst h
      rw [idTo_self, inv_mul_cancel]
      exact D.isHom_id _
    · rw [idTo_ne h]; exact D.isHom_zero _

/-- The projection onto the homogeneous entries. -/
def covProj : (Alg (F ∘ lab s))ᵐᵒᵖ →ₗ[k] cov D s where
  toFun a := ⟨MulOpposite.op (fun p q ↦ D.proj ((s p).2⁻¹ * (s q).2) _ _ (a.unop p q)),
    fun p q ↦ D.isHom_proj _ _⟩
  map_add' a b := by
    apply Subtype.ext; apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    exact map_add _ _ _
  map_smul' c a := by
    apply Subtype.ext; apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    exact map_smul _ _ _

theorem covProj_of_mem (c : cov D s) : covProj D s (c : (Alg (F ∘ lab s))ᵐᵒᵖ) = c := by
  apply Subtype.ext; apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  exact c.2 p q

theorem covProj_bimod (c c' : cov D s) (b : (Alg (F ∘ lab s))ᵐᵒᵖ) :
    covProj D s ((c : (Alg (F ∘ lab s))ᵐᵒᵖ) * b * c') = c * covProj D s b * c' := by
  apply Subtype.ext; apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  change D.proj _ _ _ (((c : (Alg (F ∘ lab s))ᵐᵒᵖ) * b * c').unop p q) =
    ((c : (Alg (F ∘ lab s))ᵐᵒᵖ) * (covProj D s b : (Alg (F ∘ lab s))ᵐᵒᵖ) * c').unop p q
  simp only [MulOpposite.unop_mul, mul_apply, Preadditive.comp_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  rw [D.proj_sandwich (c'.2 p t) (c.2 r q)]
  change _ = _ ≫ D.proj ((s t).2⁻¹ * (s r).2) _ _ (b.unop t r) ≫ _
  congr 3
  group

/-- **Lemma 4.7** (`lem:homogeneous-projection`): every finite full subcategory
of the graded covering category of a representation-finite graded algebra is
representation-finite. -/
theorem isRepresentationFinite_cov [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
    (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ) : IsRepresentationFinite k (cov D s) := by
  have hB := isRepresentationFinite_comp (lab s) hF
  exact splitRepresentationTransfer_of (C := cov D s) (q := AlgHom.id k (cov D s))
    (covProj D s) (covProj_bimod D s) (fun d ↦ ⟨d, rfl⟩) (covProj_of_mem D s) hB

end CatAlg

end MultiplicativeBasisDeformations
