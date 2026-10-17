import MultiplicativeBasisDeformations.Foundations.RepFinite
import MBDVendor.Magnitude.CategoryTheory.IndecomposableOfLocalEnd
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Lemma 4.9: weights on representation-finite posets

`lem:poset-weights` (`scalar-normalization.tex:392–420`): "If the incidence
algebra of a finite poset `R` is representation-finite, every additive weight,
with values in any abelian group, has the form `w(x,y) = ζ_y − ζ_x`."

Proof of the source: "Remove a minimal element `s` and put `U = {y : s < y}`.
Distinct connected components of `U` lie in distinct components of `R ∖ {s}`.
Otherwise, put a one-dimensional space at every vertex, assign the map one to
every comparison outside `s`, and assign maps `λ ∈ k*` from `s` to one
component of `U` and one to the others. These are representations. An
isomorphism must have the same scalar at all vertices of each component of
`R ∖ {s}`. Two components of `U` in the same such component therefore force
equality of the parameters. This produces infinitely many isomorphism classes
of fixed dimension, contrary to finite representation type. […] By induction
normalize all weights on `R ∖ {s}` to zero. The remaining weights from `s` are
constant on each component of `U`. Adjust the object values separately on the
corresponding components of `R ∖ {s}` to remove these constants."

The representations are right modules over the incidence algebra on a convex
connected set `D` (`thinRep`); the source restricts them to the component of
`s`, where they are indecomposable. The removal of minimal elements runs
through the up-sets of `R`, whose components are convex in `R`, so the
representations of all steps are representations of the incidence algebra of
`R` itself (no corner argument is needed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

namespace PosetWeights

variable {k : Type u} [Field k] {P : Type v} [PartialOrder P] [Fintype P] [DecidableEq P]
  [LocallyFiniteOrder P] [DecidableLE P]

/-- Comparability. -/
def Comp (x y : P) : Prop := x ≤ y ∨ y ≤ x

/-- Connectedness inside a set, through comparable elements of the set. -/
def ConnIn (Q : Set P) (x y : P) : Prop :=
  Relation.EqvGen (fun a b ↦ a ∈ Q ∧ b ∈ Q ∧ Comp a b) x y

/-- A convex set. -/
def IsConvex (D : Set P) : Prop := ∀ x z, x ∈ D → z ∈ D → ∀ y, x ≤ y → y ≤ z → y ∈ D

/-! ### Thin representations -/

section Rep

variable (D : Set P) [DecidablePred (· ∈ D)] (ρ : P → P → k)

/-- The action of the incidence algebra on `k^D` through the scalars `ρ`. -/
def act (a : IncidenceAlgebra k P) (v : D → k) : D → k :=
  fun y ↦ ∑ x : D, v x * a x y * ρ x y

variable {D ρ}

/-- Multiplicativity of `ρ` along chains in `D`, with `ρ x x = 1`. -/
structure IsMult (D : Set P) (ρ : P → P → k) : Prop where
  refl : ∀ x ∈ D, ρ x x = 1
  trans : ∀ x y z, x ∈ D → y ∈ D → z ∈ D → x ≤ y → y ≤ z → ρ x z = ρ x y * ρ y z

theorem sum_D_eq_Icc (hD : IsConvex D) (x z : D) (f : P → k) :
    ∑ y : D, (if (x : P) ≤ y ∧ (y : P) ≤ z then f y else 0) = ∑ y ∈ Finset.Icc (x : P) z, f y := by
  rw [← Finset.filter_le_le_eq_Icc, Finset.sum_filter]
  symm
  refine Finset.sum_congr_set D _ _ (fun y hy ↦ rfl) fun y hy ↦ ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hy (hD x z x.2 z.2 y h1 h2)

theorem act_mul (hD : IsConvex D) (hρ : IsMult D ρ) (a b : IncidenceAlgebra k P) (v : D → k) :
    act D ρ (b * a) v = act D ρ a (act D ρ b v) := by
  funext z
  simp only [act, IncidenceAlgebra.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← sum_D_eq_Icc hD x z, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  split_ifs with h
  · rw [hρ.trans x y z x.2 y.2 z.2 h.1 h.2]; ring
  · rw [not_and_or] at h
    rcases h with h | h
    · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; ring
    · rw [IncidenceAlgebra.apply_eq_zero_of_not_le h]; ring

theorem act_one (hρ : IsMult D ρ) (v : D → k) : act D ρ 1 v = v := by
  funext y
  simp only [act, IncidenceAlgebra.one_apply]
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl, hρ.refl y y.2]; ring
  · intro x _ hx
    rw [if_neg (fun h ↦ hx (Subtype.ext h))]; ring
  · simp

variable (D ρ) in
/-- The carrier of the thin representation. -/
def Car (_ρ : P → P → k) : Type (max u v) := D → k

instance : AddCommGroup (Car D ρ) := inferInstanceAs (AddCommGroup (D → k))
instance : Module k (Car D ρ) := inferInstanceAs (Module k (D → k))

variable (hD : IsConvex D) (hρ : IsMult D ρ)

include hD hρ in
/-- The right module structure. -/
def repModule : Module (IncidenceAlgebra k P)ᵐᵒᵖ (Car D ρ) where
  smul a v := act D ρ a.unop v
  one_smul v := act_one hρ v
  mul_smul a b v := act_mul hD hρ a.unop b.unop v
  smul_zero a := by
    change act D ρ a.unop 0 = 0
    funext y; simp [act]
  smul_add a v w := by
    change act D ρ a.unop (fun x ↦ v x + w x) = fun y ↦ act D ρ a.unop v y + act D ρ a.unop w y
    funext y; simp [act, add_mul, Finset.sum_add_distrib]
  add_smul a b v := by
    change act D ρ (a + b).unop v = act D ρ a.unop v + act D ρ b.unop v
    funext y; simp [act, mul_add, add_mul, Finset.sum_add_distrib, IncidenceAlgebra.add_apply]
  zero_smul v := by
    change act D ρ (0 : (IncidenceAlgebra k P)ᵐᵒᵖ).unop v = 0
    funext y; simp [act, IncidenceAlgebra.zero_apply]

/-- **The thin representation** `k^D` with maps `ρ`. -/
def thinRep : RightModuleCat (IncidenceAlgebra k P) :=
  @ModuleCat.of _ _ (Car D ρ) _ (repModule hD hρ)

/-! ### Homomorphisms between thin representations are diagonal -/

/-- The matrix unit at `x ≤ y`. -/
def sgl (k : Type u) [Field k] (x y : P) (h : x ≤ y) : IncidenceAlgebra k P :=
  ⟨fun a b ↦ if a = x ∧ b = y then 1 else 0, fun a b hab ↦ by
    rw [if_neg]; rintro ⟨rfl, rfl⟩; exact hab h⟩

theorem act_sgl (x y : D) (h : (x : P) ≤ y) (v : D → k) :
    act D ρ (sgl k x.1 y.1 h) v = fun z ↦ if z = y then v x * ρ x y else 0 := by
  funext z
  simp only [act, sgl, IncidenceAlgebra.coe_mk]
  by_cases hz : z = y
  · subst hz
    rw [if_pos rfl, Finset.sum_eq_single x]
    · simp
    · intro w _ hw; rw [if_neg (fun h' ↦ hw (Subtype.ext h'.1))]; ring
    · simp
  · rw [if_neg hz]
    exact Finset.sum_eq_zero fun w _ ↦ by
      rw [if_neg (fun h' ↦ hz (Subtype.ext h'.2))]; ring

theorem act_smul_sgl (r : k) (x y : D) (h : (x : P) ≤ y) (v : D → k) :
    act D ρ (r • sgl k x.1 y.1 h) v = fun z ↦ if z = y then r * v x * ρ x y else 0 := by
  have : act D ρ (r • sgl k x.1 y.1 h) v = fun z ↦ r * act D ρ (sgl k x.1 y.1 h) v z := by
    funext z
    simp only [act, IncidenceAlgebra.constSMul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [this, act_sgl]
  funext z
  by_cases hz : z = y
  · simp only [hz, if_true]; ring
  · simp only [hz, if_false, mul_zero]

/-- The basis vector at `x`. -/
def dlt (k : Type u) [Field k] (x : D) : D → k := fun z ↦ if z = x then 1 else 0

variable {ρ' : P → P → k} (hρ' : IsMult D ρ')

include hρ hρ' in
/-- **Homomorphisms of thin representations are diagonal**, with
`c_x ρ'(x,y) = c_y ρ(x,y)`. -/
theorem hom_diagonal (φ : thinRep hD hρ ⟶ thinRep hD hρ') :
    ∃ c : D → k, (∀ (v : thinRep hD hρ) x, φ.hom v x = c x * v x) ∧
      ∀ x y : D, (x : P) ≤ y → c x * ρ' x y = c y * ρ x y := by
  let ph : (D → k) → (D → k) := fun v ↦ φ.hom (show thinRep hD hρ from v)
  have hlin : ∀ (a : IncidenceAlgebra k P) (v : D → k),
      ph (act D ρ a v) = act D ρ' a (ph v) := fun a v ↦
    φ.hom.map_smul (MulOpposite.op a) (show thinRep hD hρ from v)
  refine ⟨fun x ↦ ph (dlt k x) x, fun v x ↦ ?_, fun x y hxy ↦ ?_⟩
  · -- `e_x v = v_x δ_x`
    let w : D → k := v
    change ph w x = ph (dlt k x) x * w x
    have hA : ph w x = ph (act D ρ (sgl k x.1 x.1 le_rfl) w) x := by
      have h := congrFun (hlin (sgl k x.1 x.1 le_rfl) w) x
      have e : act D ρ' (sgl k x.1 x.1 le_rfl) (ph w) x = ph w x := by
        rw [act_sgl]; simp only [if_true]; rw [hρ'.refl x x.2, mul_one]
      rw [h, e]
    have hB : act D ρ (sgl k x.1 x.1 le_rfl) w = act D ρ (w x • sgl k x.1 x.1 le_rfl) (dlt k x) := by
      rw [act_sgl, act_smul_sgl]
      funext z
      by_cases hz : z = x
      · simp [hz, dlt]
      · simp [hz]
    have hC := congrFun (hlin (w x • sgl k x.1 x.1 le_rfl) (dlt k x)) x
    have e : act D ρ' (w x • sgl k x.1 x.1 le_rfl) (ph (dlt k x)) x = w x * ph (dlt k x) x := by
      rw [act_smul_sgl]; simp only [if_true]; rw [hρ'.refl x x.2, mul_one]
    rw [hA, hB, hC, e]; ring
  · have h1 := congrFun (hlin (sgl k x.1 y.1 hxy) (dlt k x)) y
    have e1 : act D ρ (sgl k x.1 y.1 hxy) (dlt k x) =
        act D ρ (ρ x y • sgl k y.1 y.1 le_rfl) (dlt k y) := by
      rw [act_sgl, act_smul_sgl]
      funext z
      by_cases hz : z = y
      · simp [hz, dlt, hρ.refl y y.2]
      · simp [hz]
    have h2 := congrFun (hlin (ρ x y • sgl k y.1 y.1 le_rfl) (dlt k y)) y
    have r1 : act D ρ' (sgl k x.1 y.1 hxy) (ph (dlt k x)) y = ph (dlt k x) x * ρ' x y := by
      rw [act_sgl]; simp only [if_true]
    have r2 : act D ρ' (ρ x y • sgl k y.1 y.1 le_rfl) (ph (dlt k y)) y =
        ρ x y * ph (dlt k y) y := by
      rw [act_smul_sgl]; simp only [if_true]; rw [hρ'.refl y y.2, mul_one]
    rw [e1, h2, r1, r2] at h1
    show ph (dlt k x) x * ρ' x y = ph (dlt k y) y * ρ x y
    linear_combination -h1

/-! ### Finiteness and indecomposability -/

theorem act_algebraMap (hρ : IsMult D ρ) (c : k) (v : D → k) :
    act D ρ (algebraMap k (IncidenceAlgebra k P) c) v = c • v := by
  funext y
  simp only [act, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single y]
  · change v y * (algebraMap k k c • (1 : IncidenceAlgebra k P)) y y * ρ y y = c * v y
    rw [IncidenceAlgebra.constSMul_apply, IncidenceAlgebra.one_apply, if_pos rfl, hρ.refl y y.2]
    simp; ring
  · intro x _ hx
    change v x * (algebraMap k k c • (1 : IncidenceAlgebra k P)) x y * ρ x y = 0
    rw [IncidenceAlgebra.constSMul_apply, IncidenceAlgebra.one_apply,
      if_neg (fun h ↦ hx (Subtype.ext h))]
    simp
  · simp

include hρ in
/-- The identification with `k^D` is `k`-linear. -/
def toPi : thinRep hD hρ →ₗ[k] (D → k) where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' c v := act_algebraMap hρ c v

theorem thinRep_finite : Module.Finite k (thinRep hD hρ) :=
  Module.Finite.of_injective (toPi hD hρ) fun _ _ h ↦ h

theorem connIn_mem_iff {Q : Set P} {a b : P} (h : ConnIn Q a b) : (a ∈ Q ↔ b ∈ Q) := by
  induction h with
  | rel a b h => exact ⟨fun _ ↦ h.2.1, fun _ ↦ h.1⟩
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A connected set. -/
def IsConn (D : Set P) : Prop := ∀ x ∈ D, ∀ y ∈ D, ConnIn D x y

theorem const_of_connIn {α : Type*} {Q : Set P} (c : P → α) (hc : ∀ x y, x ∈ Q → y ∈ Q → x ≤ y → c x = c y)
    {a b : P} (h : ConnIn Q a b) : c a = c b := by
  induction h with
  | rel a b h =>
      rcases h.2.2 with h' | h'
      · exact hc a b h.1 h.2.1 h'
      · exact (hc b a h.2.1 h.1 h').symm
  | refl => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable (hρ0 : ∀ x y : D, (x : P) ≤ y → ρ x y ≠ 0)

include hρ0 in
/-- Endomorphisms of a connected thin representation are scalars. -/
theorem end_scalar (hconn : IsConn D) (x₀ : D) (φ : thinRep hD hρ ⟶ thinRep hD hρ) :
    ∃ c : k, ∀ (v : thinRep hD hρ) x, φ.hom v x = c * v x := by
  obtain ⟨c, hc, hrel⟩ := hom_diagonal hD hρ hρ φ
  let c' : P → k := fun x ↦ if h : x ∈ D then c ⟨x, h⟩ else 0
  have hconst : ∀ x : D, c x = c x₀ := by
    intro x
    have := const_of_connIn c' (fun a b ha hb hab ↦ by
      simp only [c', dif_pos ha, dif_pos hb]
      have h1 := hrel ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact mul_right_cancel₀ (hρ0 ⟨a, ha⟩ ⟨b, hb⟩ hab) h1) (hconn x x.2 x₀ x₀.2)
    simpa [c'] using this
  exact ⟨c x₀, fun v x ↦ by rw [hc, hconst]⟩

include hρ0 in
theorem end_isLocalRing (hconn : IsConn D) (x₀ : D) : IsLocalRing (End (thinRep hD hρ)) := by
  haveI : Nontrivial (End (thinRep hD hρ)) := by
    refine ⟨⟨𝟙 _, 0, fun h ↦ ?_⟩⟩
    have := congrArg (fun φ : End (thinRep hD hρ) ↦ φ.hom (show thinRep hD hρ from dlt k x₀) x₀) h
    change (dlt k x₀) x₀ = (0 : D → k) x₀ at this
    simp [dlt] at this
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro φ
  obtain ⟨c, hc⟩ := end_scalar hD hρ hρ0 hconn x₀ φ
  by_cases h0 : c = 0
  · right
    have : (1 - φ : End (thinRep hD hρ)) = 1 := by
      apply ModuleCat.hom_ext; apply LinearMap.ext; intro v
      funext x
      change v x - φ.hom v x = v x
      rw [hc, h0, zero_mul, sub_zero]
    rw [this]; exact isUnit_one
  · left
    rw [isUnit_iff_isIso]
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro v w h
      funext x
      have h1 := hc v x
      have h2 := hc w x
      have h3 : φ.hom v x = φ.hom w x := by rw [show φ.hom v = φ.hom w from h]
      rw [h1, h2] at h3
      exact mul_left_cancel₀ h0 h3
    · intro w
      refine ⟨show thinRep hD hρ from fun x ↦ c⁻¹ * (show D → k from w) x, ?_⟩
      funext x
      change φ.hom _ x = w x
      rw [hc]
      change c * (c⁻¹ * w x) = w x
      rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

include hρ0 in
theorem thinRep_indecomposable (hconn : IsConn D) (x₀ : D) : Indecomposable (thinRep hD hρ) := by
  haveI := end_isLocalRing hD hρ hρ0 hconn x₀
  exact MBDVendor.Magnitude.CategoryTheory.indecomposable_of_local_end _

include hρ0 in
theorem thinRep_isFiniteIndecomposable (hconn : IsConn D) (x₀ : D) :
    IsFiniteIndecomposable k (IncidenceAlgebra k P) (thinRep hD hρ) :=
  ⟨thinRep_finite hD hρ, thinRep_indecomposable hD hρ hρ0 hconn x₀⟩

/-- Isomorphic thin representations differ by object values. -/
theorem iso_diagonal (hρ' : IsMult D ρ') (e : thinRep hD hρ ≅ thinRep hD hρ') :
    ∃ c : D → k, (∀ x, c x ≠ 0) ∧ ∀ x y : D, (x : P) ≤ y → c x * ρ' x y = c y * ρ x y := by
  obtain ⟨c, hc, hrel⟩ := hom_diagonal hD hρ hρ' e.hom
  obtain ⟨d, hd, -⟩ := hom_diagonal hD hρ' hρ e.inv
  refine ⟨c, fun x hx ↦ ?_, hrel⟩
  have h := congrArg (fun φ : thinRep hD hρ ⟶ thinRep hD hρ ↦
    φ.hom (show thinRep hD hρ from dlt k x) x) e.hom_inv_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  change e.inv.hom (e.hom.hom (show thinRep hD hρ from dlt k x)) x = dlt k x x at h
  rw [hd, hc] at h
  change d x * (c x * dlt k x x) = dlt k x x at h
  rw [hx] at h
  simp [dlt] at h

end Rep

/-! ### Separation of the components of `U` -/

section Sep

theorem connIn_mono {Q Q' : Set P} (h : Q ⊆ Q') {a b : P} (hab : ConnIn Q a b) : ConnIn Q' a b := by
  induction hab with
  | rel a b h' => exact Relation.EqvGen.rel _ _ ⟨h h'.1, h h'.2.1, h'.2.2⟩
  | refl => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A path inside `Q` from a point of a subset `D` closed under comparability
in `Q` stays in `D`. -/
theorem connIn_restrict {Q D : Set P} (hDQ : D ⊆ Q)
    (hcl : ∀ a b, a ∈ D → b ∈ Q → Comp a b → b ∈ D) {a b : P} (hab : ConnIn Q a b) :
    a ∈ D → ConnIn D a b ∧ b ∈ D := by
  induction hab with
  | rel a b h' =>
      intro ha
      have hb := hcl a b ha h'.2.1 h'.2.2
      exact ⟨Relation.EqvGen.rel _ _ ⟨ha, hb, h'.2.2⟩, hb⟩
  | refl a => intro ha; exact ⟨Relation.EqvGen.refl _, ha⟩
  | symm a b h ih =>
      intro hb
      -- `b ∈ D`, and `a` is connected to `b` inside `Q`
      have ha : a ∈ D := by
        have key : ∀ a b, ConnIn Q a b → (a ∈ D ↔ b ∈ D) := by
          intro a b h
          induction h with
          | rel a b h' =>
              exact ⟨fun ha ↦ hcl a b ha h'.2.1 h'.2.2,
                fun hb ↦ hcl b a hb h'.1 (h'.2.2.symm)⟩
          | refl => exact Iff.rfl
          | symm a b _ ih => exact ih.symm
          | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
        exact (key a b h).2 hb
      exact ⟨Relation.EqvGen.symm _ _ (ih ha).1, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      intro ha
      obtain ⟨h₁, hb⟩ := ih₁ ha
      obtain ⟨h₂, hc⟩ := ih₂ hb
      exact ⟨Relation.EqvGen.trans _ _ _ h₁ h₂, hc⟩

variable [Infinite k]

/-- **Distinct components of `U` lie in distinct components of `Q ∖ {s}`**
(`scalar-normalization.tex:401–410`), for an up-set `Q` and a minimal `s ∈ Q`. -/
theorem sep (hrep : IsRepresentationFinite k (IncidenceAlgebra k P)) (Q : Set P)
    (hQ : IsUpperSet Q) (s : P) (hs : s ∈ Q) (hmin : ∀ x ∈ Q, ¬ x < s) (y₁ y₂ : P)
    (h₁ : s < y₁) (h₂ : s < y₂) (hc : ConnIn (Q \ {s}) y₁ y₂) : ConnIn {y | s < y} y₁ y₂ := by
  classical
  by_contra hn
  -- the component `D` of `s` in `Q`
  let D : Set P := {x | x ∈ Q ∧ ConnIn Q s x}
  have hDQ : D ⊆ Q := fun x hx ↦ hx.1
  have hcl : ∀ a b, a ∈ D → b ∈ Q → Comp a b → b ∈ D := fun a b ha hb hab ↦
    ⟨hb, Relation.EqvGen.trans _ _ _ ha.2 (Relation.EqvGen.rel _ _ ⟨ha.1, hb, hab⟩)⟩
  have hsD : s ∈ D := ⟨hs, Relation.EqvGen.refl _⟩
  have hDconv : IsConvex D := fun x z hx hz y hxy hyz ↦
    hcl x y hx (hQ hxy hx.1) (Or.inl hxy)
  have hDconn : IsConn D := fun x hx y hy ↦ by
    have hxy : ConnIn Q x y :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx.2) hy.2
    exact (connIn_restrict hDQ hcl hxy hx).1
  -- the component `C₁` of `y₁` in `U`
  let U : Set P := {y | s < y}
  let C₁ : Set P := {y | ConnIn U y₁ y}
  have hC₁U : ∀ y ∈ C₁, s < y := fun y hy ↦ (connIn_mem_iff hy).1 h₁
  -- the parameters
  let ρ : k → P → P → k := fun l x y ↦ if x = s ∧ y ∈ C₁ then l else 1
  have hmult : ∀ l, IsMult D (ρ l) := fun l ↦ by
    refine ⟨fun x _ ↦ ?_, fun x y z hx hy hz hxy hyz ↦ ?_⟩
    · simp only [ρ]
      rw [if_neg]
      rintro ⟨rfl, hx'⟩
      exact lt_irrefl _ (hC₁U _ hx')
    · by_cases hxs : x = s
      · by_cases hys : y = s
        · have hzC : z ∈ C₁ ↔ z ∈ C₁ := Iff.rfl
          simp only [ρ, hxs, hys, true_and]
          rw [if_neg (fun h ↦ lt_irrefl _ (hC₁U _ h)), one_mul]
        · have hsy : s < y := lt_of_le_of_ne (hxs ▸ hxy) (Ne.symm hys)
          have hsz : s < z := lt_of_lt_of_le hsy hyz
          have hyz' : ConnIn U y z := Relation.EqvGen.rel _ _ ⟨hsy, hsz, Or.inl hyz⟩
          have hiff : y ∈ C₁ ↔ z ∈ C₁ :=
            ⟨fun h ↦ Relation.EqvGen.trans _ _ _ h hyz',
              fun h ↦ Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hyz')⟩
          simp only [ρ, hxs, true_and, hys, false_and, if_false, mul_one]
          by_cases hz : z ∈ C₁
          · rw [if_pos hz, if_pos (hiff.2 hz)]
          · rw [if_neg hz, if_neg (fun h ↦ hz (hiff.1 h))]
      · have hys : y ≠ s := by
          rintro rfl
          exact hmin x hx.1 (lt_of_le_of_ne hxy hxs)
        simp only [ρ, hxs, hys, false_and, if_false, mul_one]
  have hρ0 : ∀ l, l ≠ 0 → ∀ x y : D, (x : P) ≤ y → ρ l x y ≠ 0 := fun l hl x y _ ↦ by
    simp only [ρ]; split_ifs <;> simp [hl]
  -- the modules are pairwise non-isomorphic
  have hne : ∀ l l', l ≠ 0 → l' ≠ 0 →
      Nonempty (thinRep hDconv (hmult l) ≅ thinRep hDconv (hmult l')) → l = l' := by
    rintro l l' hl hl' ⟨e⟩
    obtain ⟨c, hc0, hrel⟩ := iso_diagonal hDconv (hmult l) (hmult l') e
    have hy₁D : y₁ ∈ D := hcl s y₁ hsD (hQ h₁.le hs) (Or.inl h₁.le)
    have hy₂D : y₂ ∈ D := hcl s y₂ hsD (hQ h₂.le hs) (Or.inl h₂.le)
    -- `c` is constant along `Q ∖ {s}`
    let c' : P → k := fun x ↦ if h : x ∈ D then c ⟨x, h⟩ else 0
    have hD' : D \ {s} ⊆ Q \ {s} := fun x hx ↦ ⟨hx.1.1, hx.2⟩
    have hcl' : ∀ a b, a ∈ D \ {s} → b ∈ Q \ {s} → Comp a b → b ∈ D \ {s} :=
      fun a b ha hb hab ↦ ⟨hcl a b ha.1 hb.1 hab, hb.2⟩
    have hy₁D' : y₁ ∈ D \ {s} := ⟨hy₁D, ne_of_gt h₁⟩
    have hpath := (connIn_restrict hD' hcl' hc hy₁D').1
    have hconst : c' y₁ = c' y₂ := const_of_connIn c' (fun a b ha hb hab ↦ by
      simp only [c', dif_pos ha.1, dif_pos hb.1]
      have h := hrel ⟨a, ha.1⟩ ⟨b, hb.1⟩ hab
      have has : a ≠ s := ha.2
      simp only [ρ, has, false_and, if_false, mul_one] at h
      exact h) hpath
    simp only [c', dif_pos hy₁D, dif_pos hy₂D] at hconst
    have hs₁ := hrel ⟨s, hsD⟩ ⟨y₁, hy₁D⟩ h₁.le
    have hs₂ := hrel ⟨s, hsD⟩ ⟨y₂, hy₂D⟩ h₂.le
    have hy₁C : y₁ ∈ C₁ := Relation.EqvGen.refl _
    have hy₂C : y₂ ∉ C₁ := hn
    simp only [ρ, true_and, if_pos hy₁C, if_neg hy₂C, mul_one] at hs₁ hs₂
    rw [hconst, ← hs₂] at hs₁
    exact (mul_left_cancel₀ (hc0 _) hs₁).symm
  -- infinitely many isomorphism classes
  obtain ⟨n, X, -, hcov⟩ := hrep
  have hidx : ∀ l : k, l ≠ 0 → ∃ i, Nonempty (thinRep hDconv (hmult l) ≅ X i) := fun l hl ↦
    hcov _ (thinRep_isFiniteIndecomposable hDconv (hmult l) (hρ0 l hl) hDconn ⟨s, hsD⟩)
  choose idx hidx using hidx
  have hinj : Function.Injective (fun l : {l : k // l ≠ 0} ↦ idx l.1 l.2) := by
    rintro ⟨l, hl⟩ ⟨l', hl'⟩ h
    obtain ⟨e⟩ := hidx l hl
    obtain ⟨e'⟩ := hidx l' hl'
    simp only at h
    rw [h] at e
    exact Subtype.ext (hne l l' hl hl' ⟨e ≪≫ e'.symm⟩)
  have hinf : ({l : k | l ≠ 0} : Set k).Infinite :=
    (Set.infinite_univ.diff (Set.finite_singleton (0 : k))).mono fun l hl ↦ by simpa using hl
  haveI : Infinite {l : k // l ≠ 0} := hinf.to_subtype
  haveI : Finite {l : k // l ≠ 0} := Finite.of_injective _ hinj
  exact not_finite {l : k // l ≠ 0}

end Sep

/-! ### Normalizing weights -/

section Weights

variable (hsep : ∀ (Q : Set P), IsUpperSet Q → ∀ s ∈ Q, (∀ x ∈ Q, ¬ x < s) → ∀ y₁ y₂ : P,
    s < y₁ → s < y₂ → ConnIn (Q \ {s}) y₁ y₂ → ConnIn {y | s < y} y₁ y₂)
  {G : Type*} [AddCommGroup G] (wt : P → P → G)
  (hwt : ∀ x y z, x ≤ y → y ≤ z → wt x z = wt x y + wt y z)

include hsep hwt in
/-- The induction of the source, over the up-sets of `R`. -/
theorem weights_upset : ∀ (n : ℕ) (Q : Finset P), Q.card = n → IsUpperSet (Q : Set P) →
    ∃ ζ : P → G, ∀ x y, x ∈ Q → y ∈ Q → x ≤ y → wt x y = ζ y - ζ x := by
  classical
  intro n
  induction n with
  | zero =>
      intro Q hQ _
      rw [Finset.card_eq_zero] at hQ
      subst hQ
      exact ⟨0, fun x _ hx ↦ absurd hx (Finset.notMem_empty x)⟩
  | succ n ih =>
      intro Q hcard hup
      have hne : Q.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨s, hs, hmin'⟩ := Finset.exists_minimal hne
      have hmin : ∀ x ∈ Q, ¬ x < s := fun x hx hxs ↦
        (lt_irrefl x) (lt_of_lt_of_le hxs (hmin' hx hxs.le))
      let Q' := Q.erase s
      have hQ' : (Q' : Set P) = (Q : Set P) \ {s} := Finset.coe_erase s Q
      have hup' : IsUpperSet (Q' : Set P) := by
        intro x y hxy hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx ⊢
        refine ⟨fun hys ↦ ?_, hup hxy hx.2⟩
        subst hys
        exact hmin x hx.2 (lt_of_le_of_ne hxy hx.1)
      obtain ⟨ζ', hζ'⟩ := ih Q' (by rw [Finset.card_erase_of_mem hs]; omega) hup'
      have hss : wt s s = 0 := by
        have := hwt s s s le_rfl le_rfl
        exact left_eq_add.1 this
      have hU : ∀ y, s < y → y ∈ Q' := fun y hy ↦
        Finset.mem_erase.2 ⟨ne_of_gt hy, hup hy.le hs⟩
      let δ : P → G := fun y ↦ wt s y - ζ' y
      have hδ : ∀ {a b}, ConnIn {y | s < y} a b → s < a → δ a = δ b := by
        intro a b h ha
        have := const_of_connIn (Q := {y | s < y}) (fun y ↦ if s < y then δ y else 0)
          (fun x y hx hy hxy ↦ by
            simp only [Set.mem_setOf_eq] at hx hy
            simp only [if_pos hx, if_pos hy, δ]
            rw [hwt s x y hx.le hxy, hζ' x y (hU x hx) (hU y hy) hxy]
            abel) h
        have hb : s < b := (connIn_mem_iff h).1 ha
        simpa [if_pos ha, if_pos hb] using this
      let κ : P → G := fun x ↦
        if h : ∃ y, s < y ∧ ConnIn (Q' : Set P) x y then δ (Classical.choose h) else 0
      have hconnQ : ∀ {a b}, ConnIn (Q' : Set P) a b → s < a → s < b →
          ConnIn {y | s < y} a b := by
        intro a b h ha hb
        rw [hQ'] at h
        exact hsep (Q : Set P) hup s hs (fun x hx ↦ hmin x hx) a b ha hb h
      have hκ : ∀ x x', ConnIn (Q' : Set P) x x' → κ x = κ x' := by
        intro x x' hxx'
        have hiff : (∃ y, s < y ∧ ConnIn (Q' : Set P) x y) ↔
            (∃ y, s < y ∧ ConnIn (Q' : Set P) x' y) :=
          ⟨fun ⟨y, hy, h⟩ ↦ ⟨y, hy, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hxx') h⟩,
            fun ⟨y, hy, h⟩ ↦ ⟨y, hy, Relation.EqvGen.trans _ _ _ hxx' h⟩⟩
        by_cases h : ∃ y, s < y ∧ ConnIn (Q' : Set P) x y
        · have h' := hiff.1 h
          simp only [κ, dif_pos h, dif_pos h']
          apply hδ _ (Classical.choose_spec h).1
          apply hconnQ _ (Classical.choose_spec h).1 (Classical.choose_spec h').1
          exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (Classical.choose_spec h).2)
            (Relation.EqvGen.trans _ _ _ hxx' (Classical.choose_spec h').2)
        · have h' : ¬ ∃ y, s < y ∧ ConnIn (Q' : Set P) x' y := fun h' ↦ h (hiff.2 h')
          simp only [κ, dif_neg h, dif_neg h']
      have hκU : ∀ y, s < y → κ y = δ y := by
        intro y hy
        have h : ∃ y', s < y' ∧ ConnIn (Q' : Set P) y y' := ⟨y, hy, Relation.EqvGen.refl _⟩
        simp only [κ, dif_pos h]
        exact (hδ (hconnQ (Classical.choose_spec h).2 hy (Classical.choose_spec h).1) hy).symm
      refine ⟨fun x ↦ if x = s then 0 else ζ' x + κ x, fun x y hx hy hxy ↦ ?_⟩
      by_cases hxs : x = s
      · subst hxs
        by_cases hys : y = x
        · subst hys; simp [hss]
        · have hsy : x < y := lt_of_le_of_ne hxy (Ne.symm hys)
          simp only [if_pos rfl, if_neg hys, sub_zero, hκU y hsy, δ]
          abel
      · have hys : y ≠ s := by
          rintro rfl
          exact hmin x hx (lt_of_le_of_ne hxy hxs)
        have hx' : x ∈ Q' := Finset.mem_erase.2 ⟨hxs, hx⟩
        have hy' : y ∈ Q' := Finset.mem_erase.2 ⟨hys, hy⟩
        simp only [if_neg hxs, if_neg hys]
        rw [hζ' x y hx' hy' hxy,
          hκ x y (Relation.EqvGen.rel _ _ ⟨hx', hy', Or.inl hxy⟩)]
        abel

end Weights

end PosetWeights

open PosetWeights in
/-- **Lemma 4.9** (`lem:poset-weights`), over an infinite field. -/
theorem posetWeights_of {k : Type u} [Field k] [Infinite k] {P : Type v} [PartialOrder P]
    [Fintype P] [DecidableEq P] [LocallyFiniteOrder P] [DecidableLE P]
    (hP : IsRepresentationFinite k (IncidenceAlgebra k P))
    {G : Type*} [AddCommGroup G] (wt : P → P → G)
    (hwt : ∀ x y z : P, x ≤ y → y ≤ z → wt x z = wt x y + wt y z) :
    ∃ ζ : P → G, ∀ x y : P, x ≤ y → wt x y = ζ y - ζ x := by
  obtain ⟨ζ, hζ⟩ := weights_upset (fun Q hQ s hs hmin y₁ y₂ h₁ h₂ hc ↦
    sep hP Q hQ s hs hmin y₁ y₂ h₁ h₂ hc) wt hwt _ Finset.univ rfl (by
      intro x y _ _; exact Finset.mem_coe.2 (Finset.mem_univ y))
  exact ⟨ζ, fun x y hxy ↦ hζ x y (Finset.mem_univ x) (Finset.mem_univ y) hxy⟩

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

/-- Lemma 4.9 for multiplicative `k*`-weights, with either orientation of the
incidence algebra: `μ(a,b) = Z_a / Z_b`. -/
theorem ratio_of_mult {k : Type*} [Field k] [Infinite k] {P : Type*} [PartialOrder P]
    [Fintype P] [DecidableEq P] [LocallyFiniteOrder P] [DecidableLE P]
    (hP : IsRepresentationFinite k (IncidenceAlgebra k P) ∨
      IsRepresentationFinite k (IncidenceAlgebra k Pᵒᵈ))
    (μ : P → P → k) (hμ0 : ∀ a b, a ≤ b → μ a b ≠ 0)
    (hμmul : ∀ a b c, a ≤ b → b ≤ c → μ a c = μ a b * μ b c) :
    ∃ Z : P → k, (∀ a, Z a ≠ 0) ∧ ∀ a b, a ≤ b → μ a b = Z a / Z b := by
  classical
  rcases hP with hP | hP
  · let wt : P → P → Additive kˣ := fun a b ↦
      if h : a ≤ b then Additive.ofMul (Units.mk0 (μ a b) (hμ0 a b h)) else 0
    have hwt : ∀ a b c, a ≤ b → b ≤ c → wt a c = wt a b + wt b c := by
      intro a b c hab hbc
      simp only [wt, dif_pos hab, dif_pos hbc, dif_pos (le_trans hab hbc), ← ofMul_mul]
      congr 1; ext; simp [hμmul a b c hab hbc]
    obtain ⟨ζ, hζ⟩ := posetWeights_of hP wt hwt
    refine ⟨fun a ↦ ((Additive.toMul (ζ a) : kˣ) : k)⁻¹, fun a ↦ by simp, fun a b hab ↦ ?_⟩
    have h := hζ a b hab
    simp only [wt, dif_pos hab] at h
    have h2 := congrArg (fun x : Additive kˣ ↦ ((Additive.toMul x : kˣ) : k)) h
    simp only [toMul_ofMul, Units.val_mk0, toMul_sub, Units.val_div_eq_div_val] at h2
    rw [h2]
    field_simp
  · let wt : Pᵒᵈ → Pᵒᵈ → Additive kˣ := fun a b ↦
      if h : OrderDual.ofDual b ≤ OrderDual.ofDual a then
        Additive.ofMul (Units.mk0 (μ (OrderDual.ofDual b) (OrderDual.ofDual a)) (hμ0 _ _ h))
      else 0
    have hwt : ∀ a b c : Pᵒᵈ, a ≤ b → b ≤ c → wt a c = wt a b + wt b c := by
      intro a b c hab hbc
      have hca : OrderDual.ofDual c ≤ OrderDual.ofDual a := le_trans hbc hab
      simp only [wt]
      rw [dif_pos (show OrderDual.ofDual b ≤ OrderDual.ofDual a from hab),
        dif_pos (show OrderDual.ofDual c ≤ OrderDual.ofDual b from hbc), dif_pos hca,
        ← ofMul_mul]
      congr 1; ext
      simp only [Units.val_mk0, Units.val_mul]
      rw [mul_comm]
      exact hμmul _ _ _ hbc hab
    obtain ⟨ζ, hζ⟩ := posetWeights_of hP wt hwt
    refine ⟨fun a ↦ ((Additive.toMul (ζ (OrderDual.toDual a)) : kˣ) : k), fun a ↦ by simp,
      fun a b hab ↦ ?_⟩
    have h := hζ (OrderDual.toDual b) (OrderDual.toDual a) hab
    simp only [wt] at h
    rw [dif_pos (show OrderDual.ofDual (OrderDual.toDual a) ≤
      OrderDual.ofDual (OrderDual.toDual b) from hab)] at h
    have h2 := congrArg (fun x : Additive kˣ ↦ ((Additive.toMul x : kˣ) : k)) h
    simp only [toMul_ofMul, Units.val_mk0, toMul_sub, Units.val_div_eq_div_val] at h2
    exact h2

end MultiplicativeBasisDeformations
