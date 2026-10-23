module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.BigOperators
public import MBDVendor.QSE.CategoryTheory.CategoricalRadicalIdeal
public import MBDVendor.QSE.CategoryTheory.HomIdealPowers
public import MBDVendor.QSE.CategoryTheory.NilpotentCategoricalRadical

/-!
# Nilpotence of the radical from a finite additive generator

If every object is a retract of a finite biproduct of one object `G`, and
`End(G)` is Artinian, then the categorical radical Hom ideal is nilpotent.

This is a bounded adaptation of
`MBDVendor.QSE.CategoryTheory.FiniteGeneratorRadicalNilpotence`
at donor commit `d5ba0c48e7a851afd51247ff9cd81fc629e00ed2`.
Only the finite-generator definitions and nilpotence proof are retained; the
donor's wider Auslander-equivalence layer is not imported.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MBDVendor.Magnitude.CategoryTheory

open MBDVendor.QSE
open MBDVendor.QSE.CategoricalIdeal
open MBDVendor.QSE.CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- A witness that `X` is a retract of a finite biproduct of copies of `G`. -/
structure FiniteAddPresentation (G X : C) where
  n : ℕ
  retract : Retract X (⨁ fun _ : Fin n ↦ G)

/-- An object is a finite additive generator when every object is a retract
of a finite biproduct of copies of it. -/
def IsFiniteAddGenerator (G : C) : Prop :=
  ∀ X : C, Nonempty (FiniteAddPresentation G X)

omit [HasFiniteBiproducts C] in
/-- A categorical-radical endomorphism belongs to the ring-theoretic
Jacobson radical. -/
theorem mem_jacobson_of_isRadicalEndomorphism
    {X : C} {f : X ⟶ X} (hf : IsRadicalMorphism f) :
    End.of f ∈ Ring.jacobson (End X) := by
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.2
  intro y
  let yh : X ⟶ X := End.asHom y
  let a : X ⟶ X := 𝟙 X + f ≫ yh
  haveI : IsIso a := by
    have hi := hf (-yh)
    have heq : 𝟙 X - f ≫ (-yh) = a := by
      dsimp only [a]
      rw [Preadditive.comp_neg]
      abel
    rw [← heq]
    exact hi
  refine ⟨inv a, ?_⟩
  rw [Ideal.mem_bot]
  change f ≫ yh ≫ inv a + inv a - 𝟙 X = 0
  rw [sub_eq_zero]
  have ha : a ≫ inv a = 𝟙 X := IsIso.hom_inv_id a
  have ha' : inv a + f ≫ yh ≫ inv a = 𝟙 X := by
    simpa only [a, Preadditive.add_comp, Category.id_comp,
      Category.assoc] using ha
  rw [add_comm]
  exact ha'

omit [HasFiniteBiproducts C] in
/-- Sandwiching a categorical-radical morphism between maps from and to a
fixed object gives an element of that object's endomorphism-ring radical. -/
theorem sandwich_mem_jacobson
    {G X Y : C} {f : X ⟶ Y} (hf : IsRadicalMorphism f)
    (a : G ⟶ X) (b : Y ⟶ G) :
    End.of (a ≫ f ≫ b) ∈ Ring.jacobson (End G) := by
  apply mem_jacobson_of_isRadicalEndomorphism
  simpa only [Category.assoc] using
    isRadicalMorphism_postcomp b
      (isRadicalMorphism_precomp a hf)

/-- A morphism in the `n`-th categorical radical power becomes an element
of the `n`-th Jacobson-radical power after sandwiching by maps from and to a
finite additive generator. -/
theorem sandwich_mem_jacobson_pow
    (G : C) (hG : IsFiniteAddGenerator G) :
    ∀ (n : ℕ) {X Y : C} {f : X ⟶ Y},
      f ∈ ((homIdeal : HomIdeal C).pow n).hom X Y →
      ∀ (a : G ⟶ X) (b : Y ⟶ G),
        End.of (a ≫ f ≫ b) ∈
          (Ring.jacobson (End G)) ^ n
  | 0, X, Y, f, hf => by
      intro a b
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Set.mem_univ _
  | n + 1, X, Y, f, hf => by
      rw [HomIdeal.pow_succ] at hf
      intro a b
      induction hf using AddSubgroup.closure_induction with
      | mem f hf =>
          obtain ⟨M, left, right, hleft, hright, rfl⟩ := hf
          let P : FiniteAddPresentation G M := (hG M).some
          let u : Fin P.n → End G := fun j ↦
            a ≫ left ≫ P.retract.i ≫
              biproduct.π (fun _ : Fin P.n ↦ G) j
          let w : Fin P.n → End G := fun j ↦
            biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
              P.retract.r ≫ right ≫ b
          have hu (j : Fin P.n) :
              u j ∈ (Ring.jacobson (End G)) ^ n := by
            simpa only [u, Category.assoc] using
              sandwich_mem_jacobson_pow G hG n hleft a
                (P.retract.i ≫
                  biproduct.π (fun _ : Fin P.n ↦ G) j)
          have hw (j : Fin P.n) :
              w j ∈ Ring.jacobson (End G) := by
            change IsRadicalMorphism right at hright
            simpa only [w, Category.assoc] using
              sandwich_mem_jacobson hright
                (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
                  P.retract.r) b
          have hsum :
              End.of (a ≫ (left ≫ right) ≫ b) =
                ∑ j : Fin P.n,
                  (a ≫ left ≫ P.retract.i ≫
                      biproduct.π (fun _ : Fin P.n ↦ G) j) ≫
                    (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
                      P.retract.r ≫ right ≫ b) := by
            have htotal :=
              biproduct.total (f := fun _ : Fin P.n ↦ G)
            have hconjugated := congrArg
              (fun t ↦
                a ≫ left ≫ P.retract.i ≫ t ≫
                  P.retract.r ≫ right ≫ b)
              htotal
            have hconjugated' :
                a ≫ left ≫ P.retract.i ≫ P.retract.r ≫
                    right ≫ b =
                  ∑ j : Fin P.n,
                    (a ≫ left ≫ P.retract.i ≫
                        biproduct.π (fun _ : Fin P.n ↦ G) j) ≫
                      (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
                        P.retract.r ≫ right ≫ b) := by
              simpa only [Preadditive.comp_sum, Preadditive.sum_comp,
                Category.assoc, Category.comp_id, Category.id_comp] using
                hconjugated.symm
            have hretract :
                a ≫ left ≫ P.retract.i ≫ P.retract.r ≫
                    right ≫ b =
                  a ≫ left ≫ right ≫ b := by
              have h := congrArg
                (fun t : M ⟶ M ↦
                  a ≫ left ≫ t ≫ right ≫ b)
                P.retract.retract
              simpa only [Category.assoc, Category.id_comp] using h
            calc
              End.of (a ≫ (left ≫ right) ≫ b) =
                  a ≫ left ≫ right ≫ b := by
                    simp only [Category.assoc]
              _ = a ≫ left ≫ P.retract.i ≫ P.retract.r ≫
                    right ≫ b := hretract.symm
              _ = ∑ j : Fin P.n,
                    (a ≫ left ≫ P.retract.i ≫
                        biproduct.π (fun _ : Fin P.n ↦ G) j) ≫
                      (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
                        P.retract.r ≫ right ≫ b) := hconjugated'
          rw [hsum]
          apply Ideal.sum_mem
          intro j hj
          by_cases hn : n = 0
          · subst n
            have hp : w j * u j ∈ Ring.jacobson (End G) :=
              (Ring.jacobson (End G)).mul_mem_right (u j) (hw j)
            simpa only [show 0 + 1 = 1 by rfl,
              Submodule.pow_one, u, w, End.mul_def,
              Category.assoc] using hp
          · rw [Submodule.pow_succ' _ hn]
            have hp := Ideal.mul_mem_mul (hw j) (hu j)
            simpa only [u, w, End.mul_def, Category.assoc] using hp
      | zero =>
          have heq : a ≫ (0 : X ⟶ Y) ≫ b = 0 := by simp
          rw [heq]
          exact zero_mem _
      | add f g _ _ hf hg =>
          have heq :
              a ≫ (f + g) ≫ b =
                a ≫ f ≫ b + a ≫ g ≫ b := by
            simp only [Preadditive.comp_add, Preadditive.add_comp]
          rw [heq]
          exact add_mem hf hg
      | neg f _ hf =>
          have heq :
              a ≫ (-f) ≫ b = -(a ≫ f ≫ b) := by
            simp only [Preadditive.comp_neg, Preadditive.neg_comp]
          rw [heq]
          exact neg_mem hf

/-- A finite additive generator detects zero morphisms by two-sided
sandwiches. -/
theorem eq_zero_of_forall_generator_sandwich_eq_zero
    (G : C) (hG : IsFiniteAddGenerator G)
    {X Y : C} (f : X ⟶ Y)
    (hzero : ∀ (a : G ⟶ X) (b : Y ⟶ G),
      a ≫ f ≫ b = 0) :
    f = 0 := by
  have hleft (a : G ⟶ X) : a ≫ f = 0 := by
    let P : FiniteAddPresentation G Y := (hG Y).some
    apply (cancel_mono P.retract.i).1
    apply biproduct.hom_ext
    intro j
    simpa only [Category.assoc, zero_comp] using
      hzero a
        (P.retract.i ≫
          biproduct.π (fun _ : Fin P.n ↦ G) j)
  let P : FiniteAddPresentation G X := (hG X).some
  apply (cancel_epi P.retract.r).1
  apply biproduct.hom_ext'
  intro j
  simpa only [Category.assoc, comp_zero] using
    hleft
      (biproduct.ι (fun _ : Fin P.n ↦ G) j ≫
        P.retract.r)

/-- If the Jacobson radical of the endomorphism ring of a finite additive
generator is nilpotent, then the categorical radical Hom ideal is nilpotent
with the same exponent. -/
theorem homIdeal_isNilpotent_of_generator_jacobson
    (G : C) (hG : IsFiniteAddGenerator G)
    (hJ : IsNilpotent (Ring.jacobson (End G))) :
    (homIdeal : HomIdeal C).IsNilpotent := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨N, ?_⟩
  apply HomIdeal.ext_hom
  intro X Y
  apply le_antisymm
  · intro f hf
    change f = 0
    apply eq_zero_of_forall_generator_sandwich_eq_zero G hG f
    intro a b
    have hab := sandwich_mem_jacobson_pow G hG N hf a b
    rw [hN] at hab
    change End.of (a ≫ f ≫ b) = (0 : End G)
    exact hab
  · exact bot_le

/-- Artinianity of the generator endomorphism ring supplies categorical
radical nilpotence. -/
theorem homIdeal_isNilpotent_of_artinian_generator
    (G : C) (hG : IsFiniteAddGenerator G)
    [IsArtinianRing (End G)] :
    (homIdeal : HomIdeal C).IsNilpotent := by
  apply homIdeal_isNilpotent_of_generator_jacobson G hG
  simpa only [Ideal.jacobson_bot] using
    (IsArtinianRing.isNilpotent_jacobson_bot (R := End G))

/-- Canonical nilpotent-radical data for a category with an Artinian finite
additive generator. -/
def nilpotentRadicalDataOfArtinianGenerator
    (G : C) (hG : IsFiniteAddGenerator G)
    [IsArtinianRing (End G)] :
    NilpotentRadicalData C where
  ideal := homIdeal
  mem_iff := mem_homIdeal_iff
  nilpotent := homIdeal_isNilpotent_of_artinian_generator G hG

end MBDVendor.Magnitude.CategoryTheory
