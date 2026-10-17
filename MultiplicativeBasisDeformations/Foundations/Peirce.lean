import MultiplicativeBasisDeformations.Foundations.CategoryAlgebra
import MultiplicativeBasisDeformations.Foundations.RightModules
import MBDVendor.Magnitude.Algebra.RightModulePrimitiveIdempotent

/-!
# The Peirce isomorphism `A ≅ End(⊕ e_i A)ᵒᵖ`

For a complete set of orthogonal idempotents `e_i`, the right ideals `e_i A`
with the maps between them recover `A`: `Hom_A(e_i A, e_j A) ≅ e_j A e_i` by left
multiplication, and `A = ⊕ e_j A e_i`. In our path-order convention for category
algebras this is an algebra isomorphism `A ≅ (Alg (i ↦ e_i A))ᵒᵖ` (`peirceEquiv`).
It is used to identify a basic algebra with the algebra `A₀` of its projective
labels (Corollary 5.5, `mesh-deformations.tex:262–266`: "Restrict the resulting
isomorphism `ind(mod A) ≅ C` to the labelled projective objects and take
opposite algebras").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open MBDVendor.Magnitude.RightModule

namespace MultiplicativeBasisDeformations

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → A} (he : CompleteOrthogonalIdempotents e)

/-- The right ideal `e_i A` as a right module. -/
abbrev idealMod (a : A) : RightModuleCat A := ModuleCat.of Aᵐᵒᵖ (rightIdeal a)

/-- Left multiplication by `y ∈ e_j A` as a map `e_i A → e_j A`. -/
def lmul {a b : A} (hb : IsIdempotentElem b) (y : A) (hy : b * y = y) :
    rightIdeal a →ₗ[Aᵐᵒᵖ] rightIdeal b where
  toFun m := ⟨y * m.1, ⟨y * m.1, by
    change b * (y * m.1) = y * m.1
    rw [← mul_assoc, hy]⟩⟩
  map_add' m m' := Subtype.ext (mul_add y _ _)
  map_smul' r m := Subtype.ext (by
    change y * (m.1 * r.unop) = (y * m.1) * r.unop
    rw [mul_assoc])

theorem lmul_apply {a b : A} (hb : IsIdempotentElem b) (y : A) (hy : b * y = y)
    (m : rightIdeal a) : (lmul hb y hy m).1 = y * m.1 := rfl

include he in
theorem e_mul_corner (i j : ι) (x : A) : e j * (e j * x * e i) = e j * x * e i := by
  rw [← mul_assoc, ← mul_assoc, (he.idem j).eq]

include he in
/-- **The Peirce map** `x ↦ (left multiplication by e_j x e_i)`. -/
def peirceFun (x : A) : (CatAlg.Alg (fun i : ι ↦ idealMod (e i)))ᵐᵒᵖ :=
  MulOpposite.op fun i j ↦ ModuleCat.ofHom (lmul (he.idem j) (e j * x * e i) (e_mul_corner he i j x))

theorem peirceFun_apply (x : A) (i j : ι) (m : rightIdeal (e i)) :
    (((peirceFun he x).unop i j).hom m).1 = e j * x * e i * m.1 := rfl

/-- Entrywise extensionality for elements of `(Alg P)ᵒᵖ`. -/
theorem peirce_ext {a b : (CatAlg.Alg (fun i : ι ↦ idealMod (e i)))ᵐᵒᵖ}
    (h : ∀ i j (m : rightIdeal (e i)), ((a.unop i j).hom m).1 = ((b.unop i j).hom m).1) : a = b := by
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro i j
  exact ModuleCat.hom_ext (LinearMap.ext fun m ↦ Subtype.ext (h i j m))

theorem ideal_fixed {a : A} (ha : IsIdempotentElem a) (m : rightIdeal a) : a * m.1 = m.1 := by
  obtain ⟨b, hb⟩ := m.2
  change a * b = m.1 at hb
  rw [← hb, ← mul_assoc, ha.eq]

include he in
theorem idTo_apply (i j : ι) (m : rightIdeal (e i)) :
    ((CatAlg.idTo (F := fun i : ι ↦ idealMod (e i)) i j).hom m).1 = e j * e i * m.1 := by
  by_cases h : i = j
  · subst h
    rw [CatAlg.idTo_self, (he.idem i).eq, ideal_fixed (he.idem i)]
    rfl
  · rw [CatAlg.idTo_ne h, he.ortho (Ne.symm h), zero_mul]
    rfl

include he in
theorem sum_corner (x : A) : x = ∑ i, ∑ j, e j * x * e i := by
  have h1 : x = (∑ j, e j) * x * (∑ i, e i) := by rw [he.complete, one_mul, mul_one]
  conv_lhs => rw [h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul, Finset.sum_mul]

theorem smul_alg_apply (c : k) (a : CatAlg.Alg (fun i : ι ↦ idealMod (e i))) (i j : ι)
    (m : rightIdeal (e i)) : (((c • a) i j).hom m).1 = ((a i j).hom m).1 * algebraMap k A c := rfl

/-- **The Peirce algebra homomorphism.** -/
def peirceHom : A →ₐ[k] (CatAlg.Alg (fun i : ι ↦ idealMod (e i)))ᵐᵒᵖ where
  toFun := peirceFun he
  map_one' := peirce_ext fun i j m ↦ by
    rw [peirceFun_apply, mul_one]
    change _ = ((CatAlg.idTo (F := fun i : ι ↦ idealMod (e i)) i j).hom m).1
    rw [idTo_apply he]
  map_mul' x y := peirce_ext fun i l m ↦ by
    rw [peirceFun_apply, MulOpposite.unop_mul, CatAlg.mul_apply, ModuleCat.hom_sum,
      LinearMap.sum_apply, Submodule.coe_sum]
    change e l * (x * y) * e i * m.1 = ∑ j, e l * x * e j * (e j * y * e i * m.1)
    have : e l * (x * y) * e i * m.1 = e l * x * (∑ j, e j) * y * e i * m.1 := by
      rw [he.complete, mul_one, mul_assoc (e l) x y]
    rw [this, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj := (he.idem j).eq
    calc e l * x * e j * y * e i * m.1 = e l * x * (e j * e j) * y * e i * m.1 := by rw [hj]
      _ = e l * x * e j * (e j * y * e i * m.1) := by simp only [mul_assoc]
  map_zero' := peirce_ext fun i j m ↦ by
    rw [peirceFun_apply, mul_zero, zero_mul, zero_mul]; rfl
  map_add' x y := peirce_ext fun i j m ↦ by
    change e j * (x + y) * e i * m.1 = e j * x * e i * m.1 + e j * y * e i * m.1
    rw [mul_add, add_mul, add_mul]
  commutes' c := peirce_ext fun i j m ↦ by
    rw [peirceFun_apply]
    change _ = (((algebraMap k (CatAlg.Alg (fun i : ι ↦ idealMod (e i))) c) i j).hom m).1
    rw [show algebraMap k (CatAlg.Alg (fun i : ι ↦ idealMod (e i))) c = c • 1 from
      Algebra.algebraMap_eq_smul_one c]
    rw [smul_alg_apply, CatAlg.one_apply, idTo_apply he]
    simp only [mul_assoc, ← Algebra.commutes c]

include he in
/-- The generator `e_i` of `e_i A`. -/
def gen (i : ι) : rightIdeal (e i) := ⟨e i, ⟨e i, (he.idem i).eq⟩⟩

include he in
theorem peirceHom_injective : Function.Injective (peirceHom he (k := k)) := by
  intro x y h
  have hc : ∀ i j, e j * x * e i = e j * y * e i := by
    intro i j
    have := congrArg (fun a : (CatAlg.Alg (fun i : ι ↦ idealMod (e i)))ᵐᵒᵖ ↦
      ((a.unop i j).hom (gen he i)).1) h
    change e j * x * e i * e i = e j * y * e i * e i at this
    rwa [mul_assoc, (he.idem i).eq, mul_assoc (e j * y), (he.idem i).eq] at this
  rw [sum_corner he x, sum_corner he y]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hc i j

include he in
theorem peirceHom_surjective : Function.Surjective (peirceHom he (k := k)) := by
  intro a
  -- the value of each entry on the generator
  let v : ι → ι → A := fun i j ↦ ((a.unop i j).hom (gen he i)).1
  have hv : ∀ i j, e j * v i j * e i = v i j := by
    intro i j
    have h1 : e j * v i j = v i j := ideal_fixed (he.idem j) _
    have h2 : v i j * e i = v i j := by
      have := (a.unop i j).hom.map_smul (MulOpposite.op (e i)) (gen he i)
      have h := congrArg Subtype.val this
      have hg : MulOpposite.op (e i) • gen he i = gen he i := Subtype.ext (he.idem i).eq
      rw [hg] at h
      exact h.symm
    rw [h1, h2]
  refine ⟨∑ i, ∑ j, v i j, peirce_ext fun i l m ↦ ?_⟩
  change e l * (∑ i, ∑ j, v i j) * e i * m.1 = _
  have hsum : e l * (∑ i', ∑ j, v i' j) * e i = v i l := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
      · rw [← hv i l, ← mul_assoc, ← mul_assoc, (he.idem l).eq, mul_assoc, mul_assoc, (he.idem i).eq,
          ← mul_assoc, hv i l]
      · intro j _ hj
        rw [← hv i j, ← mul_assoc, ← mul_assoc, he.ortho (Ne.symm hj), zero_mul, zero_mul,
          zero_mul]
      · simp
    · intro i' _ hi'
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [← hv i' j]
      simp only [mul_assoc, he.ortho hi', mul_zero]
    · simp
  rw [hsum]
  -- `v i l · m = (a i l)(m)` since `m = e_i m`
  have hm : m = MulOpposite.op m.1 • gen he i := Subtype.ext (ideal_fixed (he.idem i) m).symm
  conv_rhs => rw [hm, LinearMap.map_smul]
  rfl

/-- **The Peirce isomorphism** `A ≅ (Alg (i ↦ e_i A))ᵒᵖ`. -/
def peirceEquiv : A ≃ₐ[k] (CatAlg.Alg (fun i : ι ↦ idealMod (e i)))ᵐᵒᵖ :=
  AlgEquiv.ofBijective (peirceHom he) ⟨peirceHom_injective he, peirceHom_surjective he⟩

end MultiplicativeBasisDeformations

/-! ### Category algebras along fully faithful functors -/

namespace MultiplicativeBasisDeformations.CatAlg

open CategoryTheory

universe u₁ v₁ w₁ v₂ w₂

variable {k : Type u₁} [Field k] {C : Type v₁} [Category.{w₁} C] [Preadditive C] [Linear k C]
  {D : Type v₂} [Category.{w₂} D] [Preadditive D] [Linear k D]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → C} {G : ι → D}
  (Φ : C ⥤ D) [Φ.Full] [Φ.Faithful] [Φ.Additive] [Φ.Linear k] (α : ∀ i, Φ.obj (F i) ≅ G i)

/-- The transport of a matrix along `Φ` and `α`. -/
def mapAlg (a : Alg F) : Alg G := fun i j ↦ (α i).inv ≫ Φ.map (a i j) ≫ (α j).hom

/-- And back. -/
def unmapAlg (b : Alg G) : Alg F := fun i j ↦ Φ.preimage ((α i).hom ≫ b i j ≫ (α j).inv)

theorem mapAlg_one : mapAlg Φ α (1 : Alg F) = 1 := by
  apply CatAlg.ext; intro i j
  change (α i).inv ≫ Φ.map (idTo i j) ≫ (α j).hom = idTo i j
  by_cases h : i = j
  · subst h; rw [idTo_self, idTo_self, Φ.map_id, Category.id_comp, Iso.inv_hom_id]
  · rw [idTo_ne h, idTo_ne h, Φ.map_zero, Limits.zero_comp, Limits.comp_zero]

theorem mapAlg_mul (a b : Alg F) : mapAlg Φ α (a * b) = mapAlg Φ α a * mapAlg Φ α b := by
  apply CatAlg.ext; intro i l
  change (α i).inv ≫ Φ.map (∑ j, a i j ≫ b j l) ≫ (α l).hom =
    ∑ j, ((α i).inv ≫ Φ.map (a i j) ≫ (α j).hom) ≫ ((α j).inv ≫ Φ.map (b j l) ≫ (α l).hom)
  rw [Φ.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Φ.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem mapAlg_add (a b : Alg F) : mapAlg Φ α (a + b) = mapAlg Φ α a + mapAlg Φ α b := by
  apply CatAlg.ext; intro i j
  change (α i).inv ≫ Φ.map (a i j + b i j) ≫ (α j).hom = _
  rw [Φ.map_add, Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem mapAlg_smul (c : k) (a : Alg F) : mapAlg Φ α (c • a) = c • mapAlg Φ α a := by
  apply CatAlg.ext; intro i j
  change (α i).inv ≫ Φ.map (c • a i j) ≫ (α j).hom = c • ((α i).inv ≫ Φ.map (a i j) ≫ (α j).hom)
  rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

/-- **Category algebras along a fully faithful linear functor.** -/
def algEquivOfFunctor : Alg F ≃ₐ[k] Alg G where
  toFun := mapAlg Φ α
  invFun := unmapAlg Φ α
  left_inv a := by
    apply CatAlg.ext; intro i j
    change Φ.preimage ((α i).hom ≫ ((α i).inv ≫ Φ.map (a i j) ≫ (α j).hom) ≫ (α j).inv) = a i j
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc,
      Functor.preimage_map]
  right_inv b := by
    apply CatAlg.ext; intro i j
    change (α i).inv ≫ Φ.map (Φ.preimage ((α i).hom ≫ b i j ≫ (α j).inv)) ≫ (α j).hom = b i j
    simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  map_mul' := mapAlg_mul Φ α
  map_add' := mapAlg_add Φ α
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change mapAlg Φ α (c • 1) = c • 1
    rw [mapAlg_smul, mapAlg_one]

end MultiplicativeBasisDeformations.CatAlg
