import Mathlib

/-!
# The category algebra of a finite family of objects

Construction 2.8 and the proof of Proposition 2.10
(`graded-category.tex:412–432, 495–503`): "Put `G = ⊕_{X ∈ ob C} X` and
`Λ = End_{add C}(G)^{op}`. For `X` in `add C`, the right `Λ`-modules
`R_X = C(G, X)` are projective". For objects `F x` (`x ∈ ι`) of a `k`-linear
category we realize `Λ` as `⊕_{x,y} C(F x, F y)` with the product in path order
(`(a b)_{xz} = ∑_y a_{xy} ≫ b_{yz}`: first `a`, then `b`). The paper's right
`Λ`-modules are then left modules over this ring; `R_X = (C(F y, X))_y` with
`(a · m)_x = ∑_y a_{xy} ≫ m_y`. The algebra `A₀` of Construction 2.8 is the
category algebra of the projective labels.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → 𝒞)

/-- The category algebra `⊕_{x,y} C(F x, F y)`. -/
def Alg := ∀ x y : ι, F x ⟶ F y

instance : AddCommGroup (Alg F) := inferInstanceAs (AddCommGroup (∀ x y : ι, F x ⟶ F y))

instance : Module k (Alg F) := inferInstanceAs (Module k (∀ x y : ι, F x ⟶ F y))

variable {F}

@[ext] theorem ext {a b : Alg F} (h : ∀ x y, a x y = b x y) : a = b := funext fun x ↦ funext (h x)

@[simp] theorem add_apply (a b : Alg F) (x y : ι) : (a + b) x y = a x y + b x y := rfl
@[simp] theorem zero_apply (x y : ι) : (0 : Alg F) x y = 0 := rfl
@[simp] theorem neg_apply (a : Alg F) (x y : ι) : (-a) x y = -a x y := rfl
@[simp] theorem sub_apply (a b : Alg F) (x y : ι) : (a - b) x y = a x y - b x y := rfl
@[simp] theorem smul_apply (c : k) (a : Alg F) (x y : ι) : (c • a) x y = c • a x y := rfl

theorem sum_apply {κ : Type*} (s : Finset κ) (f : κ → Alg F) (x y : ι) :
    (∑ i ∈ s, f i) x y = ∑ i ∈ s, f i x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_apply, ih]

/-- The identity of `F x`, as a morphism `F x ⟶ F y` when `x = y`. -/
def idTo (x y : ι) : F x ⟶ F y := if h : x = y then eqToHom (congrArg F h) else 0

@[simp] theorem idTo_self (x : ι) : idTo (F := F) x x = 𝟙 _ := by simp [idTo]

theorem idTo_ne {x y : ι} (h : x ≠ y) : idTo (F := F) x y = 0 := by simp [idTo, h]

instance : Mul (Alg F) := ⟨fun a b x z ↦ ∑ y, a x y ≫ b y z⟩

instance : One (Alg F) := ⟨fun x y ↦ idTo x y⟩

theorem mul_apply (a b : Alg F) (x z : ι) : (a * b) x z = ∑ y, a x y ≫ b y z := rfl

theorem one_apply (x y : ι) : (1 : Alg F) x y = idTo x y := rfl

theorem sum_idTo_comp {X : 𝒞} (x : ι) (f : ∀ y, F y ⟶ X) : ∑ y, idTo (F := F) x y ≫ f y = f x := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; rw [idTo_ne (Ne.symm hy), Limits.zero_comp]
  · simp

theorem sum_comp_idTo {X : 𝒞} (z : ι) (f : ∀ y, X ⟶ F y) : ∑ y, f y ≫ idTo (F := F) y z = f z := by
  rw [Finset.sum_eq_single z]
  · simp
  · intro y _ hy; rw [idTo_ne hy, Limits.comp_zero]
  · simp

theorem sum_comp_idTo_alg (a : Alg F) (x z : ι) : ∑ r, a x r ≫ idTo (F := F) r z = a x z :=
  sum_comp_idTo z (fun r ↦ a x r)

theorem sum_idTo_comp_alg (a : Alg F) (q z : ι) : ∑ t, idTo (F := F) q t ≫ a t z = a q z :=
  sum_idTo_comp q (fun t ↦ a t z)

instance : Ring (Alg F) :=
  { (inferInstance : AddCommGroup (Alg F)) with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c ↦ by
      ext x w
      simp only [mul_apply, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
      exact Finset.sum_comm
    one_mul := fun a ↦ by ext x z; exact sum_idTo_comp x (fun y ↦ a y z)
    mul_one := fun a ↦ by ext x z; exact sum_comp_idTo z (fun y ↦ a x y)
    left_distrib := fun a b c ↦ by
      ext x z; simp [mul_apply, Preadditive.comp_add, Finset.sum_add_distrib]
    right_distrib := fun a b c ↦ by
      ext x z; simp [mul_apply, Preadditive.add_comp, Finset.sum_add_distrib]
    zero_mul := fun a ↦ by ext x z; simp [mul_apply]
    mul_zero := fun a ↦ by ext x z; simp [mul_apply] }

instance : Algebra k (Alg F) :=
  Algebra.ofModule
    (fun c a b ↦ by ext x z; simp [mul_apply, Linear.smul_comp, Finset.smul_sum])
    (fun c a b ↦ by ext x z; simp [mul_apply, Linear.comp_smul, Finset.smul_sum])

/-! ### The modules `R_X` -/

variable (F) in
/-- `R_X = (C(F y, X))_y`. -/
def Rep (X : 𝒞) := ∀ y : ι, F y ⟶ X

instance (X : 𝒞) : AddCommGroup (Rep F X) := inferInstanceAs (AddCommGroup (∀ y : ι, F y ⟶ X))

instance (X : 𝒞) : Module k (Rep F X) := inferInstanceAs (Module k (∀ y : ι, F y ⟶ X))

@[ext] theorem Rep.ext {X : 𝒞} {m n : Rep F X} (h : ∀ y, m y = n y) : m = n := funext h

theorem Rep.sum_apply {X : 𝒞} {κ : Type*} (s : Finset κ) (f : κ → Rep F X) (y : ι) :
    (∑ i ∈ s, f i) y = ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

@[simp] theorem Rep.add_apply {X : 𝒞} (m n : Rep F X) (y : ι) : (m + n) y = m y + n y := rfl
@[simp] theorem Rep.zero_apply {X : 𝒞} (y : ι) : (0 : Rep F X) y = 0 := rfl
@[simp] theorem Rep.sub_apply' {X : 𝒞} (m n : Rep F X) (y : ι) : (m - n) y = m y - n y := rfl
@[simp] theorem Rep.neg_apply' {X : 𝒞} (m : Rep F X) (y : ι) : (-m) y = -m y := rfl
@[simp] theorem Rep.smul_apply' {X : 𝒞} (c : k) (m : Rep F X) (y : ι) : (c • m) y = c • m y := rfl

instance (X : 𝒞) : SMul (Alg F) (Rep F X) := ⟨fun a m x ↦ ∑ y, a x y ≫ m y⟩

theorem Rep.smul_apply {X : 𝒞} (a : Alg F) (m : Rep F X) (x : ι) :
    (a • m) x = ∑ y, a x y ≫ m y := rfl

instance (X : 𝒞) : Module (Alg F) (Rep F X) where
  one_smul m := by ext x; exact sum_idTo_comp x m
  mul_smul a b m := by
    ext x
    simp only [Rep.smul_apply, mul_apply, Preadditive.sum_comp, Preadditive.comp_sum,
      Category.assoc]
    exact Finset.sum_comm
  smul_zero a := by ext x; simp [Rep.smul_apply]
  smul_add a m n := by ext x; simp [Rep.smul_apply, Preadditive.comp_add, Finset.sum_add_distrib]
  add_smul a b m := by ext x; simp [Rep.smul_apply, Preadditive.add_comp, Finset.sum_add_distrib]
  zero_smul m := by ext x; simp [Rep.smul_apply]

instance (X : 𝒞) : IsScalarTower k (Alg F) (Rep F X) where
  smul_assoc c a m := by
    ext x
    simp [Rep.smul_apply, Linear.smul_comp, Finset.smul_sum]

/-- Postcomposition `R_X → R_Y`. -/
def repMap {X Y : 𝒞} (f : X ⟶ Y) : Rep F X →ₗ[Alg F] Rep F Y where
  toFun m y := m y ≫ f
  map_add' m n := by ext y; exact Preadditive.add_comp _ _ _ _ _ _
  map_smul' a m := by
    ext y
    change (∑ x, a y x ≫ m x) ≫ f = ∑ x, a y x ≫ (m x ≫ f)
    simp [Preadditive.sum_comp, Category.assoc]

@[simp] theorem repMap_apply {X Y : 𝒞} (f : X ⟶ Y) (m : Rep F X) (y : ι) :
    repMap f m y = m y ≫ f := rfl

/-! ### Idempotents and the Yoneda lemma -/

/-- The generator `1_x ∈ R_{F x}`. -/
def unit (x : ι) : Rep F (F x) := fun y ↦ idTo y x

/-- The column algebra element of `r ∈ R_{F x}`: `a_{yz} = r_y` for `z = x`. -/
def colAlg (x : ι) (r : Rep F (F x)) : Alg F := fun y z ↦ r y ≫ idTo x z

/-- The idempotent `e_x`. -/
def idem (x : ι) : Alg F := colAlg x (unit x)

theorem colAlg_smul_unit (x : ι) (r : Rep F (F x)) : colAlg x r • unit x = r := by
  ext y
  rw [Rep.smul_apply]
  simp only [colAlg, unit, Category.assoc]
  rw [← Preadditive.comp_sum, sum_idTo_comp x (fun z ↦ idTo (F := F) z x), idTo_self,
    Category.comp_id]

theorem colAlg_add (x : ι) (r s : Rep F (F x)) : colAlg x (r + s) = colAlg x r + colAlg x s := by
  ext y z; simp [colAlg, Preadditive.add_comp]

theorem colAlg_smul (x : ι) (a : Alg F) (r : Rep F (F x)) : colAlg x (a • r) = a * colAlg x r := by
  ext y z
  simp only [colAlg, mul_apply, Rep.smul_apply, Preadditive.sum_comp, Category.assoc]

theorem colAlg_smul' (x : ι) (c : k) (r : Rep F (F x)) : colAlg x (c • r) = c • colAlg x r := by
  ext y z; simp [colAlg, Linear.smul_comp]

theorem idem_mul_idem (x : ι) : idem (F := F) x * idem x = idem x := by
  rw [idem, ← colAlg_smul, colAlg_smul_unit]

variable {M : Type*} [AddCommGroup M] [Module (Alg F) M]

/-- **Yoneda**: maps out of `R_{F x}` are determined by the image of `1_x`. -/
theorem hom_ext {x : ι} {φ ψ : Rep F (F x) →ₗ[Alg F] M} (h : φ (unit x) = ψ (unit x)) : φ = ψ := by
  ext r
  rw [← colAlg_smul_unit x r, map_smul, map_smul, h]

/-- The map `R_{F x} → M` with `1_x ↦ m`. -/
def ofElem (x : ι) (m : M) : Rep F (F x) →ₗ[Alg F] M where
  toFun r := colAlg x r • m
  map_add' r s := by rw [colAlg_add, add_smul]
  map_smul' a r := by rw [colAlg_smul, mul_smul]; rfl

theorem ofElem_unit (x : ι) (m : M) : ofElem (F := F) x m (unit x) = idem (F := F) x • m := rfl

theorem ofElem_apply (x : ι) (m : M) (r : Rep F (F x)) : ofElem (F := F) x m r = colAlg x r • m :=
  rfl

/-- Every map out of `R_{F x}` is `ofElem` of the image of `1_x`. -/
theorem eq_ofElem {x : ι} (φ : Rep F (F x) →ₗ[Alg F] M) : φ = ofElem x (φ (unit x)) := by
  refine hom_ext ?_
  rw [ofElem_unit, ← map_smul]
  congr 1
  exact (colAlg_smul_unit (F := F) x (unit x)).symm

theorem idem_smul_rep {X : 𝒞} (x : ι) (m : Rep F X) (y : ι) :
    (idem (F := F) x • m) y = if y = x then m y else 0 := by
  rw [Rep.smul_apply]
  simp only [idem, colAlg, unit]
  by_cases h : y = x
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single y]
    · simp
    · intro z _ hz; rw [idTo_ne (Ne.symm hz), Limits.comp_zero, Limits.zero_comp]
    · simp
  · rw [if_neg h, idTo_ne h]
    simp

theorem unit_comp_apply {X : 𝒞} (x : ι) (f : F x ⟶ X) : (repMap f (unit x)) x = f := by
  simp [unit]

theorem smul_unit_component {X : 𝒞} (x : ι) (φ : Rep F (F x) →ₗ[Alg F] Rep F X) (y : ι) :
    (φ (unit x)) y = idTo y x ≫ (φ (unit x)) x := by
  have h : φ (unit x) = idem (F := F) x • φ (unit x) := by
    rw [← map_smul]
    congr 1
    exact (colAlg_smul_unit (F := F) x (unit x)).symm
  conv_lhs => rw [h]
  rw [idem_smul_rep]
  by_cases hy : y = x
  · subst hy; simp
  · rw [if_neg hy, idTo_ne hy, Limits.zero_comp]

/-- **Yoneda for representables**: `Hom(R_{F x}, R_X) = C(F x, X)`. -/
theorem eq_repMap {X : 𝒞} {x : ι} (φ : Rep F (F x) →ₗ[Alg F] Rep F X) :
    φ = repMap ((φ (unit x)) x) := by
  refine hom_ext ?_
  ext y
  rw [repMap_apply, smul_unit_component]
  rfl

theorem repMap_injective {X : 𝒞} {x : ι} {f g : F x ⟶ X} (h : repMap (F := F) f = repMap g) :
    f = g := by
  have := congrArg (fun φ ↦ (φ (unit x)) x) h
  change (repMap f (unit x)) x = (repMap g (unit x)) x at this
  rwa [unit_comp_apply, unit_comp_apply] at this

theorem repMap_comp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) :
    repMap (F := F) (f ≫ g) = (repMap g).comp (repMap f) := by
  ext m y; simp

theorem repMap_add {X Y : 𝒞} (f g : X ⟶ Y) : repMap (F := F) (f + g) = repMap f + repMap g := by
  ext m y; simp [Preadditive.comp_add]

theorem repMap_sum {X Y : 𝒞} {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ Y)) :
    repMap (F := F) (∑ i ∈ s, f i) = ∑ i ∈ s, repMap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext m y; simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, repMap_add, ih]

theorem repMap_zero {X Y : 𝒞} : repMap (F := F) (0 : X ⟶ Y) = 0 := by ext m y; simp

theorem repMap_smul_apply {X Y : 𝒞} (c : k) (f : X ⟶ Y) (m : Rep F X) :
    repMap (F := F) (c • f) m = c • repMap f m := by
  ext y; simp [Linear.comp_smul]

end CatAlg

end MultiplicativeBasisDeformations
