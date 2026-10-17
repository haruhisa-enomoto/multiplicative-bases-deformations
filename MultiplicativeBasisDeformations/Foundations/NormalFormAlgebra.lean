import MultiplicativeBasisDeformations.Foundations.NormalFormRetained
import MultiplicativeBasisDeformations.Foundations.CategoryAlgebra

/-!
# Proposition 5.4 for a filtered algebra

`prop:filtered-normal-form`: "Let `E` be a finite filtered algebra, or a finite filtered category
with the vertices of `Q` as objects, with a specified graded identification `gr E = C`. Then `E`
is isomorphic to `C` by a map inducing that identification."

The category case is `GeneralNormalForm.normalForm`. For an algebra `E` with a finite
multiplicative filtration and symbols `σ_d : F^d → C_d` into the algebra `C = ⊕_{x,y} C(x, y)`
(`CatAlg.Alg` of the relation category; `FilteredAlg`), the vertex idempotents of `C` lift to
orthogonal idempotents `f_x` of `E` through the nilpotent ideal `F¹`; the corners `f_x E f_y`
form a `k`-linear category (`CornerCat`) with the induced filtration and symbols
(`FilteredAlg.toFilteredId`); the category case gives a full and faithful functor from `C`, and
summing over the corners gives an algebra isomorphism `C ≅ E` inducing the identification
(`normalForm_algebra`). The same assembly applied to `normalFormRetained` gives Proposition 12.2
for an algebra: `E ≅ kQ/(𝔪^{N+1}, r_v − Σ_j λ_j (p_j)_v)` inducing the identification
(`normalFormRetained_algebra`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MultiplicativeBasisDeformations

namespace GeneralNormalForm

universe u

/-! ### The category of corners of an algebra -/

section Corner

variable {k : Type u} [Field k] {E : Type u} [Ring E] [Algebra k E] {V : Type} [Fintype V]
  [DecidableEq V] {f : V → E} (hf : CompleteOrthogonalIdempotents f)

variable (k f) in
/-- The corner `f_x E f_y`. -/
def corner (x y : V) : Submodule k E where
  carrier := {a | f x * a * f y = a}
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, mul_add, add_mul] at *; rw [ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by simp only [Set.mem_setOf_eq, mul_smul_comm, smul_mul_assoc] at *; rw [ha]

theorem mem_corner {x y : V} {a : E} : a ∈ corner k f x y ↔ f x * a * f y = a := Iff.rfl

include hf in
theorem left_mul_corner {x y : V} {a : E} (ha : a ∈ corner k f x y) : f x * a = a := by
  conv_lhs => rw [← ha]
  rw [← mul_assoc, ← mul_assoc, (hf.idem x).eq, ha]

include hf in
theorem corner_mul_right {x y : V} {a : E} (ha : a ∈ corner k f x y) : a * f y = a := by
  conv_lhs => rw [← ha]
  rw [mul_assoc, (hf.idem y).eq, ha]

include hf in
theorem mul_mem_corner {x y z : V} {a b : E} (ha : a ∈ corner k f x y) (hb : b ∈ corner k f y z) :
    a * b ∈ corner k f x z := by
  rw [mem_corner, ← mul_assoc, left_mul_corner hf ha, mul_assoc, corner_mul_right hf hb]

include hf in
theorem idem_mem_corner (x : V) : f x ∈ corner k f x x := by
  rw [mem_corner, (hf.idem x).eq, (hf.idem x).eq]

include hf in
theorem corner_mul_corner_ne {x y y' z : V} (h : y ≠ y') {a b : E} (ha : a ∈ corner k f x y)
    (hb : b ∈ corner k f y' z) : a * b = 0 := by
  rw [← corner_mul_right hf ha, ← left_mul_corner hf hb, mul_assoc, ← mul_assoc (f y),
    hf.ortho h, zero_mul, mul_zero]

include hf in
theorem eq_sum_corner (a : E) : a = ∑ x, ∑ y, f x * a * f y := by
  calc a = (∑ x, f x) * a * (∑ y, f y) := by rw [hf.complete, one_mul, mul_one]
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; simp_rw [Finset.mul_sum]

include hf in
theorem corner_proj_mem (a : E) (x y : V) : f x * a * f y ∈ corner k f x y := by
  rw [mem_corner, ← mul_assoc, ← mul_assoc, (hf.idem x).eq, mul_assoc, (hf.idem y).eq]

/-- **The category of corners** `f_x E f_y`, composition the product of `E`. -/
@[nolint unusedArguments]
def CornerCat (_k : Type u) (_hf : CompleteOrthogonalIdempotents f) : Type := V

instance : Category (CornerCat k hf) where
  Hom x y := corner k f x y
  id x := ⟨f x, idem_mem_corner hf x⟩
  comp a b := ⟨a.1 * b.1, mul_mem_corner hf a.2 b.2⟩
  id_comp a := Subtype.ext (left_mul_corner hf a.2)
  comp_id a := Subtype.ext (corner_mul_right hf a.2)
  assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)

@[simp] theorem cc_comp_val {x y z : CornerCat k hf} (a : x ⟶ y) (b : y ⟶ z) :
    (a ≫ b).1 = a.1 * b.1 := rfl

@[simp] theorem cc_id_val (x : CornerCat k hf) : (𝟙 x : x ⟶ x).1 = f x := rfl

instance : Preadditive (CornerCat k hf) where
  homGroup x y := inferInstanceAs (AddCommGroup (corner k f x y))
  add_comp _ _ _ a a' b := Subtype.ext (add_mul a.1 a'.1 b.1)
  comp_add _ _ _ a b b' := Subtype.ext (mul_add a.1 b.1 b'.1)

instance : Linear k (CornerCat k hf) where
  homModule x y := inferInstanceAs (Module k (corner k f x y))
  smul_comp _ _ _ c a b := Subtype.ext (smul_mul_assoc c a.1 b.1)
  comp_smul _ _ _ a c b := Subtype.ext (mul_smul_comm c a.1 b.1)

include hf in
theorem idem_mul_corner_mul_idem (x y : V) {x' y' : V} {a : E} (ha : a ∈ corner k f x' y') :
    f x * a * f y = if x = x' then if y = y' then a else 0 else 0 := by
  by_cases hx : x = x'
  · subst hx
    by_cases hy : y = y'
    · subst hy; rw [if_pos rfl, if_pos rfl]; exact ha
    · rw [if_pos rfl, if_neg hy, ← corner_mul_right hf ha, mul_assoc (f x), mul_assoc a, hf.ortho (Ne.symm hy),
        mul_zero, mul_zero]
  · rw [if_neg hx, ← left_mul_corner hf ha, ← mul_assoc, hf.ortho hx, zero_mul, zero_mul]

/-- The objects of the category of corners. -/
def cobj (hf : CompleteOrthogonalIdempotents f) (x : V) : CornerCat k hf := x

end Corner

/-! ### Matrix units of a category algebra -/

section Units

open CatAlg

variable {k : Type u} [Field k] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → 𝒞}

/-- The matrix unit with entry `c` at `(x, y)`. -/
def sgl (x y : ι) (c : G x ⟶ G y) : Alg G := fun a b ↦ idTo a x ≫ c ≫ idTo y b

theorem sgl_self (x y : ι) (c : G x ⟶ G y) : sgl x y c x y = c := by simp [sgl]

theorem sgl_zero (x y : ι) : sgl (G := G) x y 0 = 0 := by ext a b; simp [sgl]

theorem sum_sgl (m : Alg G) : ∑ x, ∑ y, sgl x y (m x y) = m := by
  ext a b
  simp only [CatAlg.sum_apply, sgl]
  simp_rw [← Preadditive.comp_sum, sum_comp_idTo_alg]
  exact sum_idTo_comp_alg m a b

theorem sgl_mem {S : ∀ x y : ι, Submodule k (G x ⟶ G y)} {x y : ι} {c : G x ⟶ G y}
    (hc : c ∈ S x y) (a b : ι) : sgl x y c a b ∈ S a b := by
  by_cases ha : a = x
  · subst ha
    by_cases hb : y = b
    · subst hb; simpa [sgl] using hc
    · simp [sgl, idTo_ne hb]
  · simp [sgl, idTo_ne ha]

theorem idem_mul_apply (x : ι) (m : Alg G) (a c : ι) : (idem x * m : Alg G) a c = idTo a x ≫ m x c := by
  rw [mul_apply]
  simp only [idem, colAlg, unit, Category.assoc]
  rw [← Preadditive.comp_sum, sum_idTo_comp_alg]

theorem mul_idem_apply (y : ι) (m : Alg G) (a b : ι) : (m * idem y : Alg G) a b = m a y ≫ idTo y b := by
  rw [mul_apply]
  simp only [idem, colAlg, unit]
  simp_rw [← Category.assoc, ← Preadditive.sum_comp, sum_comp_idTo_alg]

theorem idem_mul_mul_idem (x y : ι) (m : Alg G) : idem x * m * idem y = sgl x y (m x y) := by
  ext a b
  rw [mul_idem_apply, idem_mul_apply, sgl, Category.assoc]

theorem idem_eq_sgl (x : ι) : idem (F := G) x = sgl x x (𝟙 _) := by
  ext a b; simp [idem, colAlg, unit, sgl]

variable (G) in
theorem idem_complete : CompleteOrthogonalIdempotents (fun x : ι ↦ idem (F := G) x) where
  idem x := idem_mul_idem x
  ortho x y h := by
    change idem x * idem y = 0
    rw [← mul_one (idem x), idem_mul_mul_idem, one_apply, idTo_ne h, sgl_zero]
  complete := by
    ext a b
    simp only [CatAlg.sum_apply, idem, colAlg, unit, one_apply]
    exact sum_idTo_comp a (fun x ↦ idTo (F := G) x b)

end Units

/-! ### Filtered algebras -/

section Algebra

open CatAlg

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {ι : Type} (s t : ι → V)
  (r : ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i))

/-- The objects of `C`. -/
abbrev clObj (x : V) := (cl s t r).obj (LinearPaths.obj (k := k) x)

theorem id_mem_Cdeg (x : V) : 𝟙 (clObj s t r x) ∈ Cdeg s t r 0 x x := by
  rw [← (cl s t r).map_id]
  exact cl_mem_Cdeg s t r (LinearPaths.path_mem_degreePart (k := k) (Quiver.Path.nil : Quiver.Path x x))

/-- **A finite filtered algebra `E` with `gr E = C`**: a finite multiplicative filtration `F` of
`E` and symbols `σ_d : F^d → C_d` into the category algebra of `C`, onto, with kernel `F^{d+1}`,
multiplicative and unital. -/
structure FilteredAlg (E : Type u) [Ring E] [Algebra k E] where
  F : ℕ → Submodule k E
  F_zero : F 0 = ⊤
  F_succ_le : ∀ d, F (d + 1) ≤ F d
  F_mul : ∀ (d e : ℕ) {a b : E}, a ∈ F d → b ∈ F e → a * b ∈ F (d + e)
  N : ℕ
  F_N : F N = ⊥
  σ : ℕ → E →ₗ[k] Alg (clObj s t r)
  σ_mem : ∀ d a, a ∈ F d → ∀ x y, σ d a x y ∈ Cdeg s t r d x y
  σ_ker : ∀ d a, a ∈ F d → (σ d a = 0 ↔ a ∈ F (d + 1))
  σ_surj : ∀ d (c : Alg (clObj s t r)), (∀ x y, c x y ∈ Cdeg s t r d x y) →
    ∃ a ∈ F d, σ d a = c
  σ_mul : ∀ (d e : ℕ) {a b : E}, a ∈ F d → b ∈ F e → σ (d + e) (a * b) = σ d a * σ e b
  σ_one : σ 0 1 = 1

variable {s t r} {E : Type u} [Ring E] [Algebra k E] (A : FilteredAlg s t r E)

namespace FilteredAlg

theorem mem_F_zero (a : E) : a ∈ A.F 0 := by rw [A.F_zero]; trivial

/-- The degree-zero symbol, a ring map with nilpotent kernel `F¹`. -/
def σ₀ : E →+* Alg (clObj s t r) where
  toFun := A.σ 0
  map_one' := A.σ_one
  map_mul' a b := A.σ_mul 0 0 (A.mem_F_zero a) (A.mem_F_zero b)
  map_zero' := map_zero (A.σ 0)
  map_add' := map_add (A.σ 0)

theorem pow_mem {a : E} (ha : a ∈ A.F 1) : ∀ n, a ^ n ∈ A.F n
  | 0 => A.mem_F_zero _
  | n + 1 => by rw [pow_succ]; exact A.F_mul n 1 (pow_mem ha n) ha

theorem isNilpotent_of_ker {a : E} (ha : a ∈ RingHom.ker A.σ₀) : IsNilpotent a := by
  have h1 : a ∈ A.F 1 := (A.σ_ker 0 a (A.mem_F_zero a)).1 ((RingHom.mem_ker (f := A.σ₀)).1 ha)
  refine ⟨A.N, ?_⟩
  have := A.pow_mem h1 A.N
  rwa [A.F_N, Submodule.mem_bot] at this

/-- **The vertex idempotents lift** through the nilpotent ideal `F¹`. -/
theorem exists_idem : ∃ f : V → E, CompleteOrthogonalIdempotents f ∧
    ∀ x, A.σ 0 (f x) = idem (F := clObj s t r) x := by
  obtain ⟨f, hf, hσ⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker A.σ₀
    (fun a ha ↦ A.isNilpotent_of_ker ha) (idem_complete (clObj s t r)) (fun x ↦ by
      obtain ⟨a, -, ha⟩ := A.σ_surj 0 (idem x) (fun a b ↦ by
        rw [idem_eq_sgl]; exact sgl_mem (S := Cdeg s t r 0) (id_mem_Cdeg s t r x) a b)
      exact ⟨a, ha⟩)
  exact ⟨f, hf, fun x ↦ congrFun hσ x⟩

variable {f : V → E} (hf : CompleteOrthogonalIdempotents f)
  (hσf : ∀ x, A.σ 0 (f x) = idem (F := clObj s t r) x)

include hσf in
theorem σ_corner {d : ℕ} {g : E} (hg : g ∈ A.F d) (x y : V) :
    A.σ d (f x * g * f y) = sgl x y (A.σ d g x y) := by
  have h1 := A.σ_mul 0 d (A.mem_F_zero (f x)) hg
  have hfg : f x * g ∈ A.F d := by simpa using A.F_mul 0 d (A.mem_F_zero (f x)) hg
  have h2 := A.σ_mul d 0 hfg (A.mem_F_zero (f y))
  simp only [Nat.zero_add, Nat.add_zero] at h1 h2
  rw [h2, h1, hσf, hσf, idem_mul_mul_idem]

theorem corner_mem_F {d : ℕ} {g : E} (hg : g ∈ A.F d) (x y : V) : f x * g * f y ∈ A.F d := by
  have hfg : f x * g ∈ A.F d := by simpa using A.F_mul 0 d (A.mem_F_zero (f x)) hg
  simpa using A.F_mul d 0 hfg (A.mem_F_zero (f y))

include hσf in
theorem σ_conc {d : ℕ} {x y : V} {a : E} (ha : a ∈ corner k f x y) (had : a ∈ A.F d) :
    A.σ d a = sgl x y (A.σ d a x y) := by
  conv_lhs => rw [← (mem_corner.1 ha)]
  rw [A.σ_corner hσf had]

/-- **The filtered category of corners** `f_x E f_y`, with the induced filtration and symbols. -/
def toFilteredId : FilteredId (cobj (k := k) hf) s t r where
  F d x y := (A.F d).comap (corner k f x y).subtype
  F_zero x y := by rw [A.F_zero]; exact Submodule.comap_top _
  F_succ_le d x y := Submodule.comap_mono (A.F_succ_le d)
  F_comp d e x y z a b ha hb := A.F_mul d e ha hb
  N := A.N
  F_N x y := by
    ext a
    simp only [Submodule.mem_comap, A.F_N, Submodule.mem_bot, Submodule.subtype_apply]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [h]; rfl⟩
  σ d x y :=
    { toFun := fun a ↦ A.σ d a.1 x y
      map_add' := fun a b ↦ by
        change A.σ d (a.1 + b.1) x y = _
        rw [map_add]; rfl
      map_smul' := fun c a ↦ by
        change A.σ d (c • a.1) x y = _
        rw [map_smul]; rfl }
  σ_mem d x y a ha := A.σ_mem d a.1 ha x y
  σ_ker d x y a ha := by
    change A.σ d a.1 x y = 0 ↔ a.1 ∈ A.F (d + 1)
    rw [← A.σ_ker d a.1 ha]
    constructor
    · intro h; rw [A.σ_conc hσf (x := x) (y := y) a.2 ha, h, sgl_zero]
    · intro h; rw [h]; rfl
  σ_surj d x y c hc := by
    obtain ⟨g, hg, hgc⟩ := A.σ_surj d (sgl x y c) (fun a b ↦ sgl_mem (S := Cdeg s t r d) hc a b)
    refine ⟨⟨f x * g * f y, corner_proj_mem hf g x y⟩, A.corner_mem_F hg x y, ?_⟩
    change A.σ d (f x * g * f y) x y = c
    rw [A.σ_corner hσf hg, hgc, sgl_self, sgl_self]
  σ_comp d e x y z a b ha hb := by
    have ha' : a.1 ∈ A.F d := ha
    have hb' : b.1 ∈ A.F e := hb
    change A.σ (d + e) (a.1 * b.1) x z = A.σ d a.1 x y ≫ A.σ e b.1 y z
    rw [A.σ_mul d e ha' hb', mul_apply]
    conv_lhs => rw [A.σ_conc hσf (x := x) (y := y) a.2 ha']
    simp only [sgl, Category.assoc, idTo_self, Category.id_comp]
    rw [← Preadditive.comp_sum, sum_idTo_comp_alg]
  σ_id x := by
    change A.σ 0 (f x) x x = 𝟙 _
    rw [hσf, idem_eq_sgl, sgl_self]

end FilteredAlg

/-! ### From corner maps to an algebra isomorphism -/

section Assembly

variable {E' : Type u} [Ring E'] [Algebra k E'] {f : V → E'} (hf : CompleteOrthogonalIdempotents f)
  {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear k 𝒟] {G : V → 𝒟}

include hf in
/-- **Assembly**: maps `φ_{xy} : 𝒟(G x, G y) → f_x E f_y`, bijective onto the corners and
compatible with composition and identities, sum to an algebra isomorphism `Alg G ≅ E`. -/
theorem exists_algEquiv (φ : ∀ x y : V, (G x ⟶ G y) →ₗ[k] E')
    (hmem : ∀ x y c, φ x y c ∈ corner k f x y)
    (hcomp : ∀ x y z (c : G x ⟶ G y) (c' : G y ⟶ G z), φ x z (c ≫ c') = φ x y c * φ y z c')
    (hid : ∀ x, φ x x (𝟙 _) = f x) (hinj : ∀ x y c, φ x y c = 0 → c = 0)
    (hsurj : ∀ x y a, a ∈ corner k f x y → ∃ c, φ x y c = a) :
    ∃ Ψ : Alg G ≃ₐ[k] E', ∀ m, Ψ m = ∑ x, ∑ y, φ x y (m x y) := by
  let Ψl : Alg G →ₗ[k] E' :=
    { toFun := fun m ↦ ∑ x, ∑ y, φ x y (m x y)
      map_add' := fun m n ↦ by simp only [CatAlg.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := fun a m ↦ by
        simp only [CatAlg.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum] }
  have hΨl : ∀ m, Ψl m = ∑ x, ∑ y, φ x y (m x y) := fun m ↦ rfl
  have hcorner : ∀ x y x' y' (c : G x' ⟶ G y'),
      f x * φ x' y' c * f y = if x = x' then if y = y' then φ x' y' c else 0 else 0 :=
    fun x y x' y' c ↦ idem_mul_corner_mul_idem hf x y (hmem x' y' c)
  have hproj : ∀ m x y, f x * Ψl m * f y = φ x y (m x y) := by
    intro m x y
    simp only [hΨl, Finset.mul_sum, Finset.sum_mul]
    rw [Fintype.sum_eq_single x (fun x' hx' ↦ Finset.sum_eq_zero fun y' _ ↦ by
        rw [hcorner, if_neg (Ne.symm hx')]),
      Fintype.sum_eq_single y (fun y' hy' ↦ by rw [hcorner, if_pos rfl, if_neg (Ne.symm hy')]),
      hcorner, if_pos rfl, if_pos rfl]
  have hsum : ∀ (m n : Alg G) x z,
      φ x z (∑ y, m x y ≫ n y z) = ∑ y, φ x y (m x y) * φ y z (n y z) := by
    intro m n x z
    rw [map_sum]
    exact Finset.sum_congr rfl fun y _ ↦ hcomp x y z _ _
  let Ψa : Alg G →ₐ[k] E' := AlgHom.ofLinearMap Ψl (by
      rw [hΨl, ← hf.complete]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Fintype.sum_eq_single x (fun y hy ↦ by
        rw [CatAlg.one_apply, idTo_ne (Ne.symm hy), map_zero]), CatAlg.one_apply, idTo_self, hid])
    (fun m n ↦ by
      simp only [hΨl, CatAlg.mul_apply, hsum]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      exact (Fintype.sum_eq_single y (fun x' hx' ↦ Finset.sum_eq_zero fun z _ ↦
        corner_mul_corner_ne hf (Ne.symm hx') (hmem x y (m x y)) (hmem x' z (n x' z)))).symm)
  have hΨa : ∀ m, Ψa m = Ψl m := fun m ↦ rfl
  have hinj' : Function.Injective Ψa := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    ext x y
    rw [CatAlg.zero_apply]
    apply hinj
    rw [← hproj, ← hΨa, hm, mul_zero, zero_mul]
  have hsurj' : Function.Surjective Ψa := by
    intro e
    choose c hc using fun x y ↦ hsurj x y _ (corner_proj_mem hf e x y)
    let c' : Alg G := c
    refine ⟨c', ?_⟩
    rw [hΨa, hΨl]
    conv_rhs => rw [eq_sum_corner hf e]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ hc x y
  exact ⟨AlgEquiv.ofBijective Ψa ⟨hinj', hsurj'⟩, fun m ↦ rfl⟩

/-- **Corner maps from a full and faithful functor** `kQ/R → (corners of E)` lifting the
realization of paths. -/
theorem exists_cornerMaps {R : ∀ X Y : LinearPaths k V, Set (X ⟶ Y)}
    (L : ∀ {x y : V}, (x ⟶ y) → (cobj (k := k) hf x ⟶ cobj hf y))
    (Φ : RelationCategory k R ⥤ CornerCat k hf)
    (hΦ : RelationCategory.functor k R ⋙ Φ = pathFunctor L) (hfull : Φ.Full)
    (hfaith : Φ.Faithful) :
    ∃ φ : ∀ x y : V, ((RelationCategory.functor k R).obj (LinearPaths.obj x) ⟶
        (RelationCategory.functor k R).obj (LinearPaths.obj y)) →ₗ[k] E',
      (∀ x y P, φ x y ((RelationCategory.functor k R).map P) = (realize L x y P).1) ∧
      (∀ x y c, φ x y c ∈ corner k f x y) ∧
      (∀ x y z c c', φ x z (c ≫ c') = φ x y c * φ y z c') ∧
      (∀ x, φ x x (𝟙 _) = f x) ∧ (∀ x y c, φ x y c = 0 → c = 0) ∧
      (∀ x y a, a ∈ corner k f x y → ∃ c, φ x y c = a) := by
  have hobj : ∀ x : V, Φ.obj ((RelationCategory.functor k R).obj (LinearPaths.obj x)) =
      cobj (k := k) hf x := fun x ↦ Functor.congr_obj hΦ (LinearPaths.obj x)
  let φ : ∀ x y : V, ((RelationCategory.functor k R).obj (LinearPaths.obj x) ⟶
      (RelationCategory.functor k R).obj (LinearPaths.obj y)) → (cobj (k := k) hf x ⟶ cobj hf y) :=
    fun x y c ↦ eqToHom (hobj x).symm ≫ Φ.map c ≫ eqToHom (hobj y)
  have hφP : ∀ x y (P : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y),
      φ x y ((RelationCategory.functor k R).map P) = realize L x y P := by
    intro x y P
    have h := Functor.congr_hom hΦ P
    simp only [Functor.comp_map] at h
    simp only [φ, h, eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    have e1 : ∀ p : cobj (k := k) hf x = (pathFunctor (k := k) (O := cobj (k := k) hf) L).obj
        (LinearPaths.obj x), eqToHom p = 𝟙 _ := fun p ↦ eqToHom_refl _ p
    have e2 : ∀ p : (pathFunctor (k := k) (O := cobj (k := k) hf) L).obj (LinearPaths.obj y) =
        cobj (k := k) hf y, eqToHom p = 𝟙 _ := fun p ↦ eqToHom_refl _ p
    rw [e1, e2]
    erw [Category.id_comp, Category.comp_id]
    rfl
  have hφadd : ∀ x y c c', φ x y (c + c') = φ x y c + φ x y c' := by
    intro x y c c'
    obtain ⟨P, rfl⟩ := (RelationCategory.functor k R).map_surjective
      (X := LinearPaths.obj x) (Y := LinearPaths.obj y) c
    obtain ⟨P', rfl⟩ := (RelationCategory.functor k R).map_surjective
      (X := LinearPaths.obj x) (Y := LinearPaths.obj y) c'
    rw [← Functor.map_add, hφP, hφP, hφP, map_add]
  have hφsmul : ∀ x y (a : k) c, φ x y (a • c) = a • φ x y c := by
    intro x y a c
    obtain ⟨P, rfl⟩ := (RelationCategory.functor k R).map_surjective
      (X := LinearPaths.obj x) (Y := LinearPaths.obj y) c
    rw [← Functor.map_smul, hφP, hφP, map_smul]
  have hφzero : ∀ x y, φ x y 0 = 0 := fun x y ↦ by
    have := hφsmul x y 0 0; rwa [zero_smul, zero_smul] at this
  let φL : ∀ x y : V, ((RelationCategory.functor k R).obj (LinearPaths.obj x) ⟶
      (RelationCategory.functor k R).obj (LinearPaths.obj y)) →ₗ[k] E' := fun x y ↦
    { toFun := fun c ↦ (φ x y c).1
      map_add' := fun c c' ↦ by rw [hφadd]; rfl
      map_smul' := fun a c ↦ by rw [hφsmul]; rfl }
  refine ⟨φL, fun x y P ↦ congrArg Subtype.val (hφP x y P), fun x y c ↦ (φ x y c).2,
    fun x y z c c' ↦ ?_, fun x ↦ ?_, fun x y c h ↦ ?_, fun x y a ha ↦ ?_⟩
  · change (φ x z (c ≫ c')).1 = (φ x y c).1 * (φ y z c').1
    rw [← cc_comp_val]
    congr 1
    simp only [φ, Functor.map_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  · change (φ x x (𝟙 _)).1 = f x
    have : φ x x (𝟙 _) = 𝟙 (cobj hf x) := by simp [φ]
    rw [this]; rfl
  · have h' : φ x y c = φ x y 0 := by rw [hφzero]; exact Subtype.ext h
    have h2 := congrArg (fun g ↦ eqToHom (hobj x) ≫ g ≫ eqToHom (hobj y).symm) h'
    simp only [φ, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
      eqToHom_trans, Category.comp_id] at h2
    exact Φ.map_injective h2
  · let a' : cobj (k := k) hf x ⟶ cobj hf y := ⟨a, ha⟩
    refine ⟨Φ.preimage (eqToHom (hobj x) ≫ a' ≫ eqToHom (hobj y).symm), ?_⟩
    change (φ x y _).1 = a
    simp [φ, a']

end Assembly

/-- **Proposition 5.4** (`prop:filtered-normal-form`) **for a filtered algebra**: under the
hypotheses of the general form (quadratic relations, surjective `D_{q-1}` for `q ≥ 3`), a finite
filtered algebra `E` with a graded identification `gr E = C` is isomorphic to the category
algebra of `C` by a map inducing that identification: it sends `C_d` into `F^d E` with symbol
the identity. -/
theorem normalForm_algebra
    (hr : ∀ i, r i ∈ LinearPaths.degreePart (k := k) 2 (s i) (t i))
    (hDsurj : ∀ q', 2 ≤ q' → ∀ g : ∀ i, (cl s t r).obj (LinearPaths.obj (s i)) ⟶
        (cl s t r).obj (LinearPaths.obj (t i)), (∀ i, g i ∈ Cdeg s t r (q' + 1) (s i) (t i)) →
      ∃ f : ∀ {x y : V}, (x ⟶ y) →
          ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y)),
        (∀ {x y : V} (a : x ⟶ y), f a ∈ Cdeg s t r q' x y) ∧ ∀ i, Dmap f i = g i) :
    ∃ Ψ : Alg (clObj s t r) ≃ₐ[k] E, ∀ (d : ℕ) (c : Alg (clObj s t r)),
      (∀ x y, c x y ∈ Cdeg s t r d x y) → Ψ c ∈ A.F d ∧ A.σ d (Ψ c) = c := by
  obtain ⟨f, hf, hσf⟩ := A.exists_idem
  obtain ⟨L, -, Φ, hΦ, hfull, hfaith, hreal⟩ := normalForm (A.toFilteredId hf hσf) hr hDsurj
  obtain ⟨φ, hφP, hmem, hcomp, hid, hinj, hsurj⟩ := exists_cornerMaps hf L.L Φ hΦ hfull hfaith
  obtain ⟨Ψ, hΨ⟩ := exists_algEquiv hf φ hmem hcomp hid hinj hsurj
  have hφdeg : ∀ (d : ℕ) x y (c : clObj s t r x ⟶ clObj s t r y), c ∈ Cdeg s t r d x y →
      φ x y c ∈ A.F d ∧ A.σ d (φ x y c) x y = c := by
    rintro d x y c ⟨P, hP, rfl⟩
    change φ x y ((cl s t r).map P) ∈ A.F d ∧ A.σ d (φ x y ((cl s t r).map P)) x y =
      (cl s t r).map P
    rw [hφP]
    exact hreal d P hP
  refine ⟨Ψ, fun d c hc ↦ ?_⟩
  rw [hΨ]
  refine ⟨Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ (hφdeg d x y _ (hc x y)).1, ?_⟩
  simp only [map_sum]
  conv_rhs => rw [← sum_sgl c]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  obtain ⟨h1, h2⟩ := hφdeg d x y _ (hc x y)
  rw [A.σ_conc hσf (x := x) (y := y) (hmem x y (c x y)) h1, h2]

/-- **Proposition 12.2** (`prop:characteristic-two-normal-form`) **for a filtered algebra**:
under the hypotheses of `normalFormRetained` (quadratic relations, retained tuples `p_j` of degrees
`≥ 3` whose classes together with `im D_{q-1}` span), every finite filtered algebra `E` with a
graded identification `gr E = C` has a presentation `E ≅ kQ/(𝔪^{N+1}, r_v − Σ_j λ_j (p_j)_v)`
(the category algebra of the relation category `RelRet r p λ N`, with `F^N E = 0`) for some
scalars `λ`, and the isomorphism induces the identification: it sends the class of a family of
degree-`d` path combinations into `F^d E`, with symbol its class in `C`. -/
theorem normalFormRetained_algebra {J : Type} [Fintype J] {deg : J → ℕ}
    {p : J → ∀ i, LinearPaths.obj (k := k) (s i) ⟶ LinearPaths.obj (k := k) (t i)}
    (hdeg : ∀ j, 3 ≤ deg j)
    (hp : ∀ j i, p j i ∈ LinearPaths.degreePart (k := k) (deg j) (s i) (t i))
    (hr : ∀ i, r i ∈ LinearPaths.degreePart (k := k) 2 (s i) (t i))
    (hspan : ∀ q', 2 ≤ q' → ∀ g : ∀ i, (cl s t r).obj (LinearPaths.obj (s i)) ⟶
        (cl s t r).obj (LinearPaths.obj (t i)), (∀ i, g i ∈ Cdeg s t r (q' + 1) (s i) (t i)) →
      ∃ (f : ∀ {x y : V}, (x ⟶ y) →
          ((cl s t r).obj (LinearPaths.obj x) ⟶ (cl s t r).obj (LinearPaths.obj y))) (c : J → k),
        (∀ {x y : V} (a : x ⟶ y), f a ∈ Cdeg s t r q' x y) ∧ (∀ j, deg j ≠ q' + 1 → c j = 0) ∧
        ∀ i, g i = Dmap f i + ∑ j, c j • (cl s t r).map (p j i)) :
    ∃ (lam : J → k) (Ψ : Alg (fun x : V ↦ (RelationCategory.functor k (RelRet r p lam A.N)).obj
        (LinearPaths.obj x)) ≃ₐ[k] E),
      ∀ (d : ℕ) (P : ∀ x y : V, LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y),
        (∀ x y, P x y ∈ LinearPaths.degreePart (k := k) d x y) →
        Ψ (fun x y ↦ (RelationCategory.functor k (RelRet r p lam A.N)).map (P x y)) ∈ A.F d ∧
        A.σ d (Ψ (fun x y ↦ (RelationCategory.functor k (RelRet r p lam A.N)).map (P x y))) =
          fun x y ↦ (cl s t r).map (P x y) := by
  obtain ⟨f, hf, hσf⟩ := A.exists_idem
  obtain ⟨lam, L, -, -, hpres, hreal⟩ :=
    normalFormRetained (E := A.toFilteredId hf hσf) hdeg hp hr hspan
  obtain ⟨-, Φ, hΦ, hfull, hfaith⟩ := hpres A.N (A.toFilteredId hf hσf).F_N
  obtain ⟨φ, hφP, hmem, hcomp, hid, hinj, hsurj⟩ := exists_cornerMaps hf L.L Φ hΦ hfull hfaith
  obtain ⟨Ψ, hΨ⟩ := exists_algEquiv hf φ hmem hcomp hid hinj hsurj
  refine ⟨lam, Ψ, fun d P hP ↦ ?_⟩
  set m : Alg (fun x : V ↦ (RelationCategory.functor k (RelRet r p lam A.N)).obj
    (LinearPaths.obj x)) := fun x y ↦ (RelationCategory.functor k (RelRet r p lam A.N)).map (P x y)
    with hm
  rw [hΨ m]
  simp only [hm, hφP]
  refine ⟨Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun y _ ↦ (hreal d (P x y) (hP x y)).1,
    ?_⟩
  simp only [map_sum]
  conv_rhs => rw [← sum_sgl (fun x y ↦ (cl s t r).map (P x y))]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  obtain ⟨h1, h2⟩ := hreal d (P x y) (hP x y)
  rw [A.σ_conc hσf (x := x) (y := y) (realize L.L x y (P x y)).2 h1]
  exact congrArg (sgl x y) h2

end Algebra

end GeneralNormalForm

end MultiplicativeBasisDeformations
