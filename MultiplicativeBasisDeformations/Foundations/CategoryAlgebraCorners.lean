import MultiplicativeBasisDeformations.Foundations.FullIdempotent
import MultiplicativeBasisDeformations.Foundations.SplitTransfer
import MultiplicativeBasisDeformations.Foundations.CategoryAlgebra

/-!
# Repeated labels in category algebras

For Lemma 4.7 (`lem:homogeneous-projection`, `scalar-normalization.tex:305–320`):
"Enlarge it to the category `B'` on the same labels with `B'(i,j) = B(x_i,x_j)`.
Repeated labels give matrix multiplicities, and the distinct labels give an
idempotent corner of `B`. Thus `B'` is representation-finite by Morita
equivalence and Lemma 3.1(1)."

For a family `F : ι → C` and a relabelling `σ : κ → ι`, both `Alg F` and
`Alg (F ∘ σ)` are idempotent corners of the category algebra of the family
`F ⊔ (F ∘ σ)` on `ι ⊕ κ`, and the first corner is at a full idempotent. So if
`Alg F` is representation-finite, so are the big algebra (Morita,
`isRepresentationFinite_of_full`) and its corner `Alg (F ∘ σ)` (Lemma 3.1(1))
(`isRepresentationFinite_comp`). Algebras are taken opposite, so that right
modules are the modules `Rep F X` of `CategoryAlgebra.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

/-! ### Transfer along isomorphisms and corners given by embeddings -/

section General

variable {k : Type u} [Field k]

/-- Representation-finiteness is invariant under algebra isomorphisms (an
instance of Lemma 4.6 with `C = B`). -/
theorem isRepresentationFinite_of_algEquiv {B D : Type v} [Ring B] [Algebra k B] [Ring D]
    [Algebra k D] [FiniteDimensional k B] [FiniteDimensional k D] (φ : B ≃ₐ[k] D)
    (hB : IsRepresentationFinite k B) : IsRepresentationFinite k D :=
  splitRepresentationTransfer_of (C := ⊤) (q := φ.toAlgHom.comp (Subalgebra.val ⊤))
    φ.toLinearMap (fun c c' b ↦ by simp [map_mul]) (fun d ↦ ⟨⟨φ.symm d, trivial⟩, by simp⟩)
    (fun c ↦ rfl) hB

variable {A : Type v} [Ring A] [Algebra k A] {e : A} (he : IsIdempotentElem e)
  {B : Type v} [Ring B] [Algebra k B] (φ : B →ₗ[k] A) (hmul : ∀ a b, φ (a * b) = φ a * φ b)
  (hone : φ 1 = e)

include he hmul hone in
theorem mem_corner_of (b : B) : φ b ∈ Subsemigroup.corner e := by
  refine (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩
  · rw [← hone, ← hmul, one_mul]
  · rw [← hone, ← hmul, mul_one]

/-- An algebra embedded multiplicatively onto a corner is isomorphic to it. -/
def cornerEquivOf (hinj : Function.Injective φ)
    (hsurj : ∀ x : A, e * x * e = x → ∃ b, φ b = x) : B ≃ₐ[k] he.Corner :=
  AlgEquiv.ofBijective
    { toFun b := cornerMk he (φ b) (mem_corner_of he φ hmul hone b)
      map_one' := corner_ext he (by simp [hone])
      map_mul' a b := corner_ext he (by simp [hmul])
      map_zero' := corner_ext he (by simp)
      map_add' a b := corner_ext he (by simp)
      commutes' c := corner_ext he (by
        simp only [cornerVal_mk]
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hone]
        rfl) }
    ⟨fun a b h ↦ hinj (by
        have := congrArg (cornerVal he) h
        simpa using this),
      fun x ↦ by
        obtain ⟨b, hb⟩ := hsurj (cornerVal he x) (by
          rw [corner_mul_left, corner_mul_right])
        exact ⟨b, corner_ext he (by simpa using hb)⟩⟩

end General

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (F : ι → 𝒞) (F₂ : κ → 𝒞)

/-- The family `F ⊔ F₂` on `ι ⊕ κ`. -/
abbrev FS : ι ⊕ κ → 𝒞 := Sum.elim F F₂

/-- `Alg F` inside `Alg (F ⊔ F₂)`. -/
def embL (a : Alg F) : Alg (FS F F₂)
  | Sum.inl x, Sum.inl y => a x y
  | _, _ => 0

/-- `Alg F₂` inside `Alg (F ⊔ F₂)`. -/
def embR (b : Alg F₂) : Alg (FS F F₂)
  | Sum.inr x, Sum.inr y => b x y
  | _, _ => 0

/-- Restriction to the `ι`-block. -/
def resL (c : Alg (FS F F₂)) : Alg F := fun x y ↦ c (Sum.inl x) (Sum.inl y)

/-- Restriction to the `κ`-block. -/
def resR (c : Alg (FS F F₂)) : Alg F₂ := fun x y ↦ c (Sum.inr x) (Sum.inr y)

variable {F F₂}

theorem resL_embL (a : Alg F) : resL F F₂ (embL F F₂ a) = a := rfl
theorem resR_embR (b : Alg F₂) : resR F F₂ (embR F F₂ b) = b := rfl

@[simp] theorem embL_ll (a : Alg F) (x y : ι) : embL F F₂ a (Sum.inl x) (Sum.inl y) = a x y := rfl
@[simp] theorem embL_lr (a : Alg F) (x : ι) (y : κ) : embL F F₂ a (Sum.inl x) (Sum.inr y) = 0 := rfl
@[simp] theorem embL_rl (a : Alg F) (x : κ) (y : ι) : embL F F₂ a (Sum.inr x) (Sum.inl y) = 0 := rfl
@[simp] theorem embL_rr (a : Alg F) (x y : κ) : embL F F₂ a (Sum.inr x) (Sum.inr y) = 0 := rfl
@[simp] theorem embR_ll (b : Alg F₂) (x y : ι) : embR F F₂ b (Sum.inl x) (Sum.inl y) = 0 := rfl
@[simp] theorem embR_lr (b : Alg F₂) (x : ι) (y : κ) : embR F F₂ b (Sum.inl x) (Sum.inr y) = 0 := rfl
@[simp] theorem embR_rl (b : Alg F₂) (x : κ) (y : ι) : embR F F₂ b (Sum.inr x) (Sum.inl y) = 0 := rfl
@[simp] theorem embR_rr (b : Alg F₂) (x y : κ) : embR F F₂ b (Sum.inr x) (Sum.inr y) = b x y := rfl

@[simp] theorem zc {X Y Z : 𝒞} (f : Y ⟶ Z) : (0 : X ⟶ Y) ≫ f = 0 := Limits.zero_comp
@[simp] theorem cz {X Y Z : 𝒞} (f : X ⟶ Y) : f ≫ (0 : Y ⟶ Z) = 0 := Limits.comp_zero

theorem sum_zc {X Z : 𝒞} {Y : κ → 𝒞} (g : ∀ j, Y j ⟶ Z) : ∑ j, (0 : X ⟶ Y j) ≫ g j = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ Limits.zero_comp

theorem sum_cz {X Z : 𝒞} {Y : κ → 𝒞} (g : ∀ j, X ⟶ Y j) : ∑ j, g j ≫ (0 : Y j ⟶ Z) = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ Limits.comp_zero

theorem sum_zc' {X Z : 𝒞} {Y : ι → 𝒞} (g : ∀ j, Y j ⟶ Z) : ∑ j, (0 : X ⟶ Y j) ≫ g j = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ Limits.zero_comp

theorem sum_cz' {X Z : 𝒞} {Y : ι → 𝒞} (g : ∀ j, X ⟶ Y j) : ∑ j, g j ≫ (0 : Y j ⟶ Z) = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ Limits.comp_zero

theorem sum_type (c : ι ⊕ κ → 𝒞) {X Y : 𝒞} (f : ∀ w, X ⟶ c w) (g : ∀ w, c w ⟶ Y) :
    ∑ w, f w ≫ g w = ∑ x, f (Sum.inl x) ≫ g (Sum.inl x) + ∑ y, f (Sum.inr y) ≫ g (Sum.inr y) :=
  Fintype.sum_sum_type _

theorem embL_mul (a b : Alg F) : embL F F₂ (a * b) = embL F F₂ a * embL F F₂ b := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> rw [mul_apply, sum_type] <;> simp only [mul_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  all_goals first | rfl | exact (sum_zc _).symm | exact (sum_cz _).symm | exact (sum_zc' _).symm | exact (sum_cz' _).symm | exact sum_zc _ | exact sum_cz _ | exact sum_zc' _ | exact sum_cz' _ | skip

theorem embR_mul (a b : Alg F₂) : embR F F₂ (a * b) = embR F F₂ a * embR F F₂ b := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> rw [mul_apply, sum_type] <;> simp only [mul_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  all_goals first | rfl | exact (sum_zc _).symm | exact (sum_cz _).symm | exact (sum_zc' _).symm | exact (sum_cz' _).symm | exact sum_zc _ | exact sum_cz _ | exact sum_zc' _ | exact sum_cz' _ | skip

variable (F F₂) in
/-- `embL` as a linear map. -/
def embLₗ : Alg F →ₗ[k] Alg (FS F F₂) where
  toFun := embL F F₂
  map_add' a b := by
    apply CatAlg.ext; rintro (x | x) (y | y) <;> (try rfl) <;> simp only [add_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  map_smul' c a := by
    apply CatAlg.ext; rintro (x | x) (y | y) <;> (try rfl) <;> simp only [smul_apply, RingHom.id_apply, smul_zero, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]

variable (F F₂) in
/-- `embR` as a linear map. -/
def embRₗ : Alg F₂ →ₗ[k] Alg (FS F F₂) where
  toFun := embR F F₂
  map_add' a b := by
    apply CatAlg.ext; rintro (x | x) (y | y) <;> (try rfl) <;> simp only [add_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  map_smul' c a := by
    apply CatAlg.ext; rintro (x | x) (y | y) <;> (try rfl) <;> simp only [smul_apply, RingHom.id_apply, smul_zero, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]

theorem embL_resL (c : Alg (FS F F₂)) :
    embL F F₂ (resL F F₂ c) = embL F F₂ 1 * c * embL F F₂ 1 := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> rw [mul_apply, sum_type] <;> simp only [mul_apply, sum_type,
    resL, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add, Preadditive.sum_comp, Preadditive.comp_sum] <;> simp only [one_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  · have h1 : ∀ x₁, ∑ x₂, idTo (F := F) x x₂ ≫ c (Sum.inl x₂) (Sum.inl x₁) =
        c (Sum.inl x) (Sum.inl x₁) := fun x₁ ↦ sum_idTo_comp_alg (resL F F₂ c) x x₁
    refine (sum_comp_idTo_alg (resL F F₂ c) x y).symm.trans (Finset.sum_congr rfl fun x₁ _ ↦ ?_)
    exact congrArg (· ≫ idTo (F := F) x₁ y) (h1 x₁).symm
  all_goals first | rfl | exact (sum_zc _).symm | exact (sum_cz _).symm | exact (sum_zc' _).symm | exact (sum_cz' _).symm | exact sum_zc _ | exact sum_cz _ | exact sum_zc' _ | exact sum_cz' _

theorem embR_resR (c : Alg (FS F F₂)) :
    embR F F₂ (resR F F₂ c) = embR F F₂ 1 * c * embR F F₂ 1 := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> rw [mul_apply, sum_type] <;> simp only [mul_apply, sum_type,
    resR, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add, Preadditive.sum_comp, Preadditive.comp_sum] <;> simp only [one_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add]
  all_goals try first | rfl | exact (sum_zc _).symm | exact (sum_cz _).symm | exact (sum_zc' _).symm | exact (sum_cz' _).symm | exact sum_zc _ | exact sum_cz _ | exact sum_zc' _ | exact sum_cz' _
  have h1 : ∀ x₁, ∑ x₂, idTo (F := F₂) x x₂ ≫ c (Sum.inr x₂) (Sum.inr x₁) =
      c (Sum.inr x) (Sum.inr x₁) := fun x₁ ↦ sum_idTo_comp_alg (resR F F₂ c) x x₁
  refine (sum_comp_idTo_alg (resR F F₂ c) x y).symm.trans (Finset.sum_congr rfl fun x₁ _ ↦ ?_)
  exact congrArg (· ≫ idTo (F := F₂) x₁ y) (h1 x₁).symm

theorem embL_one_add_embR_one : embL F F₂ 1 + embR F F₂ 1 = 1 := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> simp only [add_apply, one_apply, embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add] <;>
    simp only [idTo, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, dite_false, add_zero, zero_add] <;>
    split_ifs <;> first | rfl | exact add_zero _ | exact zero_add _ | exact add_zero (0 : _) |
      (subst_vars; first | exact add_zero _ | exact zero_add _)

/-! ### Fullness of the original labels -/

section Full

variable {σ : κ → ι}

/-- The unit `F (σ j) → F (σ j)` from the copy `j` to the original label. -/
def uj (j : κ) : Alg (FS F (F ∘ σ))
  | Sum.inr a, Sum.inl i => if a = j then idTo (F := F) (σ a) i else 0
  | _, _ => 0

/-- The unit from the original label back to the copy `j`. -/
def vj (j : κ) : Alg (FS F (F ∘ σ))
  | Sum.inl i, Sum.inr b => if b = j then idTo (F := F) i (σ b) else 0
  | _, _ => 0

variable (σ) in
/-- The idempotent of the copy `j`. -/
def ejR (j : κ) : Alg (F ∘ σ) := fun a b ↦ if a = j ∧ b = j then idTo (F := F ∘ σ) a b else 0

theorem sum_ejR : ∑ j, ejR (F := F) σ j = 1 := by
  apply CatAlg.ext
  intro a b
  rw [CatAlg.sum_apply, Finset.sum_eq_single a]
  · by_cases h : a = b
    · subst h; simp [ejR, one_apply]
    · simp [ejR, h, one_apply, idTo_ne h]
  · intro j _ hj; simp [ejR, Ne.symm hj]
  · simp

theorem uj_mul_vj (j : κ) : uj (σ := σ) j * embL F (F ∘ σ) 1 * vj j =
    embR F (F ∘ σ) (ejR σ j) := by
  apply CatAlg.ext
  rintro (x | x) (y | y) <;> rw [mul_apply, sum_type] <;> simp only [mul_apply, sum_type,
    embL_ll, embL_lr, embL_rl, embL_rr, embR_ll, embR_lr, embR_rl, embR_rr, Limits.zero_comp, Limits.comp_zero, Finset.sum_const_zero, add_zero, zero_add, Preadditive.sum_comp, Preadditive.comp_sum, uj, vj, one_apply]
  case inr.inr =>
    change (∑ i, ∑ i', ((if x = j then idTo (F := F) (σ x) i' else 0) ≫ idTo (F := F) i' i) ≫
      (if y = j then idTo (F := F) i (σ y) else 0)) = ejR σ j x y
    by_cases hx : x = j <;> by_cases hy : y = j
    · simp only [if_pos hx, if_pos hy, ← Preadditive.sum_comp, sum_idTo_comp]
      change _ = if x = j ∧ y = j then idTo (F := F ∘ σ) x y else 0
      rw [if_pos (And.intro hx hy)]
      have hxy : x = y := hx.trans hy.symm
      subst hxy
      simp [idTo]
    all_goals
      change _ = if x = j ∧ y = j then idTo (F := F ∘ σ) x y else 0
      simp [hx, hy]
  all_goals first | rfl | exact (sum_zc _).symm | exact (sum_cz _).symm | exact (sum_zc' _).symm | exact (sum_cz' _).symm | exact sum_zc _ | exact sum_cz _ | exact sum_zc' _ | exact sum_cz' _

theorem sum_uj_mul_vj : ∑ j, uj (σ := σ) j * embL F (F ∘ σ) 1 * vj j = embR F (F ∘ σ) 1 := by
  simp only [uj_mul_vj]
  apply CatAlg.ext
  rintro (x | x) (y | y)
  case inr.inr =>
    rw [CatAlg.sum_apply]
    change ∑ j, ejR σ j x y = (1 : Alg (F ∘ σ)) x y
    rw [← CatAlg.sum_apply, sum_ejR]
  all_goals rw [CatAlg.sum_apply]; exact Finset.sum_const_zero

/-- **The original labels form a full idempotent.** -/
theorem full_embL (c : Alg (FS F (F ∘ σ))) :
    c ∈ Submodule.span k {x | ∃ p q, x = p * embL F (F ∘ σ) 1 * q} := by
  have h1 : c = c * embL F (F ∘ σ) 1 * 1 + ∑ j, (c * uj j) * embL F (F ∘ σ) 1 * vj j := by
    calc c = c * 1 := (mul_one c).symm
      _ = c * (embL F (F ∘ σ) 1 + ∑ j, uj j * embL F (F ∘ σ) 1 * vj j) := by
          rw [sum_uj_mul_vj, embL_one_add_embR_one]
      _ = _ := by
          rw [mul_add, Finset.mul_sum, mul_one]
          simp only [mul_assoc]
  rw [h1]
  refine add_mem (Submodule.subset_span ⟨c, 1, rfl⟩) (Submodule.sum_mem _ fun j _ ↦ ?_)
  exact Submodule.subset_span ⟨c * uj j, vj j, rfl⟩

end Full

/-! ### Representation-finiteness with repeated labels -/

section Repeat

variable (σ : κ → ι)

instance finiteDimensional_alg [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] :
    FiniteDimensional k (Alg F) :=
  inferInstanceAs (FiniteDimensional k (∀ x y : ι, F x ⟶ F y))

instance finiteDimensional_hom_FS [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] :
    ∀ x y : ι ⊕ κ, FiniteDimensional k (FS F (F ∘ σ) x ⟶ FS F (F ∘ σ) y)
  | Sum.inl _, Sum.inl _ => inferInstanceAs (FiniteDimensional k (F _ ⟶ F _))
  | Sum.inl _, Sum.inr _ => inferInstanceAs (FiniteDimensional k (F _ ⟶ F _))
  | Sum.inr _, Sum.inl _ => inferInstanceAs (FiniteDimensional k (F _ ⟶ F _))
  | Sum.inr _, Sum.inr _ => inferInstanceAs (FiniteDimensional k (F _ ⟶ F _))

instance finiteDimensional_hom_comp [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (x y : κ) :
    FiniteDimensional k ((F ∘ σ) x ⟶ (F ∘ σ) y) :=
  inferInstanceAs (FiniteDimensional k (F _ ⟶ F _))

/-- The opposite of an embedding of category algebras. -/
def opEmb {B C : Type w} [Ring B] [Algebra k B] [Ring C] [Algebra k C] (f : B →ₗ[k] C) :
    Bᵐᵒᵖ →ₗ[k] Cᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv k).toLinearMap ∘ₗ f ∘ₗ (MulOpposite.opLinearEquiv k).symm.toLinearMap

theorem opEmb_apply {B C : Type w} [Ring B] [Algebra k B] [Ring C] [Algebra k C] (f : B →ₗ[k] C)
    (b : Bᵐᵒᵖ) : opEmb f b = MulOpposite.op (f b.unop) := rfl

theorem isIdempotent_op_embL :
    IsIdempotentElem (MulOpposite.op (embL F (F ∘ σ) 1)) := by
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op, ← embL_mul, mul_one]

theorem isIdempotent_op_embR :
    IsIdempotentElem (MulOpposite.op (embR F (F ∘ σ) 1)) := by
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_op, ← embR_mul, mul_one]

/-- `Alg F` as a corner of the doubled algebra (opposite algebras). -/
def cornerL : (Alg F)ᵐᵒᵖ ≃ₐ[k] (isIdempotent_op_embL (F := F) σ).Corner :=
  cornerEquivOf (isIdempotent_op_embL σ) (opEmb (embLₗ F (F ∘ σ)))
    (fun a b ↦ by
      simp only [opEmb_apply, MulOpposite.unop_mul, embLₗ, LinearMap.coe_mk, AddHom.coe_mk,
        embL_mul, MulOpposite.op_mul])
    rfl
    (fun a b h ↦ by
      have := congrArg (fun c ↦ resL F (F ∘ σ) c.unop) h
      simp only [opEmb_apply, MulOpposite.unop_op, embLₗ, LinearMap.coe_mk, AddHom.coe_mk,
        resL_embL] at this
      exact MulOpposite.unop_injective this)
    (fun x hx ↦ ⟨MulOpposite.op (resL F (F ∘ σ) x.unop), by
      apply MulOpposite.unop_injective
      have h := congrArg MulOpposite.unop hx
      simp only [MulOpposite.unop_mul, MulOpposite.unop_op] at h
      simp only [opEmb_apply, MulOpposite.unop_op, embLₗ, LinearMap.coe_mk, AddHom.coe_mk,
        embL_resL]
      rw [mul_assoc]; exact h⟩)

/-- `Alg (F ∘ σ)` as a corner of the doubled algebra (opposite algebras). -/
def cornerR : (Alg (F ∘ σ))ᵐᵒᵖ ≃ₐ[k] (isIdempotent_op_embR (F := F) σ).Corner :=
  cornerEquivOf (isIdempotent_op_embR σ) (opEmb (embRₗ F (F ∘ σ)))
    (fun a b ↦ by
      simp only [opEmb_apply, MulOpposite.unop_mul, embRₗ, LinearMap.coe_mk, AddHom.coe_mk,
        embR_mul, MulOpposite.op_mul])
    rfl
    (fun a b h ↦ by
      have := congrArg (fun c ↦ resR F (F ∘ σ) c.unop) h
      simp only [opEmb_apply, MulOpposite.unop_op, embRₗ, LinearMap.coe_mk, AddHom.coe_mk,
        resR_embR] at this
      exact MulOpposite.unop_injective this)
    (fun x hx ↦ ⟨MulOpposite.op (resR F (F ∘ σ) x.unop), by
      apply MulOpposite.unop_injective
      have h := congrArg MulOpposite.unop hx
      simp only [MulOpposite.unop_mul, MulOpposite.unop_op] at h
      simp only [opEmb_apply, MulOpposite.unop_op, embRₗ, LinearMap.coe_mk, AddHom.coe_mk,
        embR_resR]
      rw [mul_assoc]; exact h⟩)

theorem full_op (a : (Alg (FS F (F ∘ σ)))ᵐᵒᵖ) :
    a ∈ Submodule.span k {x | ∃ p q, x = p * MulOpposite.op (embL F (F ∘ σ) 1) * q} := by
  have h := full_embL (k := k) (σ := σ) a.unop
  have h2 := Submodule.mem_map_of_mem (f := (MulOpposite.opLinearEquiv k).toLinearMap) h
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨p, q, rfl⟩, rfl⟩
  exact ⟨MulOpposite.op q, MulOpposite.op p, by simp [mul_assoc]⟩

/-- **Repeated labels** (Lemma 4.7, first step): if `Alg F` is
representation-finite, so is `Alg (F ∘ σ)`. -/
theorem isRepresentationFinite_comp [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
    (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ) : IsRepresentationFinite k (Alg (F ∘ σ))ᵐᵒᵖ := by
  have := corner_finite (k := k) (isIdempotent_op_embL (F := F) σ)
  have := corner_finite (k := k) (isIdempotent_op_embR (F := F) σ)
  have h1 := isRepresentationFinite_of_algEquiv (cornerL σ) hF
  have h2 := isRepresentationFinite_of_full (isIdempotent_op_embL (F := F) σ) (full_op σ) h1
  have h3 := corner_isRepresentationFinite_of (isIdempotent_op_embR (F := F) σ) h2
  exact isRepresentationFinite_of_algEquiv (cornerR σ).symm h3

end Repeat

end CatAlg

end MultiplicativeBasisDeformations
