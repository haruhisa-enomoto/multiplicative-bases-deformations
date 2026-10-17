import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners

/-!
# Lemma 8.9: representation transfer along a functor with a bimodule retraction

`local-ray-geometry.tex` (`lem:representation-transfer`): "Let `F : S → B` be a
functor between finite categories. Let `B_F` be the category with the objects of `S` and
morphisms `B_F(x, y) = B(Fx, Fy)`, so that `F` gives a functor `S → B_F`, which we assume
injective on morphisms. Suppose that there is an `S`-bimodule map `π : B_F → S` retracting
this inclusion. If `B` is representation-finite, then so is `S`."

Finite `k`-linear categories are given by finite families of objects (`CatAlg.Alg`): `S` by
`FS : ι → 𝒮` and `B` by `FB : κ → ℬ`; the functor is a `k`-linear functor `G : 𝒮 ⥤ ℬ` with
`G (FS i) = FB (σ i)`. `B_F` is the family `G ∘ FS = FB ∘ σ`, representation-finite by
repeated labels (`isRepresentationFinite_comp`: an idempotent corner of a Morita equivalent
algebra); `G` embeds `S` into `B_F` (`funcAlgHom`), and Lemma 4.6
(`splitRepresentationTransfer_of`) applies to the retraction (`representationTransfer`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v v' w

namespace CatAlg

variable {k : Type u} [Field k] {𝒮 : Type v} [Category.{w} 𝒮] [Preadditive 𝒮] [Linear k 𝒮]
  {ℬ : Type v'} [Category.{w} ℬ] [Preadditive ℬ] [Linear k ℬ]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (FS : ι → 𝒮) (G : 𝒮 ⥤ ℬ) [G.Additive] [G.Linear k]

/-- `G` on category algebras: `(a_{xy}) ↦ (G a_{xy})`. -/
def funcAlg (a : Alg FS) : Alg (fun i ↦ G.obj (FS i)) := fun x y ↦ G.map (a x y)

theorem funcAlg_apply (a : Alg FS) (x y : ι) : funcAlg FS G a x y = G.map (a x y) := rfl

theorem funcMap_idTo (x y : ι) :
    G.map (idTo (F := FS) x y) = idTo (F := fun i ↦ G.obj (FS i)) x y := by
  by_cases h : x = y
  · subst h; simp
  · rw [idTo_ne h, idTo_ne h, G.map_zero]

/-- **`G` as an algebra map** `kS → kB_F`. -/
def funcAlgHom : Alg FS →ₐ[k] Alg (fun i ↦ G.obj (FS i)) where
  toFun := funcAlg FS G
  map_one' := by ext x y; rw [funcAlg_apply, one_apply, one_apply, funcMap_idTo]
  map_mul' a b := by
    ext x z
    simp only [funcAlg_apply, mul_apply, G.map_sum, G.map_comp]
  map_zero' := by ext x y; simp [funcAlg_apply]
  map_add' a b := by ext x y; simp [funcAlg_apply]
  commutes' t := by
    ext x y
    rw [funcAlg_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change G.map (t • (1 : Alg FS) x y) = t • (1 : Alg (fun i ↦ G.obj (FS i))) x y
    rw [G.map_smul, one_apply, one_apply, funcMap_idTo]

theorem funcAlgHom_injective (hinj : ∀ X Y : 𝒮, Function.Injective (G.map : (X ⟶ Y) → _)) :
    Function.Injective (funcAlgHom (k := k) FS G) := by
  intro a b h
  ext x y
  exact hinj _ _ (congrFun (congrFun h x) y)

variable (π : ∀ x y : ι, (G.obj (FS x) ⟶ G.obj (FS y)) →ₗ[k] (FS x ⟶ FS y))

/-- The retraction on category algebras. -/
def funcRet : Alg (fun i ↦ G.obj (FS i)) →ₗ[k] Alg FS where
  toFun b x y := π x y (b x y)
  map_add' b b' := by funext x y; exact (π x y).map_add _ _
  map_smul' t b := by funext x y; exact (π x y).map_smul _ _

theorem funcRet_mul_left
    (hl : ∀ x y z (f : FS x ⟶ FS y) (b : G.obj (FS y) ⟶ G.obj (FS z)),
      π x z (G.map f ≫ b) = f ≫ π y z b) (a : Alg FS) (b : Alg (fun i ↦ G.obj (FS i))) :
    funcRet FS G π (funcAlgHom (k := k) FS G a * b) = a * funcRet FS G π b := by
  ext x z
  change π x z (∑ y, G.map (a x y) ≫ b y z) = ∑ y, a x y ≫ π y z (b y z)
  rw [map_sum]
  exact Finset.sum_congr rfl fun y _ ↦ hl _ _ _ _ _

theorem funcRet_mul_right
    (hr : ∀ x y z (b : G.obj (FS x) ⟶ G.obj (FS y)) (f : FS y ⟶ FS z),
      π x z (b ≫ G.map f) = π x y b ≫ f) (b : Alg (fun i ↦ G.obj (FS i))) (a : Alg FS) :
    funcRet FS G π (b * funcAlgHom (k := k) FS G a) = funcRet FS G π b * a := by
  ext x z
  change π x z (∑ y, b x y ≫ G.map (a y z)) = ∑ y, π x y (b x y) ≫ a y z
  rw [map_sum]
  exact Finset.sum_congr rfl fun y _ ↦ hr _ _ _ _ _

/-- **Lemma 8.9** (`lem:representation-transfer`): for a `k`-linear functor `G : 𝒮 ⥤ ℬ`
carrying the objects `FS i` of the finite category `S` to objects `FB (σ i)` of the finite
category `B`, injective on morphisms, with an `S`-bimodule retraction `π : B_F → S`: if `B` is
representation-finite, so is `S`. -/
theorem representationTransfer (FB : κ → ℬ) [∀ x y : ι, FiniteDimensional k (FS x ⟶ FS y)]
    [∀ x y : κ, FiniteDimensional k (FB x ⟶ FB y)] (σ : ι → κ) (hσ : ∀ i, G.obj (FS i) = FB (σ i))
    (hinj : ∀ X Y : 𝒮, Function.Injective (G.map : (X ⟶ Y) → _))
    (hret : ∀ x y (f : FS x ⟶ FS y), π x y (G.map f) = f)
    (hl : ∀ x y z (f : FS x ⟶ FS y) (b : G.obj (FS y) ⟶ G.obj (FS z)),
      π x z (G.map f ≫ b) = f ≫ π y z b)
    (hr : ∀ x y z (b : G.obj (FS x) ⟶ G.obj (FS y)) (f : FS y ⟶ FS z),
      π x z (b ≫ G.map f) = π x y b ≫ f)
    (hB : IsRepresentationFinite k (Alg FB)ᵐᵒᵖ) : IsRepresentationFinite k (Alg FS)ᵐᵒᵖ := by
  classical
  -- `B_F` is representation-finite
  have hfam : (fun i ↦ G.obj (FS i)) = FB ∘ σ := funext hσ
  have hBF : IsRepresentationFinite k (Alg (fun i ↦ G.obj (FS i)))ᵐᵒᵖ := by
    rw [hfam]; exact isRepresentationFinite_comp (F := FB) σ hB
  have : ∀ x y : ι, FiniteDimensional k (G.obj (FS x) ⟶ G.obj (FS y)) := fun x y ↦ by
    rw [hσ x, hσ y]; infer_instance
  -- the split transfer on opposite algebras
  set Φ : (Alg FS)ᵐᵒᵖ →ₐ[k] (Alg (fun i ↦ G.obj (FS i)))ᵐᵒᵖ := AlgHom.op (funcAlgHom FS G)
  have hΦ : Function.Injective Φ := fun a b h ↦
    MulOpposite.unop_injective (funcAlgHom_injective (k := k) FS G hinj (congrArg MulOpposite.unop h))
  set e := AlgEquiv.ofInjective Φ hΦ
  let q : Φ.range →ₐ[k] (Alg FS)ᵐᵒᵖ := e.symm.toAlgHom
  let πo : (Alg (fun i ↦ G.obj (FS i)))ᵐᵒᵖ →ₗ[k] (Alg FS)ᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv k).toLinearMap ∘ₗ funcRet FS G π ∘ₗ
      (MulOpposite.opLinearEquiv k).symm.toLinearMap
  have hπo : ∀ b, πo b = MulOpposite.op (funcRet FS G π b.unop) := fun _ ↦ rfl
  have hc : ∀ c : Φ.range, (c : (Alg (fun i ↦ G.obj (FS i)))ᵐᵒᵖ) = Φ (q c) := fun c ↦ by
    have := e.apply_symm_apply c
    exact (congrArg Subtype.val this).symm
  have hretA : ∀ a : Alg FS, funcRet FS G π (funcAlgHom (k := k) FS G a) = a := fun a ↦ by
    ext x y; exact hret x y (a x y)
  refine splitRepresentationTransfer_of (C := Φ.range) (q := q) πo ?_ ?_ ?_ hBF
  · intro c c' b
    rw [hc c, hc c', hπo, hπo]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Φ, AlgHom.op_apply_apply,
      Function.comp_apply]
    rw [funcRet_mul_left FS G π hl, funcRet_mul_right FS G π hr]
  · intro a
    exact ⟨e a, by simp [q]⟩
  · intro c
    rw [hc c, hπo]
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, Φ, AlgHom.op_apply_apply, Function.comp_apply]
    rw [hretA]

end CatAlg

end MultiplicativeBasisDeformations
