import MultiplicativeBasisDeformations.Foundations.LiftedModules

/-!
# The automorphism `Φ` of the cover induced by a weight

Lemma 4.13 (`lem:scalar-object-values`, `scalar-normalization.tex`):
"Every scalar automorphism consequently fixes each `V_X̃` up to isomorphism.
Choose such isomorphisms, using the natural ones on projectives, in the
direction for which the following automorphism agrees with the given scalar
automorphism on the lifted projectives. Full faithfulness in Lemma 4.8 turns
them into an object-fixing automorphism `Φ` of `C̃`."

For a weight `d` on `L`, each lifted object `X̃` gets a `d`-scaled
automorphism of `V_X̃` (`ScAut`): the natural one `m ↦ d(z, x̃) m` on a lifted
projective `x̃` (`natAut`), and on the other objects the components of an
isomorphism `V_X̃^{σ_d} ≅ V_X̃` over a finite covering algebra containing the
support (`exists_twistAut`, from `weight_twist_iso`). Conjugating composition
with `f : X̃ → Ỹ` by these gives a natural family, hence by Lemma 4.8 a morphism
`Φ f` (`Φ`). `Φ` is linear, multiplicative, injective, and multiplies a
morphism `z₁ → z₂` of `L` by `d(z₁, z₂)` (`Φ_proj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

universe u v

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]

namespace MeshData

variable {L : LocalFamily (k := k) F} {D : MeshData F L} {Dg : HomGrading (k := k) F G}
  {T : Finset (D.PV × G)} {X : ι × G}

/-! ### Semilinear maps of `V_X̃` -/

theorem op_smul_smul (c : k) (b : covT D Dg T) (y : VX D Dg T X) :
    MulOpposite.op (c • b) • y = c • (MulOpposite.op b • y) := by
  apply ιV_injective
  change ρ D Dg T (MulOpposite.op (c • b)) • ιV y = c • ιV (MulOpposite.op b • y)
  rw [ιV_smul]
  change (c • ρ D Dg T (MulOpposite.op b)) • ιV y = c • (ρ D Dg T (MulOpposite.op b) • ιV y)
  rw [smul_assoc]

theorem scale_unitE (d : D.PV × G → D.PV × G → k) (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1)
    (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u) :
    scale (sT D T) d (unitE T q' q u hu) = d q'.1 q.1 • unitE T q' q u hu := by
  apply Subtype.ext; apply MulOpposite.unop_injective; apply CatAlg.ext; intro p r
  change d p.1 r.1 • (idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫
    idTo (F := D.F0 ∘ lab (sT D T)) q r) = d q'.1 q.1 • (idTo (F := D.F0 ∘ lab (sT D T)) p q' ≫ u ≫
    idTo (F := D.F0 ∘ lab (sT D T)) q r)
  by_cases hp : p = q'
  · subst hp
    by_cases hr : r = q
    · subst hr; rfl
    · rw [idTo_ne (Ne.symm hr), Limits.comp_zero, Limits.comp_zero, smul_zero, smul_zero]
  · rw [idTo_ne hp, Limits.zero_comp, smul_zero, smul_zero]

/-- A map semilinear for an automorphism, as a `k`-linear map. -/
def semiK (σ : covT D Dg T ≃ₐ[k] covT D Dg T) (f : VX D Dg T X →+ VX D Dg T X)
    (hf : ∀ (b : (covT D Dg T)ᵐᵒᵖ) y, f (b • y) = MulOpposite.op (σ b.unop) • f y) :
    VX D Dg T X →ₗ[k] VX D Dg T X where
  toFun := f
  map_add' := map_add f
  map_smul' c y := by
    rw [RingHom.id_apply, ← algebraMap_smul_VX, hf, ← algebraMap_smul_VX]
    congr 1
    apply MulOpposite.unop_injective
    exact σ.commutes c

theorem semiK_isScaled (σ : covT D Dg T ≃ₐ[k] covT D Dg T) (f : VX D Dg T X →+ VX D Dg T X)
    (hf : ∀ (b : (covT D Dg T)ᵐᵒᵖ) y, f (b • y) = MulOpposite.op (σ b.unop) • f y)
    (c : D.PV × G → D.PV × G → k)
    (hσ : ∀ (q' q : T) (u : F q'.1.1.1 ⟶ F q.1.1.1) (hu : Dg.IsHom ((q'.1.2)⁻¹ * q.1.2) u),
      σ (unitE T q' q u hu) = c q'.1 q.1 • unitE T q' q u hu) :
    IsScaled c (semiK σ f hf) := by
  intro q' q u hu y
  change f _ = _
  rw [hf, MulOpposite.unop_op, hσ, op_smul_smul]
  rfl

/-! ### Scaled automorphisms of `V_X̃` -/

variable (D Dg) in
/-- **A `d`-scaled automorphism of `V_X̃`.** -/
structure ScAut (d : D.PV × G → D.PV × G → k) (X : ι × G) where
  ψ : ScFam (D := D) (Dg := Dg) d X X
  ψ' : ScFam (D := D) (Dg := Dg) (fun z z' ↦ (d z z')⁻¹) X X
  left : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    ψ'.φ z (ψ.φ z m) = m
  right : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
    ψ.φ z (ψ'.φ z m) = m

variable {d : D.PV × G → D.PV × G → k}
  (hd : Thin.IsWeight (O := CovObj (grading0 D Dg)) Set.univ d)

include hd in
theorem weight_mul_of_ne {z' z x : D.PV × G} {u : F z'.1.1 ⟶ F z.1.1} {m : F z.1.1 ⟶ F x.1.1}
    (hu : u ∈ Dg.part (z'.2⁻¹ * z.2) z'.1.1 z.1.1) (hm : m ∈ Dg.part (z.2⁻¹ * x.2) z.1.1 x.1.1)
    (h : u ≫ m ≠ 0) : d z' x = d z' z * d z x :=
  hd.mul z' trivial z trivial x trivial (@id (@Quiver.Hom (CovObj (grading0 D Dg)) _ z' z) ⟨u, hu⟩)
    (@id (@Quiver.Hom (CovObj (grading0 D Dg)) _ z x) ⟨m, hm⟩) (cov_ne_zero.2 h)

include hd in
theorem weight_ne_of_ne {z x : D.PV × G} {m : F z.1.1 ⟶ F x.1.1}
    (hm : m ∈ Dg.part (z.2⁻¹ * x.2) z.1.1 x.1.1) (h : m ≠ 0) : d z x ≠ 0 :=
  hd.ne z trivial x trivial (@id (@Quiver.Hom (CovObj (grading0 D Dg)) _ z x) ⟨m, hm⟩)
    (cov_ne_zero.2 h)

omit [DecidableEq ι] [Fintype ι] in
/-- The natural scaled family on a lifted projective: `m ↦ c(z, x₀) m`. -/
def natFam (c : D.PV × G → D.PV × G → k) (x₀ : D.PV × G)
    (hc : ∀ (z' z : D.PV × G) (u : F z'.1.1 ⟶ F z.1.1) (m : F z.1.1 ⟶ F x₀.1.1),
      u ∈ Dg.part (z'.2⁻¹ * z.2) z'.1.1 z.1.1 → m ∈ Dg.part (z.2⁻¹ * x₀.2) z.1.1 x₀.1.1 →
      u ≫ m ≠ 0 → c z' x₀ = c z' z * c z x₀) :
    ScFam (D := D) (Dg := Dg) c (x₀.1.1, x₀.2) (x₀.1.1, x₀.2) where
  φ z := c z x₀ • LinearMap.id
  mem z m hm := Submodule.smul_mem _ _ hm
  nat z z' u m hu hm := by
    change c z' x₀ • (u ≫ m) = c z' z • (u ≫ (c z x₀ • m))
    rw [Linear.comp_smul, smul_smul]
    by_cases h : u ≫ m = 0
    · rw [h, smul_zero, smul_zero]
    · rw [hc z' z u m hu hm h]

include hd in
/-- **The natural automorphism of `V_x̃` for a lifted projective `x̃`.** -/
def natAut (x₀ : D.PV × G) : ScAut D Dg d (x₀.1.1, x₀.2) where
  ψ := natFam d x₀ fun z' z u m hu hm h ↦ weight_mul_of_ne hd hu hm h
  ψ' := natFam (fun z z' ↦ (d z z')⁻¹) x₀ fun z' z u m hu hm h ↦ by
    change (d z' x₀)⁻¹ = (d z' z)⁻¹ * (d z x₀)⁻¹
    rw [weight_mul_of_ne hd hu hm h, mul_inv]
  left z m hm := by
    change (d z x₀)⁻¹ • d z x₀ • m = m
    by_cases h : m = 0
    · rw [h, smul_zero, smul_zero]
    · rw [smul_smul, inv_mul_cancel₀ (weight_ne_of_ne hd hm h), one_smul]
  right z m hm := by
    change d z x₀ • (d z x₀)⁻¹ • m = m
    by_cases h : m = 0
    · rw [h, smul_zero, smul_zero]
    · rw [smul_smul, mul_inv_cancel₀ (weight_ne_of_ne hd hm h), one_smul]

/-! ### Twisted automorphisms -/

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

variable (D Dg) in
/-- A finite set of lifted projectives containing the support of `V_X̃`. -/
def suppT (X : ι × G) : Finset (D.PV × G) :=
  (Finset.univ ×ˢ Dg.degs).image fun pe : D.PV × G ↦ (pe.1, X.2 * pe.2⁻¹)

theorem supp_suppT (X : ι × G) : Supp Dg (suppT D Dg X) X := by
  intro z hz
  rw [eq_bot_iff]
  rintro f ⟨f', rfl⟩
  rw [Submodule.mem_bot]
  refine Dg.proj_eq_zero_of_not_mem (fun hdeg ↦ hz ?_) f'
  refine Finset.mem_image.2 ⟨(z.1, z.2⁻¹ * X.2), Finset.mem_product.2 ⟨Finset.mem_univ _, hdeg⟩, ?_⟩
  exact Prod.ext rfl (by simp)

include L in
theorem id_ne_zero (X : ι) : 𝟙 (F X) ≠ 0 := fun h ↦ L.id_not_mem X (h ▸ Submodule.zero_mem _)

instance (x y : D.PV) : FiniteDimensional k (D.F0 x ⟶ D.F0 y) := hfd x.1 y.1

include hd hfd in
/-- **A weight fixes `V_X̃` up to isomorphism**: a `d`-scaled automorphism from
an isomorphism `V_X̃^{σ_d} ≅ V_X̃` over a finite covering algebra. -/
theorem exists_twistAut [IsAlgClosed k] [Infinite k] (H : HeightData Dg)
    (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ) (X : ι × G) : Nonempty (ScAut D Dg d X) := by
  set T := suppT D Dg X
  have hX : Supp Dg T X := supp_suppT X
  have hM := VM_isFiniteIndecomposable H hX (id_ne_zero (L := L) X.1)
  have hd' : Thin.IsWeight (O := CovObj (grading0 D Dg)) (Set.range (sT D T)) d :=
    hd.mono (Set.subset_univ _)
  obtain ⟨e⟩ := weight_twist_iso hd' (H.comp Subtype.val Subtype.val_injective) hF (VM D Dg T X) hM
  set σ := scaleEquiv hd'
  -- the two semilinear maps
  let f : VX D Dg T X →+ VX D Dg T X := e.inv.hom.toAddMonoidHom
  let g : VX D Dg T X →+ VX D Dg T X := e.hom.hom.toAddMonoidHom
  have hf : ∀ (b : (covT D Dg T)ᵐᵒᵖ) y, f (b • y) = MulOpposite.op (σ b.unop) • f y :=
    fun b y ↦ map_smul e.inv.hom b y
  have hg : ∀ (b : (covT D Dg T)ᵐᵒᵖ) y, g (b • y) = MulOpposite.op (σ.symm b.unop) • g y := by
    intro b y
    have := LinearMap.map_smul e.hom.hom (MulOpposite.op (σ.symm b.unop)) y
    change g (MulOpposite.op (σ (σ.symm b.unop)) • y) =
      MulOpposite.op (σ.symm b.unop) • g y at this
    rwa [AlgEquiv.apply_symm_apply] at this
  have hgf : ∀ y, g (f y) = y := fun y ↦ by
    change (e.inv ≫ e.hom).hom y = y
    rw [Iso.inv_hom_id]; rfl
  have hfg : ∀ y, f (g y) = y := fun y ↦ by
    change (e.hom ≫ e.inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hsf := semiK_isScaled σ f hf d fun q' q u hu ↦ scale_unitE d q' q u hu
  have hsg := semiK_isScaled σ.symm g hg (fun z z' ↦ (d z z')⁻¹) fun q' q u hu ↦
    scale_unitE (fun z z' ↦ (d z z')⁻¹) q' q u hu
  have key : ∀ (f₁ f₂ : VX D Dg T X →ₗ[k] VX D Dg T X) (c₂ : D.PV × G → D.PV × G → k),
      IsScaled c₂ f₂ → (∀ y, f₂ (f₁ y) = y) → ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1),
      m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 → famOf T f₂ z (famOf T f₁ z m) = m := by
    intro f₁ f₂ c₂ h₂ hinv z m hm
    by_cases hz : z ∈ T
    · rw [famOf_apply f₁ hz hm, famOf_apply f₂ hz (Submodule.coe_mem _)]
      have := h₂.apply (f₁ (singleV (T := T) ⟨z, hz⟩ ⟨m, hm⟩)) ⟨z, hz⟩
      rw [hinv, singleV_same] at this
      exact congrArg Subtype.val this.symm
    · rw [eq_zero_of_supp hX hz hm, map_zero, map_zero]
  exact ⟨{ ψ := scFamOf hX hX hsf
           ψ' := scFamOf hX hX hsg
           left := key _ _ _ hsg hgf
           right := key _ _ d hsf hfg }⟩

/-! ### The automorphism `Φ` -/

variable {X Y Z : ι × G}

include hd in
/-- Conjugating composition with `f` by scaled automorphisms gives a natural
family. -/
def compFam (A : ScAut D Dg d X) (B : ScAut D Dg d Y) (f : F X.1 ⟶ F Y.1)
    (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) : NatFam D Dg X Y where
  φ z := B.ψ.φ z ∘ₗ Linear.rightComp k _ f ∘ₗ A.ψ'.φ z
  mem z m hm := by
    apply B.ψ.mem
    have h1 := (HomGrading.mem_part_iff (D := Dg)).1 (A.ψ'.mem z m hm)
    have := Dg.isHom_comp h1 ((HomGrading.mem_part_iff (D := Dg)).1 hf)
    rw [HomGrading.mem_part_iff]
    rwa [show z.2⁻¹ * X.2 * (X.2⁻¹ * Y.2) = z.2⁻¹ * Y.2 by group] at this
  nat z z' u m hu hm := by
    simp only [LinearMap.coe_comp, Function.comp_apply, Linear.rightComp_apply]
    by_cases hu0 : u = 0
    · rw [hu0, Limits.zero_comp, map_zero, Limits.zero_comp, map_zero, Limits.zero_comp]
    have hn := A.ψ'.mem z m hm
    have hnf : A.ψ'.φ z m ≫ f ∈ Dg.part (z.2⁻¹ * Y.2) z.1.1 Y.1 := by
      have := Dg.isHom_comp ((HomGrading.mem_part_iff (D := Dg)).1 hn)
        ((HomGrading.mem_part_iff (D := Dg)).1 hf)
      rw [HomGrading.mem_part_iff]
      rwa [show z.2⁻¹ * X.2 * (X.2⁻¹ * Y.2) = z.2⁻¹ * Y.2 by group] at this
    rw [A.ψ'.nat z z' u m hu hm, Linear.smul_comp, Category.assoc, map_smul,
      B.ψ.nat z z' u _ hu hnf, smul_smul, inv_mul_cancel₀ (weight_ne_of_ne hd hu hu0), one_smul]

include hd hfd in
theorem compFam_exists (A : ScAut D Dg d X) (B : ScAut D Dg d Y) (f : F X.1 ⟶ F Y.1)
    (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) :
    ∃ g : F X.1 ⟶ F Y.1, Dg.IsHom (X.2⁻¹ * Y.2) g ∧
      ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
        B.ψ.φ z (A.ψ'.φ z m ≫ f) = m ≫ g :=
  (compFam hd A B f hf).exists_hom

variable [IsAlgClosed k] [Infinite k] (H : HeightData Dg)
  (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

include hd H hF in
/-- **The chosen automorphisms**: natural on the lifted projectives. -/
def aut (X : ι × G) : ScAut D Dg d X :=
  if hX : D.proj X.1 then natAut hd (⟨X.1, hX⟩, X.2)
  else Classical.choice (exists_twistAut hd H hF X)

theorem aut_proj (x : D.PV × G) : aut hd H hF (x.1.1, x.2) = natAut hd x := by
  rw [aut, dif_pos x.1.2]

include hd H hF in
/-- **The automorphism `Φ` of `C̃`** on a morphism `f : X̃ → Ỹ`. -/
def Φ (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) : F X.1 ⟶ F Y.1 :=
  Classical.choose (compFam_exists hd (aut hd H hF X) (aut hd H hF Y) f hf)

theorem Φ_isHom (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Dg.IsHom (X.2⁻¹ * Y.2) (Φ hd H hF f hf) :=
  (Classical.choose_spec (compFam_exists hd (aut hd H hF X) (aut hd H hF Y) f hf)).1

theorem Φ_mem (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd H hF f hf ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1 :=
  (HomGrading.mem_part_iff (D := Dg)).2 (Φ_isHom hd H hF f hf)

theorem Φ_spec (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) (z : D.PV × G)
    (m : F z.1.1 ⟶ F X.1) (hm : m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1) :
    (aut hd H hF Y).ψ.φ z ((aut hd H hF X).ψ'.φ z m ≫ f) = m ≫ Φ hd H hF f hf :=
  (Classical.choose_spec (compFam_exists hd (aut hd H hF X) (aut hd H hF Y) f hf)).2 z m hm

include hfd in
/-- Uniqueness: `Φ f` is the only morphism with the defining property. -/
theorem Φ_unique (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1)
    (g : F X.1 ⟶ F Y.1)
    (hg : ∀ (z : D.PV × G) (m : F z.1.1 ⟶ F X.1), m ∈ Dg.part (z.2⁻¹ * X.2) z.1.1 X.1 →
      (aut hd H hF Y).ψ.φ z ((aut hd H hF X).ψ'.φ z m ≫ f) = m ≫ g) :
    Φ hd H hF f hf = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_lifted (D := D) (Dg := Dg) _ fun z m hm ↦ ?_
  rw [Preadditive.comp_sub, ← Φ_spec hd H hF f hf z m hm, ← hg z m hm, sub_self]

omit hfd in
theorem comp_mem {x y z : ι} {a b c : G} {f : F x ⟶ F y} {g : F y ⟶ F z}
    (hf : f ∈ Dg.part (a⁻¹ * b) x y) (hg : g ∈ Dg.part (b⁻¹ * c) y z) :
    f ≫ g ∈ Dg.part (a⁻¹ * c) x z := by
  rw [HomGrading.mem_part_iff] at hf hg ⊢
  have := Dg.isHom_comp hf hg
  rwa [show a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c by group] at this

include hfd in
/-- **`Φ` is multiplicative.** -/
theorem Φ_comp (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1)
    (g : F Y.1 ⟶ F Z.1) (hg : g ∈ Dg.part (Y.2⁻¹ * Z.2) Y.1 Z.1) :
    Φ hd H hF (f ≫ g) (comp_mem hf hg) = Φ hd H hF f hf ≫ Φ hd H hF g hg := by
  refine Φ_unique hd H hF _ _ _ fun z m hm ↦ ?_
  have hn := comp_mem ((aut hd H hF X).ψ'.mem z m hm) hf
  rw [← Category.assoc m (Φ hd H hF f hf), ← Φ_spec hd H hF f hf z m hm,
    ← Φ_spec hd H hF g hg z _ ((aut hd H hF Y).ψ.mem z _ hn), (aut hd H hF Y).left z _ hn,
    Category.assoc]

include hfd in
theorem Φ_id (h : 𝟙 (F X.1) ∈ Dg.part (X.2⁻¹ * X.2) X.1 X.1) :
    Φ hd H hF (𝟙 (F X.1)) h = 𝟙 (F X.1) := by
  refine Φ_unique hd H hF _ _ _ fun z m hm ↦ ?_
  rw [Category.comp_id, Category.comp_id, (aut hd H hF X).right z m hm]

include hfd in
theorem Φ_add (f f' : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1)
    (hf' : f' ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd H hF (f + f') (add_mem hf hf') = Φ hd H hF f hf + Φ hd H hF f' hf' := by
  refine Φ_unique hd H hF _ _ _ fun z m hm ↦ ?_
  rw [Preadditive.comp_add, map_add, Φ_spec hd H hF f hf z m hm,
    Φ_spec hd H hF f' hf' z m hm, Preadditive.comp_add]

include hfd in
theorem Φ_smul (c : k) (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1) :
    Φ hd H hF (c • f) (Submodule.smul_mem _ c hf) = c • Φ hd H hF f hf := by
  refine Φ_unique hd H hF _ _ _ fun z m hm ↦ ?_
  rw [Linear.comp_smul, map_smul, Φ_spec hd H hF f hf z m hm, Linear.comp_smul]

include hfd in
/-- **`Φ` is injective.** -/
theorem eq_zero_of_Φ (f : F X.1 ⟶ F Y.1) (hf : f ∈ Dg.part (X.2⁻¹ * Y.2) X.1 Y.1)
    (h : Φ hd H hF f hf = 0) : f = 0 := by
  refine eq_zero_of_lifted (D := D) (Dg := Dg) f fun z m hm ↦ ?_
  have hm' := (aut hd H hF X).ψ.mem z m hm
  have h1 := Φ_spec hd H hF f hf z _ hm'
  rw [h, Limits.comp_zero, (aut hd H hF X).left z m hm] at h1
  have h2 := congrArg ((aut hd H hF Y).ψ'.φ z) h1
  rw [(aut hd H hF Y).left z _ (comp_mem hm hf), map_zero] at h2
  exact h2

include hfd in
/-- **`Φ` agrees with the scalar automorphism on `L`**: it multiplies a morphism
`x̃₁ → x̃₂` of lifted projectives by `d(x̃₁, x̃₂)`. -/
theorem Φ_proj (x₁ x₂ : D.PV × G) (f : F x₁.1.1 ⟶ F x₂.1.1)
    (hf : f ∈ Dg.part (x₁.2⁻¹ * x₂.2) x₁.1.1 x₂.1.1) :
    Φ (X := (x₁.1.1, x₁.2)) (Y := (x₂.1.1, x₂.2)) hd H hF f hf = d x₁ x₂ • f := by
  refine Φ_unique hd H hF _ _ _ fun z m hm ↦ ?_
  rw [aut_proj, aut_proj]
  change d z x₂ • (((d z x₁)⁻¹ • m) ≫ f) = m ≫ (d x₁ x₂ • f)
  rw [Linear.smul_comp, smul_smul, Linear.comp_smul]
  by_cases h : m ≫ f = 0
  · rw [h, smul_zero, smul_zero]
  · have hm0 : m ≠ 0 := fun h0 ↦ h (by rw [h0, Limits.zero_comp])
    rw [weight_mul_of_ne hd hm hf h, mul_comm (d z x₁), mul_assoc,
      mul_inv_cancel₀ (weight_ne_of_ne hd hm hm0), mul_one]

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
