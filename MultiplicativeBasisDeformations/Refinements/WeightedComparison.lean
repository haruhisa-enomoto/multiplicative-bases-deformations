import MultiplicativeBasisDeformations.Refinements.FullHochschild
import MultiplicativeBasisDeformations.Foundations.WeightLift

/-!
# Proposition 12.5: weights, and `I₀ = I`

`deformation-refinements.tex:267–283`: "Giving `ε` internal degree `−q` and the opposite weight
makes the corner deformation homogeneous of the required degree and weight. […] In
characteristic two, each residual line `k[p_i]` of Proposition 6.1 has weight `χ_i` and is now
in the image, so `HH²(A₀)_{χ_i} ≠ 0` and `I₀ = I`."

For a mesh weight `W`, the weight-`χ` part of a category cocycle (`CatCocycle.wproj`) is again a
cocycle of the same internal degree; its mesh value is the relative weight-`χ` part of the
original one, and its corner `μ` has character `χ` (`catMu_hasChar`). Hence every correction
tuple of relative weight `χ` is `Ψ[μ]` for a cocycle `μ` of character `χ`
(`Ψc_surjective_char`), and a row with nonzero cokernel class gives a cocycle of the row's
character which is not a coboundary (`exists_not_cobdry`): `I ⊆ I₀`. The inclusion `I₀ ⊆ I` is
Proposition 7.6 (`Ψc_mem_rowSpan_char`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  {Q : TranslationQuiver V} {c : MeshCoefficients k Q}
  {M : Type} [AddCommGroup M] (W : MeshWt Q M)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

namespace CatCocycle

variable {q : ℕ} (Φ : CatCocycle c q)

/-- The weight-`χ` part of a category cocycle. -/
def wφ (χ : M) {X Y Z : V} (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) : obj c X ⟶ obj c Z :=
  ∑ α ∈ wSupp W hfin, ∑ β ∈ wSupp W hfin,
    wπ c W (α + β + χ) X Z (Φ.φ (wπ c W α X Y f) (wπ c W β Y Z g))

theorem wφ_hom (χ : M) {X Y Z : V} {α β : M} {f : obj c X ⟶ obj c Y} {g : obj c Y ⟶ obj c Z}
    (hf : f ∈ wP c W α X Y) (hg : g ∈ wP c W β Y Z) :
    Φ.wφ W hfin χ f g = wπ c W (α + β + χ) X Z (Φ.φ f g) := by
  by_cases ha : α ∈ wSupp W hfin
  · by_cases hb : β ∈ wSupp W hfin
    · rw [wφ, Finset.sum_eq_single α, Finset.sum_eq_single β]
      · rw [wπ_of_mem W hf, if_pos rfl, wπ_of_mem W hg, if_pos rfl]
      · intro e _ he
        rw [wπ_of_mem W hg, if_neg (Ne.symm he), Φ.zero_right, map_zero]
      · intro h; exact absurd hb h
      · intro d _ hd
        refine Finset.sum_eq_zero fun e _ ↦ ?_
        rw [wπ_of_mem W hf, if_neg (Ne.symm hd), Φ.zero_left, map_zero]
      · intro h; exact absurd ha h
    · have : g = 0 := by rw [wP_eq_bot W hfin hb, Submodule.mem_bot] at hg; exact hg
      subst this
      simp [wφ, Φ.zero_right]
  · have : f = 0 := by rw [wP_eq_bot W hfin ha, Submodule.mem_bot] at hf; exact hf
    subst this
    simp [wφ, Φ.zero_left]

theorem wφ_add_left (χ : M) {X Y Z : V} (f f' : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    Φ.wφ W hfin χ (f + f') g = Φ.wφ W hfin χ f g + Φ.wφ W hfin χ f' g := by
  simp only [wφ, map_add, Φ.add_left, ← Finset.sum_add_distrib]

theorem wφ_add_right (χ : M) {X Y Z : V} (f : obj c X ⟶ obj c Y) (g g' : obj c Y ⟶ obj c Z) :
    Φ.wφ W hfin χ f (g + g') = Φ.wφ W hfin χ f g + Φ.wφ W hfin χ f g' := by
  simp only [wφ, map_add, Φ.add_right, ← Finset.sum_add_distrib]

theorem wφ_smul_left (χ : M) {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y) (g : obj c Y ⟶ obj c Z) :
    Φ.wφ W hfin χ (t • f) g = t • Φ.wφ W hfin χ f g := by
  simp only [wφ, map_smul, Φ.smul_left, Finset.smul_sum]

theorem wφ_smul_right (χ : M) {X Y Z : V} (t : k) (f : obj c X ⟶ obj c Y)
    (g : obj c Y ⟶ obj c Z) : Φ.wφ W hfin χ f (t • g) = t • Φ.wφ W hfin χ f g := by
  simp only [wφ, map_smul, Φ.smul_right, Finset.smul_sum]

include hfin in
theorem eq_zero_of_whom {X Y : V} {N : Type*} [AddCommGroup N] (F : (obj c X ⟶ obj c Y) →+ N)
    (h : ∀ α (f : obj c X ⟶ obj c Y), f ∈ wP c W α X Y → F f = 0) (f : obj c X ⟶ obj c Y) :
    F f = 0 := by
  rw [eq_sum_wπ W hfin f, map_sum]
  exact Finset.sum_eq_zero fun α _ ↦ h α _ (wπ_mem W α f)

/-- The cocycle expression of the weight part. -/
def wExpr (χ : M) {V₀ X Y Z : V} (f : obj c V₀ ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) : obj c V₀ ⟶ obj c Z :=
  f ≫ Φ.wφ W hfin χ g h - Φ.wφ W hfin χ (f ≫ g) h + Φ.wφ W hfin χ f (g ≫ h) -
    Φ.wφ W hfin χ f g ≫ h

theorem wExpr_hom (χ : M) {V₀ X Y Z : V} {a b d : M} {f : obj c V₀ ⟶ obj c X}
    {g : obj c X ⟶ obj c Y} {h : obj c Y ⟶ obj c Z} (hf : f ∈ wP c W a V₀ X)
    (hg : g ∈ wP c W b X Y) (hh : h ∈ wP c W d Y Z) : Φ.wExpr W hfin χ f g h = 0 := by
  rw [wExpr, Φ.wφ_hom W hfin χ hg hh, Φ.wφ_hom W hfin χ (comp_mem_wP W hf hg) hh,
    Φ.wφ_hom W hfin χ hf (comp_mem_wP W hg hh), Φ.wφ_hom W hfin χ hf hg,
    ← wπ_comp_left W hfin hf, ← wπ_comp_right W hfin hh]
  rw [show a + (b + d + χ) = a + b + d + χ by abel, show a + (b + d) + χ = a + b + d + χ by abel,
    show a + b + χ + d = a + b + d + χ by abel, ← map_sub, ← map_add, ← map_sub, Φ.cocycle,
    map_zero]

theorem wExpr_eq_zero (χ : M) {V₀ X Y Z : V} (f : obj c V₀ ⟶ obj c X) (g : obj c X ⟶ obj c Y)
    (h : obj c Y ⟶ obj c Z) : Φ.wExpr W hfin χ f g h = 0 := by
  have h1 : ∀ (g : obj c X ⟶ obj c Y) (h : obj c Y ⟶ obj c Z) {b d : M},
      g ∈ wP c W b X Y → h ∈ wP c W d Y Z →
        ∀ f : obj c V₀ ⟶ obj c X, Φ.wExpr W hfin χ f g h = 0 := by
    intro g h b d hg hh
    refine eq_zero_of_whom W hfin
      (AddMonoidHom.mk' (fun f ↦ Φ.wExpr W hfin χ f g h) fun f f' ↦ ?_)
      (fun a f hf ↦ Φ.wExpr_hom W hfin χ hf hg hh)
    simp only [wExpr, Preadditive.add_comp, Φ.wφ_add_left, Preadditive.comp_add]; abel
  have h2 : ∀ (h : obj c Y ⟶ obj c Z) {d : M}, h ∈ wP c W d Y Z →
      ∀ (f : obj c V₀ ⟶ obj c X) (g : obj c X ⟶ obj c Y), Φ.wExpr W hfin χ f g h = 0 := by
    intro h d hh f
    refine eq_zero_of_whom W hfin
      (AddMonoidHom.mk' (fun g ↦ Φ.wExpr W hfin χ f g h) fun g g' ↦ ?_)
      (fun b g hg ↦ h1 g h hg hh f)
    simp only [wExpr, Preadditive.add_comp, Preadditive.comp_add, Φ.wφ_add_left,
      Φ.wφ_add_right]; abel
  refine eq_zero_of_whom W hfin
    (AddMonoidHom.mk' (fun h ↦ Φ.wExpr W hfin χ f g h) fun h h' ↦ ?_)
    (fun d h hh ↦ h2 h hh f g) h
  simp only [wExpr, Preadditive.comp_add, Φ.wφ_add_right]; abel

/-- **The weight-`χ` part of a category cocycle**, of the same internal degree. -/
def wproj (χ : M) : CatCocycle c q where
  φ := Φ.wφ W hfin χ
  add_left := Φ.wφ_add_left W hfin χ
  add_right := Φ.wφ_add_right W hfin χ
  smul_left := Φ.wφ_smul_left W hfin χ
  smul_right := Φ.wφ_smul_right W hfin χ
  cocycle := Φ.wExpr_eq_zero W hfin χ
  deg {X Y Z d e f g} hf hg := Submodule.sum_mem _ fun α _ ↦ Submodule.sum_mem _ fun β _ ↦
    wπ_mem_degreePart W _ (Φ.deg (wπ_mem_degreePart W α hf) (wπ_mem_degreePart W β hg))

theorem meshVal_wproj (χ : M) (x : Q.nonprojective) :
    (Φ.wproj W hfin χ).meshVal x = wπ c W (W.ν x + χ) _ _ (Φ.meshVal x) := by
  change ∑ a : Σ y : V, y ⟶ x.1, ((c x a.1 a.2 : kˣ) : k) •
      Φ.wφ W hfin χ (arrowMor c (Q.mate x a.1 a.2)) (arrowMor c a.2) = _
  rw [meshVal, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Φ.wφ_hom W hfin χ (arrowMor_mem_wP W _) (arrowMor_mem_wP W _), W.mesh x a, map_smul]

/-- The zero cocycle. -/
def zero : CatCocycle c q where
  φ _ _ := 0
  add_left _ _ _ := (add_zero 0).symm
  add_right _ _ _ := (add_zero 0).symm
  smul_left _ _ _ := (smul_zero _).symm
  smul_right _ _ _ := (smul_zero _).symm
  cocycle _ _ _ := by simp
  deg _ _ := zero_mem _

theorem meshVal_zero : (zero (c := c) (q := q)).meshVal = 0 := by
  funext x; simp [meshVal, zero]

end CatCocycle

variable {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

theorem catMu_hasChar {q : ℕ} (Φ : CatCocycle c q) (χ : M) :
    HasChar W hfin D χ (catMu D (Φ.wproj W hfin χ)) := by
  intro α β a b ha hb
  rw [grA0_isHom] at ha hb ⊢
  intro y z
  rw [catMu_apply]
  refine Submodule.sum_mem _ fun w _ ↦ ?_
  change Φ.wφ W hfin χ _ _ ∈ _
  rw [Φ.wφ_hom W hfin χ (hb y w) (ha w z), show α + β + χ = β + α + χ by abel]
  exact wπ_mem W _ _

theorem catMu_zero {q : ℕ} : catMu D (CatCocycle.zero (c := c) (q := q)) = 0 := by
  ext a b
  apply MulOpposite.unop_injective; apply CatAlg.ext; intro y z
  simp [catMu_apply, CatCocycle.zero]

theorem Ψc_cast {q : ℕ} {μ μ' : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (e : μ = μ') (Ld : LiftData D hfin q μ) : Ψc (e ▸ Ld) = Ψc Ld := by
  subst e; rfl

include hfin hfd in
/-- **Proposition 12.5 with weights**: a correction tuple of relative weight `χ` is `Ψ[μ]` for a
cocycle `μ` of character `χ`. -/
theorem Ψc_surjective_char
    (hres : ∀ w x, Function.Injective
        (FlatPert.relMap (FlatPert.meshPres c) (FlatPert.idealC (FlatPert.meshPres c))
          (FlatPert.meshPres c).r w x) ∧
      LinearMap.ker (FlatPert.alpha (FlatPert.idealC (FlatPert.meshPres c)) w x) ≤
        LinearMap.range (FlatPert.relMap (FlatPert.meshPres c)
          (FlatPert.idealC (FlatPert.meshPres c)) (FlatPert.meshPres c).r w x))
    {q : ℕ} (hq : 1 ≤ q) (χ : M) (z : MeshFamily c)
    (hz : ∀ x, z x ∈ ScalarMeshCategory.degreePart c (q + 2) (Q.tau x).1 x.1)
    (hzw : ∀ x, z x ∈ wP c W (W.ν x + χ) (Q.tau x).1 x.1) :
    ∃ (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (_ : IsHCocycle μ)
      (_ : HDeg (galgA0 D hfin) μ (q : ℤ)) (_ : HasChar W hfin D χ μ)
      (Ld : LiftData D hfin q μ), Ψc Ld = Submodule.Quotient.mk z := by
  haveI := hfin
  obtain ⟨N, hN⟩ := MeshFirstOrder.exists_hN c
  obtain ⟨Φ, hΦ⟩ := MeshFirstOrder.exists_catCocycle (c := c) ⟨N, hN, hres, q, hq, z, hz⟩
  have hval : (Φ.wproj W hfin χ).meshVal = z := by
    funext x
    rw [CatCocycle.meshVal_wproj, hΦ, wπ_of_mem W (hzw x), if_pos rfl]
  refine ⟨catMu D (Φ.wproj W hfin χ), catMu_isHCocycle D _, catMu_hDeg D hfin _,
    catMu_hasChar W hfin D Φ χ, catLift D hfin _, (Ψc_catLift D hfin _).trans (congrArg _ hval)⟩

include hfin hfd in
/-- **`I ⊆ I₀`** (`deformation-refinements.tex:278–283`): a row `p : τx → x` of length
`q + 2 ≥ 3` whose class in `coker D_{q+1}` is nonzero gives a Hochschild cocycle of `A₀` of
internal degree `q` and of the row's character `χ = w(p) − ν_x` which is not a coboundary of
degree `q`, with `Ψ[μ] = [p]`. -/
theorem exists_not_cobdry (J : D.InjData) (h1 : DegOne D)
    (hres : ∀ w x, Function.Injective
        (FlatPert.relMap (FlatPert.meshPres c) (FlatPert.idealC (FlatPert.meshPres c))
          (FlatPert.meshPres c).r w x) ∧
      LinearMap.ker (FlatPert.alpha (FlatPert.idealC (FlatPert.meshPres c)) w x) ≤
        LinearMap.range (FlatPert.relMap (FlatPert.meshPres c)
          (FlatPert.idealC (FlatPert.meshPres c)) (FlatPert.meshPres c).r w x))
    {q : ℕ} (hq : 1 ≤ q) (x : Q.nonprojective) (p : Quiver.Path (Q.tau x).1 x.1)
    (hp : p.length = q + 2) (hne : rowClass c (q + 1) x p ≠ 0) :
    ∃ (μ : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ) (_ : IsHCocycle μ)
      (_ : HDeg (galgA0 D hfin) μ (q : ℤ)) (_ : HasChar W hfin D (W.pw p - W.ν x) μ)
      (Ld : LiftData D hfin q μ), Ψc Ld = rowClass c (q + 1) x p ∧
      ¬ ∃ H : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ,
        (∀ p a, (galgA0 D hfin).gr.IsHom p a → (galgA0 D hfin).gr.IsHom (p + q) (H a)) ∧
        μ = hcobdry H := by
  classical
  have hz : ∀ y, row c x p y ∈ ScalarMeshCategory.degreePart c (q + 2) (Q.tau y).1 y.1 := by
    intro y
    by_cases hy : y = x
    · subst hy
      rw [row, Pi.single_eq_same, ← hp]
      exact ⟨LinearPaths.path p, LinearPaths.path_mem_degreePart p, rfl⟩
    · rw [row, Pi.single_eq_of_ne hy]; exact zero_mem _
  have hzw : ∀ y, row c x p y ∈ wP c W (W.ν y + (W.pw p - W.ν x)) (Q.tau y).1 y.1 := by
    intro y
    by_cases hy : y = x
    · subst hy
      rw [row, Pi.single_eq_same, show W.ν y + (W.pw p - W.ν y) = W.pw p by abel]
      exact pathMor_mem_wP W p
    · rw [row, Pi.single_eq_of_ne hy]; exact zero_mem _
  obtain ⟨μ, hμ, hμdeg, hχ, Ld, hLd⟩ :=
    Ψc_surjective_char W hfin D hres hq (W.pw p - W.ν x) (row c x p) hz hzw
  refine ⟨μ, hμ, hμdeg, hχ, Ld, hLd, ?_⟩
  rintro ⟨H, hH, rfl⟩
  apply hne
  -- the coboundary of the zero cocycle has `Ψ = 0`
  set Ld₀ := (catLift D hfin (CatCocycle.zero (c := c) (q := q))).cobdry H hH
  have e : catMu D (CatCocycle.zero (c := c) (q := q)) + hcobdry H = hcobdry H := by
    rw [catMu_zero, zero_add]
  have h0 : Ψc (e ▸ Ld₀) = 0 := by
    rw [Ψc_cast, Ψc_cobdry, Ψc_catLift, CatCocycle.meshVal_zero, Submodule.Quotient.mk_zero]
  change Submodule.Quotient.mk (row c x p) = 0
  rw [← hLd, Ψc_indep J h1 (e ▸ Ld₀) Ld, h0]

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.IndSkeleton

universe w

variable {k A : Type w} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)
  {M : Type} [AddCommGroup M] (W : MeshWalk.MeshWt S.arTranslationQuiver M)

/-- **`I ⊆ I₀` for `A₀`** (Proposition 12.5, `deformation-refinements.tex:278–283`): a row of
`Γ_A` of length `q + 2 ≥ 3` with nonzero cokernel class gives a non-trivial Hochschild class of
`A₀` of the row's character. -/
theorem exists_not_cobdry_ar {q : ℕ} (hq : 1 ≤ q) (x : S.arTranslationQuiver.nonprojective)
    (p : Quiver.Path (S.arTranslationQuiver.tau x).1 x.1) (hp : p.length = q + 2)
    (hne : ScalarMeshCategory.rowClass (S.arCoefficients b) (q + 1) x p ≠ 0) :
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    ∃ (μ : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k]
        (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) (_ : GExt.IsHCocycle μ)
      (_ : GExt.HDeg (MeshWalk.galgA0 (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y))
        μ (q : ℤ))
      (_ : MeshWalk.HasChar W (fun x y ↦ S.finiteDimensional_meshHom b x y) (S.arMeshData b)
        (W.pw p - W.ν x) μ)
      (Ld : MeshWalk.LiftData (S.arMeshData b) (fun x y ↦ S.finiteDimensional_meshHom b x y) q μ),
      MeshWalk.Ψc Ld = ScalarMeshCategory.rowClass (S.arCoefficients b) (q + 1) x p ∧
      ¬ ∃ H : (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ →ₗ[k] (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ,
        (∀ p a, (MeshWalk.galgA0 (S.arMeshData b)
            (fun x y ↦ S.finiteDimensional_meshHom b x y)).gr.IsHom p a →
          (MeshWalk.galgA0 (S.arMeshData b)
            (fun x y ↦ S.finiteDimensional_meshHom b x y)).gr.IsHom (p + q) (H a)) ∧
        μ = GExt.hcobdry H :=
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  MeshWalk.exists_not_cobdry W (fun x y ↦ S.finiteDimensional_meshHom b x y) (S.arMeshData b)
    (S.arInjData b) (S.arDegOne b) (S.hres_ar b) hq x p hp hne

end MultiplicativeBasisDeformations.IndSkeleton
