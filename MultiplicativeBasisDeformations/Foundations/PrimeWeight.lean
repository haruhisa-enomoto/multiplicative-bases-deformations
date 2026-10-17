import MultiplicativeBasisDeformations.Foundations.PrimeTable
import MultiplicativeBasisDeformations.Foundations.IntegralWeightInstance

/-!
# Weight-homogeneous lifts for `A⁽²⁾ = 𝔽₂P` (Proposition 10.1)

`integral-deformations.tex`: "lifting a basis of `H_ℤ` to mesh weights by Lemma 7.4 gives
the modules `M_i⁽²⁾` compatible weight gradings, and the corrections can be chosen in each weight
component."

For the table `tab₂` of `A⁽²⁾` and any mesh weight `W` (with values in any abelian group), the
ray weights are the restriction of `W` (`hvW`, Lemma 7.4's `MeshWt.rv`), and the ray basis
vectors `Θ₂(b_r) = e_r` of `A⁽²⁾` are homogeneous of these weights (`hΘ₂`): `e_r` is the matrix
unit of a path of the deck degree of `r` (`eT_eq_path`). So the weight-homogeneous lifts hold
for `A⁽²⁾` with no further hypothesis (`exists_modLiftW₂`, `exists_arrowLiftW₂`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MGr

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [DecidableEq M] {N : Type*}
  [AddCommGroup N] [Module R N] (G : MGr R M N)

/-- A nonzero homogeneous element has a unique weight. -/
theorem isHom_unique {g h : M} {n : N} (hn : n ≠ 0) (hg : G.IsHom g n) (hh : G.IsHom h n) :
    g = h := by
  by_contra hne
  apply hn
  rw [← hh, G.proj_of_isHom hg, if_neg hne]

end MGr

namespace IndSkeleton

universe w

open ScalarMeshCategory CatAlg MeshWalk WLift GExt

attribute [local instance] ZMod.algebra Classical.decEq

variable {k A : Type w} [Field k] [IsAlgClosed k] [CharP k 2] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)
  [∀ x y : S.ARVertex, Subsingleton (x ⟶ y)]
  [∀ x y : S.ARVertex, FiniteDimensional k (MeshWalk.meshFam S.arTranslationQuiver
    (S.arCoefficients b) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y)]
  [∀ x y : S.ARVertex, FiniteDimensional (ZMod 2) (MeshWalk.meshFam S.arTranslationQuiver
    (S.oneC (ZMod 2)) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) y)]
  (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (Alg (S.arMeshData b).F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt S.arTranslationQuiver ℤ)
  {M : Type} [AddCommGroup M] (W : MeshWt S.arTranslationQuiver M)

/-- **The ray weights of a mesh weight** (the restriction of Lemma 7.4). -/
def hvW (r : RayA0 (S.arMeshData b) v₀) : M :=
  W.rv (c := S.arCoefficients b) (D := S.arMeshData b) r.1

include hF in
theorem exists_path_ray (r : RayA0 (S.arMeshData b) v₀) :
    ∃ p : Quiver.Path r.1.1.1 r.1.2.1.1, (degW S.arTranslationQuiver v₀).deg p = r.1.2.2 ∧
      pathMor (S.arCoefficients b) p ≠ 0 := by
  obtain ⟨⟨x, y, g⟩, hr⟩ := r
  have hv := deckV_ne (S.arMeshData b) v₀ hF x y g hr
  by_contra hne
  push Not at hne
  apply hv
  have hf : deckV (S.arMeshData b) v₀ hF x y g ∈
      wPart (S.arCoefficients b) (degW S.arTranslationQuiver v₀) g x.1 y.1 :=
    (isHom_iff (Q := S.arTranslationQuiver) (c := S.arCoefficients b) (v₀ := v₀)).1
      ((HomGrading.mem_part_iff _).1 (deckV_mem (S.arMeshData b) v₀ hF x y g))
  have := wPart_le_span (Q := S.arTranslationQuiver) (c := S.arCoefficients b) (v₀ := v₀) g
    x.1 y.1 hf
  have hsub : Submodule.span k {f | ∃ p : Quiver.Path x.1 y.1,
      (degW S.arTranslationQuiver v₀).deg p = g ∧ pathMor (S.arCoefficients b) p = f} ≤ ⊥ :=
    Submodule.span_le.2 fun f hf ↦ by
      obtain ⟨p, hp, rfl⟩ := hf; exact (Submodule.mem_bot k).2 (hne p hp)
  exact (Submodule.mem_bot k).1 (hsub this)

/-- **`e_r` is the matrix unit of any path of the deck degree of `r` with nonzero image.** -/
theorem eT_eq_path (r : RayA0 (S.arMeshData b) v₀) {p : Quiver.Path r.1.1.1 r.1.2.1.1}
    (hp : (degW S.arTranslationQuiver v₀).deg p = r.1.2.2) (hp0 : pathMor (S.arCoefficients b) p ≠ 0) :
    S.eT b v₀ hF Wd r = MulOpposite.op (unitM (F := (S.primeMeshData b).F0) r.1.1 r.1.2.1
      (pathMor (S.oneC (ZMod 2)) p)) := by
  obtain ⟨⟨x, y, g⟩, hr⟩ := r
  have hpm : pathMor (S.arCoefficients b) p ∈ (D0 S.arTranslationQuiver (S.arCoefficients b) v₀
      (S.arMeshData b)).part g x y := by
    refine (HomGrading.mem_part_iff _).2 ((isHom_iff (Q := S.arTranslationQuiver)
      (c := S.arCoefficients b) (v₀ := v₀)).2 ?_)
    have hp' : (degW S.arTranslationQuiver v₀).deg p = g := hp
    have hm := pathMor_mem_wPart (c := S.arCoefficients b) (wt := degW S.arTranslationQuiver v₀) p
    rw [hp'] at hm
    exact hm
  obtain ⟨α, hα⟩ := deckV_span (S.arMeshData b) v₀ hF x y g _ hpm
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_smul] at hα; exact hp0 hα
  have hι : S.ι₂ b (MulOpposite.op (unitM (F := (S.primeMeshData b).F0) x y
      (pathMor (S.oneC (ZMod 2)) p))) = (((pathWt (S.arMu b) p : kˣ) : k) * α) •
        basisR (S.arMeshData b) v₀ hF ⟨(x, y, g), hr⟩ := by
    rw [ι₂_unitM, S.Fm2_pathMor b, hα, smul_smul, unitM_smul, MulOpposite.op_smul, basisR_apply]
  refine S.eq_of_ι₂_mem_span b (S.eT_ne_zero b v₀ hF Wd _) (fun h0 ↦ ?_) (S.eT_mem b v₀ hF Wd _)
    (by rw [hι]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  rw [h0, ι₂_zero] at hι
  exact smul_ne_zero (mul_ne_zero (Units.ne_zero _) hα0)
    ((basisR (S.arMeshData b) v₀ hF).ne_zero _) hι.symm

/-- The matrix unit of a path is homogeneous of the weight of the path. -/
theorem unitM_path_isHom {x y : (S.primeMeshData b).PV} (p : Quiver.Path x.1 y.1) :
    (grA0 W (hfin2 (c := S.oneC (ZMod 2))) (S.primeMeshData b)).IsHom (W.pw p)
      (MulOpposite.op (unitM (F := (S.primeMeshData b).F0) x y (pathMor (S.oneC (ZMod 2)) p))) := by
  rw [grA0_isHom]
  intro p' q'
  change unitM (F := (S.primeMeshData b).F0) x y (pathMor (S.oneC (ZMod 2)) p) p' q' ∈ _
  rw [unitM_apply]
  by_cases h1 : p' = x
  · subst h1
    by_cases h2 : y = q'
    · subst h2
      rw [idTo_self, idTo_self, Category.id_comp, Category.comp_id]
      exact pathMor_mem_wP (c := S.oneC (ZMod 2)) W p
    · rw [idTo_ne h2, Limits.comp_zero, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [idTo_ne h1, Limits.zero_comp]; exact Submodule.zero_mem _

/-- **The basis vectors `e_r` of `A⁽²⁾` are homogeneous for the restricted weights.** -/
theorem eT_isHomW (r : RayA0 (S.arMeshData b) v₀) :
    (grA0 W (hfin2 (c := S.oneC (ZMod 2))) (S.primeMeshData b)).IsHom (S.hvW b v₀ W r)
      (S.eT b v₀ hF Wd r) := by
  obtain ⟨p, hp, hp0⟩ := S.exists_path_ray b v₀ hF r
  rw [S.eT_eq_path b v₀ hF Wd r hp hp0, hvW, MeshWt.rv_path W r.2 hp]
  exact S.unitM_path_isHom b W p

/-- **The ray basis `Θ₂(b_r)` of `A⁽²⁾` is homogeneous for the restricted weights.** -/
theorem hΘ₂ (r : RayA0 (S.arMeshData b) v₀) :
    (grA0 W (hfin2 (c := S.oneC (ZMod 2))) (S.primeMeshData b)).IsHom (S.hvW b v₀ W r)
      ((S.tab₂ b v₀ hF Wd).Θ ((SysD (S.arMeshData b) v₀ hF Wd).P.toMult.b (ZMod 2) r)) := by
  change (grA0 W (hfin2 (c := S.oneC (ZMod 2))) (S.primeMeshData b)).IsHom (S.hvW b v₀ W r)
    (S.Θ₂ b v₀ hF Wd ((SysD (S.arMeshData b) v₀ hF Wd).P.b (ZMod 2) r))
  rw [Θ₂_b]
  exact S.eT_isHomW b v₀ hF Wd W r

/-- The restricted ray weights are additive on nonzero products. -/
theorem hvW_mul (r s t : RayA0 (S.arMeshData b) v₀)
    (h : (SysD (S.arMeshData b) v₀ hF Wd).P.toMult.mul r s = some t) :
    S.hvW b v₀ W t = S.hvW b v₀ W r + S.hvW b v₀ W s := by
  have e : S.eT b v₀ hF Wd r * S.eT b v₀ hF Wd s = S.eT b v₀ hF Wd t := by
    rw [S.eT_mul b v₀ hF Wd]
    rw [h, Option.elim_some]
  refine MGr.isHom_unique _ (S.eT_ne_zero b v₀ hF Wd t) (S.eT_isHomW b v₀ hF Wd W t) ?_
  rw [← e]
  exact grA0_mul W _ _ (S.eT_isHomW b v₀ hF Wd W r) (S.eT_isHomW b v₀ hF Wd W s)

/-- The restricted ray weights vanish on the idempotents. -/
theorem hvW_e (x : (S.arMeshData b).PV) :
    S.hvW b v₀ W ((SysD (S.arMeshData b) v₀ hF Wd).P.toMult.e x) = 0 := by
  refine MGr.isHom_unique _ (S.eT_ne_zero b v₀ hF Wd _) (S.eT_isHomW b v₀ hF Wd W _) ?_
  change (grA0 W (hfin2 (c := S.oneC (ZMod 2))) (S.primeMeshData b)).IsHom 0
    (S.eT b v₀ hF Wd ((SysD (S.arMeshData b) v₀ hF Wd).P.e x))
  rw [S.eT_e b v₀ hF Wd, eP, idem_eq_unitM]
  have := S.unitM_path_isHom b W (x := x) (y := x) Quiver.Path.nil
  rwa [pathMor_nil, show W.pw (Quiver.Path.nil : Quiver.Path x.1 x.1) = 0 by simp [MeshWt.pw]]
    at this

/-! ### Proposition 10.1: weight-homogeneous lifts for `A⁽²⁾` -/

variable {r : ℕ} (φ : Fin r → M →+ ℤ)

/-- **Proposition 10.1, weight-homogeneous module lifts for `A⁽²⁾ = 𝔽₂P`**: for any mesh weight
`W` and any finite family of integer coordinates, every evaluated module `M_X⁽²⁾` lifts to
`𝒪 = ℤ/4` with an action homogeneous for the degree and for every coordinate of the restricted
ray weights. -/
theorem exists_modLiftW₂ (X : S.ARVertex) :
    Nonempty (ModLiftW (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) (S.hvW_mul b v₀ hF Wd W)
      (S.hvW_e b v₀ hF Wd W) φ X) :=
  exists_modLiftW (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) (S.hvW_mul b v₀ hF Wd W)
    (S.hvW_e b v₀ hF Wd W) (S.hΘ₂ b v₀ hF Wd W) φ (S.primeInjData b) (S.primeDegOne b) X

/-- **Proposition 10.1, weight-homogeneous arrow lifts for `A⁽²⁾ = 𝔽₂P`**: the arrow maps lift
to maps of degree one, homogeneous of the weight of the arrow for every coordinate. -/
theorem exists_arrowLiftW₂
    (N : ∀ X, ModLiftW (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) (S.hvW_mul b v₀ hF Wd W)
      (S.hvW_e b v₀ hF Wd W) φ X) {y x : S.ARVertex} (a : y ⟶ x) :
    ∃ f : (Fin (N y).n → ZMod 4) →ₗ[ZMod 4] (Fin (N x).n → ZMod 4),
      (∀ m b, f ((N y).MM.act m b) = (N x).MM.act (f m) b) ∧
      (∀ m, ρF (N x).β (f m) = fA (S.primeMeshData b) a (ρF (N y).β m)) ∧
      (∀ p m, (N y).MM.gr.IsHom p m → (N x).MM.gr.IsHom (p + 1) (f m)) ∧
      ∀ i p m, (grF ((N y).wβ i)).IsHom p m →
        (grF ((N x).wβ i)).IsHom (p + φ i (W.w a)) (f m) :=
  exists_arrowLiftW (S.tab₂ b v₀ hF Wd) W (S.hvW b v₀ W) (S.hvW_mul b v₀ hF Wd W)
    (S.hvW_e b v₀ hF Wd W) (S.hΘ₂ b v₀ hF Wd W) φ (S.primeInjData b) (S.primeDegOne b) N a

end IndSkeleton

end MultiplicativeBasisDeformations
