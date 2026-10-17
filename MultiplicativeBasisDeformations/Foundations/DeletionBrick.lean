import MultiplicativeBasisDeformations.Foundations.InjectiveLabels

/-!
# Lemma 5.2: object quotients have bricks

`lem:deletion-brick` (`mesh-deformations.tex`): "Among the objects
outside `Σ`, choose `X` of least composition length. Every radical endomorphism
of `X` factors through its proper image. Each indecomposable summand of that
image has smaller length, belongs to `D` by image-closure, and therefore belongs
to `Σ`. Hence the radical of `End(X)` becomes zero in the quotient. Its identity
remains nonzero … Thus its quotient endomorphism ring is its residue division
algebra." "By Proposition 2.10, this applies to `C` as `ind(mod A₀)`."

We run this argument for `C` through the evaluation `ev : add C ≃ mod A₀`
(full faithfulness and essential surjectivity, Lemma 2.9 and Proposition 2.10):
the length of `X` is `dim ev(X)`, the image of `ev(r)` is `ev(W)` for a family
`W` of smaller labels, and `r` factors through `W`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  {L : LocalFamily (k := k) F} (D : MeshData F L)

namespace MeshData

section Families

variable {κ κ' κ'' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
  [Fintype κ''] [DecidableEq κ'']

/-- Composition of matrices (first `α`, then `β`). -/
def matMul {Z : κ → ι} {Z' : κ' → ι} {Z'' : κ'' → ι} (α : Mat F Z Z') (β : Mat F Z' Z'') :
    Mat F Z Z'' := fun j j'' ↦ ∑ j', α j j' ≫ β j' j''

theorem evMap_comp {Z : κ → ι} {Z' : κ' → ι} {Z'' : κ'' → ι} (α : Mat F Z Z') (β : Mat F Z' Z'') :
    (D.evMap β).comp (D.evMap α) = D.evMap (matMul α β) := by
  refine LinearMap.ext fun m ↦ funext fun j'' ↦ ?_
  rw [LinearMap.comp_apply, evMap_apply, evMap_apply]
  simp only [evMap_apply, map_sum, matMul, repMap_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦ ?_
  rw [repMap_comp, LinearMap.comp_apply]

theorem evMap_sub {Z : κ → ι} {Z' : κ' → ι} (f g : Mat F Z Z') :
    D.evMap (f - g) = D.evMap f - D.evMap g := by
  refine LinearMap.ext fun m ↦ funext fun j' ↦ ?_
  rw [LinearMap.sub_apply, Pi.sub_apply, evMap_apply, evMap_apply, evMap_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change repMap (f j j' - g j j') (m j) = _
  ext y
  simp [Preadditive.comp_sub]

end Families

variable (F) in
/-- The maps through objects of `Σ`. -/
def through (Sg : Set ι) (x y : ι) : Submodule k (F x ⟶ F y) :=
  Submodule.span k {h | ∃ s ∈ Sg, ∃ (f : F x ⟶ F s) (g : F s ⟶ F y), h = f ≫ g}

theorem through_le_rad (Sg : Set ι) {x : ι} (hx : x ∉ Sg) : through (k := k) F Sg x x ≤ L.rad x x :=
  Submodule.span_le.2 fun _ ⟨s, hs, f, g, he⟩ ↦ by
    rw [he]
    exact L.comp_right (L.mem_of_ne (fun e ↦ hx (by rw [e]; exact hs)) f) g

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (J : InjData D)

include J in
/-- **Lemma 5.2 for `C`**: a label outside `Σ` of least evaluation dimension has
all its radical endomorphisms factoring through `Σ`. -/
theorem brick (Sg : Set ι) (hne : ∃ x, x ∉ Sg) :
    ∃ x, x ∉ Sg ∧ L.rad x x ≤ through (k := k) F Sg x x := by
  classical
  set d : ι → ℕ := fun x ↦ Module.finrank k (Rep D.F0 (F x))
  obtain ⟨x, hx, hmin⟩ := (Finset.univ.filter (· ∉ Sg)).exists_min_image d
    (by obtain ⟨x, hx⟩ := hne; exact ⟨x, by simpa using hx⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hmin
  refine ⟨x, hx, fun r hr ↦ ?_⟩
  set ρ : Rep D.F0 (F x) →ₗ[Alg D.F0] Rep D.F0 (F x) := repMap (F := D.F0) r
  set M := LinearMap.range ρ
  by_cases hdim : Module.finrank k (M.restrictScalars k) < d x
  · -- `M ≅ ev(W)` with smaller labels
    haveI : FiniteDimensional k M :=
      Module.Finite.of_injective (M.subtype.restrictScalars k) Subtype.val_injective
    obtain ⟨μ, _, _, W, ⟨eM⟩⟩ := J.essSurj (X := M)
    have hW : ∀ j, W j ∈ Sg := by
      intro j
      by_contra hj
      have h1 := hmin (W j) hj
      have h2 : d (W j) ≤ Module.finrank k (D.EZ W) := by
        change Module.finrank k (Rep D.F0 (F (W j))) ≤
          Module.finrank k (∀ j, Rep D.F0 (F (W j)))
        rw [Module.finrank_pi_fintype]
        exact Finset.single_le_sum (f := fun j ↦ Module.finrank k (Rep D.F0 (F (W j))))
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      have h3 : Module.finrank k (D.EZ W) = Module.finrank k (M.restrictScalars k) :=
        (LinearEquiv.finrank_eq (eM.restrictScalars k)).symm
      omega
    -- the factorization through `W`
    set α' : D.EZ (uZ x) →ₗ[Alg D.F0] D.EZ W :=
      eM.toLinearMap.comp (ρ.rangeRestrict.comp (D.eU (F x)).symm.toLinearMap)
    set β' : D.EZ W →ₗ[Alg D.F0] D.EZ (uZ x) :=
      (D.eU (F x)).toLinearMap.comp (M.subtype.comp eM.symm.toLinearMap)
    obtain ⟨α, hα⟩ := D.evMap_surjective α'
    obtain ⟨β, hβ⟩ := D.evMap_surjective β'
    have hcomp : D.evMap (matMul α β) = D.evMap (fun _ _ ↦ r : Mat F (uZ x) (uZ x)) := by
      rw [← D.evMap_comp, hα, hβ]
      refine LinearMap.ext fun m ↦ funext fun u ↦ ?_
      simp only [α', β', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.subtype_apply]
      rw [evMap_apply, Fintype.sum_unique]
      rfl
    have hmat : matMul α β = fun _ _ ↦ r := by
      have := D.evMap_injective (f := matMul α β - fun _ _ ↦ r) (by
        rw [D.evMap_sub, hcomp, sub_self])
      exact sub_eq_zero.1 this
    have hr : r = ∑ j, α () j ≫ β j () := (congrFun (congrFun hmat ()) ()).symm
    rw [hr]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.subset_span ⟨W j, hW j, _, _, rfl⟩
  · -- `ρ` is onto, hence `ev(x) = 0` and `r = 0`
    have htop : M.restrictScalars k = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le (M.restrictScalars k)
      exact le_antisymm this (not_lt.1 hdim)
    have hsurj : Function.Surjective ρ := by
      intro m
      have : m ∈ M.restrictScalars k := htop ▸ Submodule.mem_top
      exact this
    set r' : End (F x) := r
    obtain ⟨n, hn⟩ := L.nilpotent x r' hr
    have hpow : ∀ n : ℕ, repMap (F := D.F0) (r' ^ n) = ρ ^ n := by
      intro n
      induction n with
      | zero =>
          refine LinearMap.ext fun m ↦ ?_
          ext y
          change m y ≫ 𝟙 _ = m y
          rw [Category.comp_id]
      | succ n ih =>
          rw [pow_succ, End.mul_def, repMap_comp, ih]
          exact (pow_succ ρ n).symm
    have hz : ∀ m, ρ m = 0 := by
      have hs : Function.Surjective (ρ ^ n) := by
        rw [Module.End.coe_pow]; exact hsurj.iterate n
      intro m
      obtain ⟨m', rfl⟩ := hs m
      rw [← hpow, hn, repMap_zero]
      simp
    have h0 : r' = 0 := D.repMap_eq_zero _ _ r' hz
    rw [h0]
    exact zero_mem _

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
