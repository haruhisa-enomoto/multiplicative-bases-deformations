module

public import MultiplicativeBasisDeformations.Foundations.ExtResolutions

/-!
# Lemma 6.3(2) with `Ext` from graded projective resolutions

`positive-deformations.tex`: internal degree `t` in `Ext` means degree-`t` maps from a
graded projective resolution, and `Ext^n_{A₀}(M_i, M_j)_t = 0` for `n ≥ 1`, `t > −2n`. Every
`M_i` has a graded projective resolution (`exists_gres_ev`), and for every one of them the `Ext`
computed from it vanishes in the stated range (`extVanish_ev_res`), by the comparison with the
bar `Ext` (`GExt.GRes.extVanish_iff`) and the bar form of the lemma (`extVanish_ev`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- `A₀` is finite-dimensional. -/
theorem finite_A0op : Module.Finite k (Alg D.F0)ᵐᵒᵖ :=
  Module.Finite.equiv (MulOpposite.opLinearEquiv k)

/-- **Every `M_i` has a graded projective resolution** (by finite free graded `A₀`-modules). -/
theorem exists_gres_ev (i : V) : Nonempty (GExt.GRes (gmodEv D hfin i)) :=
  haveI := finite_A0op D
  GExt.exists_gres _

/-- **The `Ext` of any graded projective resolution of `M_i` is the bar `Ext`.** -/
theorem gres_extVanish_iff (i j : V) (Rs : GExt.GRes (gmodEv D hfin i)) (n : ℕ) (t : ℤ) :
    Rs.ExtVanish (gmodEv D hfin j) n t ↔ GExt.ExtVanish (gmodEv D hfin i) (gmodEv D hfin j) n t :=
  GExt.GRes.extVanish_iff_field _ n Rs t

/-- **Lemma 6.3(2)** (`lem:positive-ext-vanishing`), with `Ext` as in the manuscript: for every
graded projective resolution of `M_i`, the `Ext^{n+1}_{A₀}(M_i, M_j)_t` computed from it vanishes
for `t > −2(n+1)`, and for all `t` when `M_i` is projective. -/
theorem extVanish_ev_res (J : InjData D) (h1 : DegOne D) (n : ℕ) (i j : V) (t : ℤ)
    (ht : D.proj i ∨ -2 * ((n : ℤ) + 1) < t) (Rs : GExt.GRes (gmodEv D hfin i)) :
    Rs.ExtVanish (gmodEv D hfin j) n t :=
  (gres_extVanish_iff D hfin i j Rs n t).2 (extVanish_ev D hfin J h1 n i j t ht)

end MeshWalk

end MultiplicativeBasisDeformations
