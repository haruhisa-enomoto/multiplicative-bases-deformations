import MultiplicativeBasisDeformations.Foundations.FinalStandardness
import MultiplicativeBasisDeformations.Foundations.InitialFormProducts

/-!
# Proposition 8.2 in every characteristic

`local-ray-geometry.tex` (`prop:table-weight-lifting`): "Let `T` be a weighted
multiplication table whose linearization `kT` is representation-finite over the algebraically
closed field `k`. Every additive weight `T → ℤ/2` lifts to an additive weight `T → ℤ`."

The induction of `Induction.lean` proves this in characteristic two. Here, in every
characteristic: a connected table presents `kT` (`self_rayPres`), and so does the ray table of
the algebra `A₀` of `kT` (`rayA_eq_rayA0`, Theorem 11.8(1)); the latter has the lifting
property (`A0Mult_lift2`, `W(P)` free), which passes along the comparison of the two
presentations (`IsRayPres.lift2`). Disconnected tables split along a component
(`lift2_of_split`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The connected case**, in every characteristic. -/
theorem lift2_conn_any {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R]
    [DecidableEq R] (T : RaySys.Tab V R L) (hfin : IsRepresentationFinite k (T.Lin k))
    (hc : T.Conn) (hV : Nonempty V) : T.Lift2 := by
  classical
  haveI : IsNoetherianRing (T.Lin k)ᵐᵒᵖ := IsNoetherianRing.of_finite k (T.Lin k)ᵐᵒᵖ
  haveI hn : Nontrivial (T.Lin k) := ⟨⟨T.b k (T.e hV.some), 0, RaySys.Mult.b_ne_zero _ k _⟩⟩
  obtain ⟨S⟩ := exists_indSkeleton hfin
  obtain ⟨b, v₀, hF, F1, ι1, β1, hpres1⟩ := rayA_eq_rayA0 k (T.Lin k) (T.isBasic_lin k) hfin hn S
  set Ssys := T.toSys k hfin
  have hpres2 := Ssys.self_rayPres k hfin
  obtain ⟨ψ, σ, hψ⟩ := exists_algEquiv_idempotents (k := k)
    (T.isBasic_lin k) (Ssys.fibreIdem k hfin 0 (LinearEquiv.refl k _) (Ssys.self_hΨ k)) F1
  have hpres2' := hpres2.map ψ F1 σ hψ
  have hconnA : (S.A0MultAR b v₀ hF).Conn := hpres2'.conn hpres1 hc
  have hm : F1.m ≠ 0 := ne_zero_of_complete F1.complete
  have hL : (S.A0MultAR b v₀ hF).Lift2 := by
    haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    set x₀ := ι1.symm ⟨0, Nat.pos_of_ne_zero hm⟩
    exact MeshWalk.A0Mult_lift2 (S.arMeshData b) v₀ hF x₀
      (MeshWalk.A0Conn_of_conn (S.arMeshData b) v₀ hF hconnA x₀)
  exact hpres2'.lift2 hfin hpres1 hL

/-- **Proposition 8.2** (`prop:table-weight-lifting`), in every characteristic: every additive
weight modulo two of a table with representation-finite linearization lifts to `ℤ`. -/
theorem tableWeightLifting {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V]
    [Fintype R] [DecidableEq R] (T : RaySys.Tab V R L) (hfin : IsRepresentationFinite k (T.Lin k)) :
    T.Lift2 := by
  suffices h : ∀ n, ∀ (V R L : Type) [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R]
      [DecidableEq R] (T : RaySys.Tab V R L), Fintype.card R < n →
      IsRepresentationFinite k (T.Lin k) → T.Lift2 from h _ V R L T (Nat.lt_succ_self _) hfin
  intro n
  induction n with
  | zero => intro V R L _ _ _ _ _ T hT; omega
  | succ n ih =>
    intro V R L _ _ _ _ _ T hT hfin
    classical
    by_cases hV : Nonempty V
    · by_cases hc : T.Conn
      · exact lift2_conn_any T hfin hc hV
      · obtain ⟨C, hC, hxC, hx⟩ := RaySys.Tab.exists_split hc
        refine RaySys.Tab.lift2_of_split hC (ih _ _ _ _ ?_ ?_) (ih _ _ _ _ ?_ ?_)
        · obtain ⟨y, hy⟩ := hx
          have := Fintype.card_subtype_lt (p := (RaySys.Tab.compData hC).pR) (x := T.e y)
            (by change ¬ C (T.src (T.e y)); rw [T.src_e]; exact hy)
          exact lt_of_lt_of_le this (by omega)
        · exact RaySys.Tab.comp_isRepresentationFinite hC k hfin
        · obtain ⟨y, hy⟩ := hxC
          have := Fintype.card_subtype_lt (p := (RaySys.Tab.compData hC.compl).pR) (x := T.e y)
            (by change ¬ ¬ C (T.src (T.e y)); rw [T.src_e]; exact not_not.2 hy)
          exact lt_of_lt_of_le this (by omega)
        · exact RaySys.Tab.comp_isRepresentationFinite hC.compl k hfin
    · haveI : IsEmpty V := not_nonempty_iff.1 hV
      haveI : IsEmpty R := ⟨fun r ↦ isEmptyElim (T.src r)⟩
      intro w _
      exact ⟨fun r ↦ isEmptyElim r, fun r ↦ isEmptyElim r, fun r ↦ isEmptyElim r⟩

/-- **Proposition 8.3** (`prop:dimension-induction`), in every characteristic: for a basic
representation-finite algebra `A`, (1) `A` has a normed multiplicative basis consisting of one
representative of each nonzero ray (`finalBasis_ray`); (2) the initial-form bijection identifies
the products in `ray A` and `ray A₀` (`rayA_initialForms`); (3) `ray A` is presented by the
table of `A₀`, whose weight group is free abelian (`W_A0_free`). -/
theorem dimensionInduction (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A) (hn : Nontrivial A) :
    (∀ F : PrimitiveIdempotents A, ∃ b : Module.Basis (F.NonzeroRay k) k A,
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b) ∧
    (letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
     ∀ S : IndSkeleton k A, ∃ (b : S.ArrowBases) (v₀ : S.ARVertex)
      (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
      (F : PrimitiveIdempotents A) (ι : (S.arMeshData b).PV ≃ Fin F.m)
      (β : S.rayA0AR b v₀ → A), F.IsRayPres (k := k) (S.A0MultAR b v₀ hF) ι β ∧
        Module.Free ℤ (S.A0MultAR b v₀ hF).W) := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  refine ⟨fun F ↦ finalBasis_ray k A hbasic hA F, fun S ↦ ?_⟩
  obtain ⟨b, v₀, hF, F, ι, β, h⟩ := rayA_eq_rayA0 k A hbasic hA hn S
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  exact ⟨b, v₀, hF, F, ι, β, h, MeshWalk.W_A0_free (S.arMeshData b) v₀ hF⟩

end MultiplicativeBasisDeformations
