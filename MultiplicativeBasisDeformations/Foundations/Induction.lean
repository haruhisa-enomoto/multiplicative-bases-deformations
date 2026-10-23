module

public import MultiplicativeBasisDeformations.Foundations.Char2Basic
public import MultiplicativeBasisDeformations.Foundations.TableInduction
public import MultiplicativeBasisDeformations.Foundations.A0Lift
public import MultiplicativeBasisDeformations.Foundations.SkeletonExists

/-!
# The dimension induction (Proposition 8.3) in characteristic two

`main-theorems.tex`. The induction is run on representation-finite ray tables `T`
(Definition 3.9: `kT` is its own ray linearization). Its conclusion is the weight lifting
property of `T` (Proposition 8.3(3), in the form `hW` used by Theorem 9.1):

* a disconnected table splits into two unions of components with fewer rays;
* for a connected table, `B = kT` is basic and representation-finite; the characteristic-two
  step (`exists_normedRayBasis_char2`) presents `B` by the ray table `P` of its algebra `A₀`
  (Proposition 8.3(2)), and `T` presents `B` as well (`self_rayPres`); so the two tables are
  isomorphic (Lemma 3.6), `P` is connected, and its weights lift by Proposition 7.2.

Corollary 10.5 enters the characteristic-two step and itself uses the induction hypothesis
(through Lemma 9.2 and Theorem 9.1); here it is the hypothesis `Cor105Hyp`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Weight lifting for every representation-finite ray table with fewer than `n` rays. -/
def LiftBelow (n : ℕ) : Prop :=
  ∀ (V R L : Type) [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
    (T : RaySys.Tab V R L), Fintype.card R < n → IsRepresentationFinite k (T.Lin k) → T.Lift2

/-- **Corollary 10.5 under the induction hypothesis**, for every basic representation-finite
algebra. -/
def Cor105Hyp : Prop :=
  ∀ (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ],
    IsBasicAlgebra A → IsRepresentationFinite k A → LiftBelow k (Module.finrank k A) →
      ∀ (S : IndSkeleton k A) (b : S.ArrowBases), S.Cor105AR b

variable {k}

theorem ne_zero_of_complete {B : Type u} [Ring B] [Nontrivial B] {n : ℕ} {e : Fin n → B}
    (he : CompleteOrthogonalIdempotents e) : n ≠ 0 := by
  rintro rfl
  have := he.complete
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

/-- **The connected case of the induction.** -/
theorem lift2_conn (h2 : (2 : k) = 0) (hcor : Cor105Hyp k) {V R L : Type} [AddCommGroup L]
    [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (T : RaySys.Tab V R L)
    (hfin : IsRepresentationFinite k (T.Lin k)) (hc : T.Conn) (hV : Nonempty V)
    (hIH : LiftBelow k (Fintype.card R)) : T.Lift2 := by
  classical
  haveI : IsNoetherianRing (T.Lin k)ᵐᵒᵖ := IsNoetherianRing.of_finite k (T.Lin k)ᵐᵒᵖ
  haveI : Nontrivial (T.Lin k) := ⟨⟨T.b k (T.e hV.some), 0, RaySys.Mult.b_ne_zero _ k _⟩⟩
  obtain ⟨S⟩ := exists_indSkeleton hfin
  obtain ⟨b⟩ := S.nonempty_arrowBases
  have hbasic := T.isBasic_lin k
  obtain ⟨n, e, he, hprim, hbas⟩ := hbasic
  have hfr : Module.finrank k (T.Lin k) = Fintype.card R :=
    Module.finrank_eq_card_basis (T.basis k)
  have hcorAR := hcor (T.Lin k) (T.isBasic_lin k) hfin (by rw [hfr]; exact hIH) S b
  obtain ⟨v₀, hF, F1, -, -, -, ι1, β1, hpres1⟩ :=
    S.exists_normedRayBasis_char2 b h2 hfin he hprim hbas (ne_zero_of_complete he) hcorAR
  set Ssys := T.toSys k hfin
  have hpres2 := Ssys.self_rayPres k hfin
  obtain ⟨ψ, σ, hψ⟩ := exists_algEquiv_idempotents (k := k)
    (Ssys.P.isBasic_lin k) (Ssys.fibreIdem k hfin 0 (LinearEquiv.refl k _) (Ssys.self_hΨ k)) F1
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

theorem LiftBelow.mono {m n : ℕ} (h : LiftBelow k n) (hmn : m ≤ n) : LiftBelow k m :=
  fun V R L _ _ _ _ _ T hT hfin ↦ h V R L T (lt_of_lt_of_le hT hmn) hfin

/-- **Proposition 8.3(3) for all representation-finite ray tables**, by strong induction on
the number of rays, given Corollary 10.5 under the induction hypothesis. -/
theorem lift2_all (h2 : (2 : k) = 0) (hcor : Cor105Hyp k) (n : ℕ) : LiftBelow k n := by
  induction n with
  | zero => intro V R L _ _ _ _ _ T hT; omega
  | succ n ih =>
    intro V R L _ _ _ _ _ T hT hfin
    classical
    by_cases hV : Nonempty V
    · by_cases hc : T.Conn
      · exact lift2_conn h2 hcor T hfin hc hV (ih.mono (by omega))
      · obtain ⟨C, hC, hxC, hx⟩ := RaySys.Tab.exists_split hc
        have hx' : ∃ x, ¬ ¬ C x := by
          obtain ⟨y, hy⟩ := hxC
          exact ⟨y, not_not.2 hy⟩
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

/-- **Normed multiplicative ray bases of basic algebras in characteristic two**, given
Corollary 10.5 (Proposition 8.3(1)). -/
theorem exists_normedRayBasis_basic_char2 (h2 : (2 : k) = 0) (hcor : Cor105Hyp k)
    (A : Type u) [Ring A] [Algebra k A] [FiniteDimensional k A] (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (hn : Nontrivial A) :
    ∃ (F : PrimitiveIdempotents A) (bF : Module.Basis (F.NonzeroRay k) k A),
      IsNormedMultiplicativeBasis bF ∧ F.IsRayTransversal bF := by
  haveI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  obtain ⟨S⟩ := exists_indSkeleton hA
  obtain ⟨b⟩ := S.nonempty_arrowBases
  have hbasic' := hbasic
  obtain ⟨n, e, he, hprim, hbas⟩ := hbasic'
  obtain ⟨-, -, F, bF, hnorm, htr, -⟩ := S.exists_normedRayBasis_char2 b h2 hA he hprim hbas
    (ne_zero_of_complete he) (hcor A hbasic hA (lift2_all h2 hcor _) S b)
  exact ⟨F, bF, hnorm, htr⟩

end MultiplicativeBasisDeformations
