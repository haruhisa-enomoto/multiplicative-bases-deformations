import MultiplicativeBasisDeformations.Statements.MainTheorems

/-!
# Theorem 11.8(1): initial forms identify `ray A` with `ray A₀`

`main-theorems.tex` (`thm:final-standardness`(1)): for a basic representation-finite `A`,
in every characteristic, "initial forms identify `ray A` with `ray A₀`. In particular `ray A`
is associative, `A₀ ≅ k ray A` is representation-finite".

We state the identification as a ray presentation of `A` by the ray table of `A₀`
(`rayA_eq_rayA0`): the table is associative by construction, its linearization is `A₀`
(`thetaA0`), and `A₀` is representation-finite (Proposition 2.10). In characteristic two the
presentation is Proposition 8.3(2) (`exists_normedRayBasis_char2`); otherwise `A ≅ A₀`
(Theorem B with Corollary 4.15) and the fibre presentation of Proposition 11.3(3) with zero
correction (`exists_rayPres_A0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

/-! ### Two ray presentations of one algebra have isomorphic tables -/

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {B : Type u} [Ring B] [Algebra k B]
  [FiniteDimensional k B] {F : PrimitiveIdempotents B} {V R V' R' : Type} {T : RaySys.Mult V R}
  {T' : RaySys.Mult V' R'} {ι : V ≃ Fin F.m} {ι' : V' ≃ Fin F.m} {β : R → B} {β' : R' → B}

/-- **Lemma 3.6, as an isomorphism of tables**: two ray presentations of one
representation-finite algebra have isomorphic tables. -/
theorem IsRayPres.exists_tableIso (hB : IsRepresentationFinite k B)
    (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β') :
    ∃ (m : R ≃ R') (ν : V ≃ V'), (∀ r s, T'.mul (m r) (m s) = (T.mul r s).map m) ∧
      ∀ x, m (T.e x) = T'.e (ν x) := by
  let m : R ≃ R' := ⟨h.matchFn h', h'.matchFn h, h.matchFn_left_inv h', h'.matchFn_left_inv h⟩
  let ν : V ≃ V' := ι.trans ι'.symm
  have hmul : ∀ r s, T'.mul (m r) (m s) = (T.mul r s).map m := by
    intro r s
    cases hrs : T.mul r s with
    | some t =>
      exact h.mul_iff hB h' (h.matchFn_spec h' r) (h.matchFn_spec h' s) (h.matchFn_spec h' t) hrs
    | none =>
      cases h2 : T'.mul (m r) (m s) with
      | none => rfl
      | some t' =>
        exfalso
        have := h'.mul_iff hB h (h'.matchFn_spec h (m r)) (h'.matchFn_spec h (m s))
          (h'.matchFn_spec h t') h2
        change T.mul (h'.matchFn h (h.matchFn h' r)) (h'.matchFn h (h.matchFn h' s)) = _ at this
        rw [h.matchFn_left_inv h', h.matchFn_left_inv h', hrs] at this
        cases this
  refine ⟨m, ν, hmul, fun x ↦ ?_⟩
  have htg : T'.tgt (m (T.e x)) = ν x := by
    have := (h.matchFn_spec h' (T.e x)).2.1
    rw [T.tgt_e] at this
    apply ι'.injective
    change ι' (T'.tgt (h.matchFn h' (T.e x))) = _
    rw [this]
    simp [ν]
  have hr₀ : T.src (m.symm (T'.e (ν x))) = x := by
    have := (h'.matchFn_spec h (T'.e (ν x))).1
    rw [T'.src_e] at this
    apply ι.injective
    change ι (T.src (h'.matchFn h (T'.e (ν x)))) = _
    rw [this]
    simp [ν]
  have h1 := hmul (T.e x) (m.symm (T'.e (ν x)))
  have h2 := T.e_mul (m.symm (T'.e (ν x)))
  rw [hr₀] at h2
  rw [h2, Option.map_some, Equiv.apply_symm_apply] at h1
  have h3 := T'.mul_e (m (T.e x))
  rw [htg, h1] at h3
  exact (Option.some_injective _ h3).symm

end PrimitiveIdempotents

/-! ### Definition 3.9 -/

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] (F : PrimitiveIdempotents A)

/-- **Representative independence of the ray products** (Definition 3.9(3)); for a
representation-finite algebra this is Lemma 3.6 (`rayProductIndependent_of`). -/
def RayProductIndependent : Prop :=
  ∀ ⦃x y z : Fin F.m⦄ ⦃f f' h h' : A⦄, f ∈ F.corner (k := k) x y → f ≠ 0 →
    h ∈ F.corner (k := k) y z → h ≠ 0 → f' ∈ F.ray (k := k) x y f →
      h' ∈ F.ray (k := k) y z h →
      (f * h ∈ F.insertionSpan (k := k) x y z f h ↔
          f' * h' ∈ F.insertionSpan (k := k) x y z f' h') ∧
        (f * h ∉ F.insertionSpan (k := k) x y z f h →
          f' * h' ≠ 0 ∧ F.ray (k := k) x z (f * h) = F.ray (k := k) x z (f' * h'))

theorem rayProductIndependent_of [IsAlgClosed k] [FiniteDimensional k A]
    (hA : IsRepresentationFinite k A) : F.RayProductIndependent (k := k) :=
  fun _ _ _ _ _ _ _ hf hf0 hh hh0 hf' hh' ↦
    F.rayProduct_independent_of hA hf hf0 hh hh0 hf' hh'

/-- A middle-radical insertion `M(f, g)` with `f ∈ A(x, y)`, `g ∈ A(y, x)` lies in `rad R_x`. -/
theorem insertionSpan_le_cornerRadical [IsAlgClosed k] [FiniteDimensional k A] {x y : Fin F.m} {f g : A} (hf : f ∈ F.corner (k := k) x y)
    (hg : g ∈ F.corner (k := k) y x) :
    F.insertionSpan (k := k) x y x f g ≤ F.cornerRadical (k := k) x := by
  rw [insertionSpan, Submodule.span_le]
  rintro _ ⟨a, ha, r, hr, b, hb, rfl⟩
  refine ⟨F.corner_mul_corner (F.corner_mul_corner (F.corner_mul_corner
    (F.corner_mul_corner ha hf) hr.1) hg) hb, ?_⟩
  change a * f * r * g * b ∈ Ring.jacobson A
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
    ((Ring.jacobson A).mul_mem_left (a * f) hr.2))

end PrimitiveIdempotents

namespace RaySys.Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (T : Mult V R)

/-- The category with zero is skeletal: inverse morphisms are endomorphisms. -/
def IsSkeletal : Prop :=
  ∀ r s, T.mul r s = some (T.e (T.src r)) → T.mul s r = some (T.e (T.src s)) → T.src r = T.src s

variable (k : Type u) [Field k]

/-- **Definition 3.9(3)**: `Q` is a finite ray category: a finite skeletal category with zero
whose identity vectors in `kQ` are primitive, whose ray products in `kQ` are
representative-independent, and which `r ↦ [r]` identifies with the ray table of `kQ`. -/
def IsFiniteRayCategory : Prop :=
  T.IsSkeletal ∧ ∃ (F : PrimitiveIdempotents (T.Lin k)) (ι : V ≃ Fin F.m),
    (∀ x, F.e (ι x) = T.b k (T.e x)) ∧ F.RayProductIndependent (k := k) ∧
      F.IsRayPres (k := k) T ι (T.b k)

variable {T k} [IsAlgClosed k]

/-- In a ray presentation of `kQ` by `Q`, an inverse pair `f g = e_i` has identity ray
product. -/
theorem mul_eq_e_of_inverse {F : PrimitiveIdempotents (T.Lin k)} {ι : V ≃ Fin F.m}
    (hFe : ∀ x, F.e (ι x) = T.b k (T.e x)) (hind : F.RayProductIndependent (k := k))
    (hP : F.IsRayPres (k := k) T ι (T.b k)) {i j : Fin F.m} {f g : T.Lin k}
    (hf : f ∈ F.corner (k := k) i j) (hg : g ∈ F.corner (k := k) j i) (hfg : f * g = F.e i)
    {r s : R} (hr : ι (T.src r) = i ∧ ι (T.tgt r) = j ∧ f ∈ F.ray (k := k) i j (T.b k r))
    (hs : ι (T.src s) = j ∧ ι (T.tgt s) = i ∧ g ∈ F.ray (k := k) j i (T.b k s)) :
    T.mul r s = some (T.e (T.src r)) := by
  have he0 : F.e i ≠ 0 := (F.primitive i).2.1
  have hf0 : f ≠ 0 := by rintro rfl; rw [zero_mul] at hfg; exact he0 hfg.symm
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hfg; exact he0 hfg.symm
  have hcr : T.b k r ∈ F.corner (k := k) i j := by rw [← hr.1, ← hr.2.1]; exact hP.corner r
  have hcs : T.b k s ∈ F.corner (k := k) j i := by rw [← hs.1, ← hs.2.1]; exact hP.corner s
  have hr' : T.b k r ∈ F.ray (k := k) i j f := F.ray_symm hcr hr.2.2
  have hs' : T.b k s ∈ F.ray (k := k) j i g := F.ray_symm hcs hs.2.2
  -- `f g = e_i ∉ M(f, g) ⊆ rad R_i`
  have hM : f * g ∉ F.insertionSpan (k := k) i j i f g := fun h ↦
    F.e_not_mem_radical (k := k) i (by
      rw [← hfg]; exact (F.insertionSpan_le_cornerRadical hf hg h).2)
  obtain ⟨hiff, hray⟩ := hind hf hf0 hg hg0 hr' hs'
  have hM' : T.b k r * T.b k s ∉ F.insertionSpan (k := k) i j i (T.b k r) (T.b k s) :=
    fun h ↦ hM (hiff.2 h)
  obtain ⟨-, hrayeq⟩ := hray hM
  have hmid : T.tgt r = T.src s := ι.injective (hr.2.1.trans hs.1.symm)
  cases ht : T.mul r s with
  | none =>
    exfalso
    have := hP.mul_none r s ht hmid
    rw [hr.1, hr.2.1, hs.2.1] at this
    exact hM' this
  | some t =>
    congr 1
    obtain ⟨-, hbt⟩ := hP.mul_some r s t ht
    have hst : T.src t = T.src r := T.mul_src r s t ht
    have htt : T.tgt t = T.tgt s := T.mul_tgt r s t ht
    rw [hst, htt, hr.1, hs.2.1] at hbt
    have hcb : T.b k t ∈ F.corner (k := k) i i := by
      have := hP.corner t
      rwa [hst, htt, hr.1, hs.2.1] at this
    have h1 : F.ray (k := k) i i (T.b k r * T.b k s) = F.ray (k := k) i i (T.b k t) :=
      F.ray_eq_of_mem hcb hbt
    have h2 : F.e i ∈ F.ray (k := k) i i (T.b k t) := by
      rw [← h1, ← hrayeq, hfg]
      exact F.mem_ray_self (F.e_mem_corner i)
    have h3 : T.b k (T.e (T.src r)) ∈ F.ray (k := k) (ι (T.src t)) (ι (T.tgt t)) (T.b k t) := by
      rw [← hFe, hst, htt, hr.1, hs.2.1]
      exact h2
    exact (hP.inj _ _ h3).symm

/-- **The linearization of a finite ray category is basic** (proof of Theorem 11.8). -/
theorem isBasic_of_isFiniteRayCategory (hQ : T.IsFiniteRayCategory k) :
    IsBasicAlgebra (T.Lin k) := by
  obtain ⟨hsk, F, ι, hFe, hind, hP⟩ := hQ
  refine ⟨F.m, F.e, F.complete, F.primitive, fun i j ⟨x, y, hx, hy, hxy, hyx⟩ ↦ ?_⟩
  by_contra hij
  have hxc : x ∈ F.corner (k := k) i j := F.mem_corner_iff'.2 hx
  have hyc : y ∈ F.corner (k := k) j i := F.mem_corner_iff'.2 hy
  have he0 : F.e i ≠ 0 := (F.primitive i).2.1
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hxy; exact he0 hxy.symm
  have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hxy; exact he0 hxy.symm
  obtain ⟨r, hr1, hr2, hr3⟩ := hP.surj i j x hxc hx0
  obtain ⟨s, hs1, hs2, hs3⟩ := hP.surj j i y hyc hy0
  have h1 := mul_eq_e_of_inverse hFe hind hP hxc hyc hxy ⟨hr1, hr2, hr3⟩ ⟨hs1, hs2, hs3⟩
  have h2 := mul_eq_e_of_inverse hFe hind hP hyc hxc hyx ⟨hs1, hs2, hs3⟩ ⟨hr1, hr2, hr3⟩
  exact hij (hr1.symm.trans ((congrArg ι (hsk r s h1 h2)).trans hs1))

end RaySys.Mult

namespace MeshWalk

attribute [local instance] Classical.decEq

open CatAlg

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

/-- **An algebra isomorphic to `A₀` is presented by the ray table of `A₀`.** -/
theorem exists_rayPres_of_algEquiv {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
    (φ : B ≃ₐ[k] (Alg D.F0)ᵐᵒᵖ) :
    ∃ (F : PrimitiveIdempotents B) (ι : D.PV ≃ Fin F.m) (β : RayA0 D v₀ → B),
      F.IsRayPres (k := k) (A0Mult D v₀ hF) ι β := by
  let Sy := A0Sys (k := k) D v₀ hF
  have hfin := A0Tab_isRepresentationFinite D v₀ hF
  let Ψ := ((thetaA0 D v₀ hF).trans φ.symm).toLinearEquiv
  have hΨ : ∀ a z, Ψ (a * z + Sy.coch k 0 a z) = Ψ a * Ψ z := by
    intro a z
    have h0 : Sy.coch k 0 a z = 0 := by
      rw [RaySys.Sys.coch_zero]
      rfl
    rw [h0, add_zero]
    exact map_mul ((thetaA0 D v₀ hF).trans φ.symm) a z
  exact ⟨_, _, _, Sy.fibre_rayPres k hfin 0 Ψ hΨ⟩

end MeshWalk

namespace IndSkeleton

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- **An algebra isomorphic to `A₀` is presented by the ray table of `A₀`.** -/
theorem exists_rayPres_A0 (φ : A ≃ₐ[k] S.A0 b) (v₀ : S.ARVertex)
    (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ) :
    ∃ (F : PrimitiveIdempotents A) (ι : (S.arMeshData b).PV ≃ Fin F.m)
      (β : S.rayA0AR b v₀ → A), F.IsRayPres (k := k) (S.A0MultAR b v₀ hF) ι β := by
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  exact MeshWalk.exists_rayPres_of_algEquiv (S.arMeshData b) v₀ hF φ

end IndSkeleton

/-- **Theorem 11.8(1)** (`thm:final-standardness`): in every characteristic, a basic
representation-finite algebra is presented by the ray table of its algebra `A₀`
(the initial-form identification `ray A = ray A₀`); `A₀ ≅ k ray A₀` and `A₀` is
representation-finite. -/
theorem rayA_eq_rayA0 (k : Type u) [Field k] [IsAlgClosed k] (A : Type u) [Ring A] [Algebra k A]
    [FiniteDimensional k A] (hbasic : IsBasicAlgebra A) (hA : IsRepresentationFinite k A)
    (hn : Nontrivial A) :
    letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
    ∀ S : IndSkeleton k A, ∃ (b : S.ArrowBases) (v₀ : S.ARVertex)
      (hF : IsRepresentationFinite k (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ)
      (F : PrimitiveIdempotents A) (ι : (S.arMeshData b).PV ≃ Fin F.m)
      (β : S.rayA0AR b v₀ → A), F.IsRayPres (k := k) (S.A0MultAR b v₀ hF) ι β := by
  letI : IsNoetherianRing Aᵐᵒᵖ := IsNoetherianRing.of_finite k Aᵐᵒᵖ
  intro S
  classical
  obtain ⟨n, e, he, hprim, hbas⟩ := id hbasic
  by_cases hchar : ringChar k = 2
  · haveI : CharP k 2 := ringChar.of_eq hchar
    obtain ⟨b⟩ := S.nonempty_arrowBases
    obtain ⟨v₀, hF, F, -, -, -, ι, β, h⟩ := S.exists_normedRayBasis_char2 b
      CharTwo.two_eq_zero hA he hprim hbas (ne_zero_of_complete he)
      ((cor105Hyp k) A hbasic hA (lift2_all CharTwo.two_eq_zero (cor105Hyp k) _) S b)
    exact ⟨b, v₀, hF, F, ι, β, h⟩
  · obtain ⟨b, Φ0, hEq, hlin, hβ⟩ := theoremB k A hbasic hA hchar S
    haveI := hEq
    haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
    haveI : ∀ x y : S.ARVertex, FiniteDimensional k
        (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
          MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
      fun x y ↦ S.finiteDimensional_meshHom b x y
    have hn0 : n ≠ 0 := ne_zero_of_complete he
    let v₀ : S.ARVertex := ((S.pvEquiv b he hprim hbas).symm ⟨0, Nat.pos_of_ne_zero hn0⟩).1
    have hF := CatAlg.MeshData.isRepresentationFinite_A0 (S.arInjData b)
    let φ := S.algEquivA0 b he hprim hbas Φ0 hlin fun x ↦ (hβ x).some
    obtain ⟨F, ι, β, h⟩ := S.exists_rayPres_A0 b φ v₀ hF
    exact ⟨b, v₀, hF, F, ι, β, h⟩

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys.Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] {T : Mult V R}
  {k : Type u} [Field k] [IsAlgClosed k]

/-- **Theorem 11.8(3), standardness**: the linearization of a finite ray category `Q` with
`kQ` representation-finite is standard, in every characteristic. By Theorem 11.8(1) `kQ` is
presented by the ray table of its `A₀`; by Definition 3.9 it is presented by `Q`; Lemma 3.6
identifies the two tables, so `kQ ≅ A₀`, and the converse of Corollary 4.15 applies. -/
theorem isStandard_of_isFiniteRayCategory (hQ : T.IsFiniteRayCategory k)
    (hfin : IsRepresentationFinite k (T.Lin k)) : IsStandard k (T.Lin k) := by
  have hbasic := isBasic_of_isFiniteRayCategory hQ
  letI : IsNoetherianRing (T.Lin k)ᵐᵒᵖ := IsNoetherianRing.of_finite k (T.Lin k)ᵐᵒᵖ
  intro S
  rcases subsingleton_or_nontrivial (T.Lin k) with hs | hn
  · exact S.isStandard_of_subsingleton
  obtain ⟨b, v₀, hF, F₁, ι₁, β₁, h₁⟩ := rayA_eq_rayA0 k (T.Lin k) hbasic hfin hn S
  obtain ⟨-, F, ι, -, -, hP⟩ := hQ
  obtain ⟨ψ', σ, hψ'⟩ := exists_algEquiv_idempotents (k := k) hbasic F F₁
  have hP₁ := hP.map ψ' F₁ σ hψ'
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  obtain ⟨m, ν, hmul, he⟩ := hP₁.exists_tableIso hfin h₁
  exact S.isStandard_of_algEquiv b
    ((Classical.choice (RaySys.nonempty_algEquiv_of_match' T (S.A0MultAR b v₀ hF) m ν hmul he
      k)).trans (MeshWalk.thetaA0 (S.arMeshData b) v₀ hF))

end RaySys.Mult

end MultiplicativeBasisDeformations

/-! ### The scalar-weight group of a table (Definition 7.1) -/

namespace MultiplicativeBasisDeformations

namespace RaySys.Mult

variable {V R : Type} (T : Mult V R)

/-- The relations of `W(Q)`: `[rs] - [r] - [s]` for `rs ≠ 0`, and the identity symbols. -/
def wRel : AddSubgroup (R →₀ ℤ) := AddSubgroup.closure
  ({w | ∃ r s t, T.mul r s = some t ∧
      w = Finsupp.single t 1 - Finsupp.single r 1 - Finsupp.single s 1} ∪
    {w | ∃ x, w = Finsupp.single (T.e x) 1})

/-- **Definition 7.1**: the scalar-weight group
`W(Q) = ℤ⟨[r]⟩ / ⟨[rs] - [r] - [s] : rs ≠ 0⟩`, identity symbols being zero. -/
abbrev W := (R →₀ ℤ) ⧸ T.wRel

/-- The class `[r]`. -/
def wCls (r : R) : T.W := QuotientAddGroup.mk (Finsupp.single r 1)

theorem wCls_mul {r s t : R} (h : T.mul r s = some t) : T.wCls t = T.wCls r + T.wCls s := by
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  change (QuotientAddGroup.mk (Finsupp.single t 1 - Finsupp.single r 1 - Finsupp.single s 1) :
    T.W) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (Or.inl ⟨r, s, t, h, rfl⟩)

theorem wCls_e (x : V) : T.wCls (T.e x) = 0 := by
  change (QuotientAddGroup.mk (Finsupp.single (T.e x) 1) : T.W) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (Or.inr ⟨x, rfl⟩)

theorem mk_single (r : R) (n : ℤ) :
    (QuotientAddGroup.mk (Finsupp.single r n) : T.W) = n • T.wCls r := by
  rw [wCls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Homomorphisms out of `W(Q)` are additive weights. -/
def wLift {M : Type*} [AddCommGroup M] (φ : R → M)
    (hmul : ∀ r s t, T.mul r s = some t → φ t = φ r + φ s) (he : ∀ x, φ (T.e x) = 0) :
    T.W →+ M :=
  QuotientAddGroup.lift _ (Finsupp.liftAddHom fun r ↦ zmultiplesHom M (φ r)) (by
    rw [wRel, AddSubgroup.closure_le]
    rintro w (⟨r, s, t, h, rfl⟩ | ⟨x, rfl⟩)
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, Finsupp.liftAddHom_apply_single,
        zmultiplesHom_apply, one_smul, hmul r s t h]
      abel
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Finsupp.liftAddHom_apply_single,
        zmultiplesHom_apply, one_smul, he x])

theorem wLift_cls {M : Type*} [AddCommGroup M] (φ : R → M)
    (hmul : ∀ r s t, T.mul r s = some t → φ t = φ r + φ s) (he : ∀ x, φ (T.e x) = 0) (r : R) :
    T.wLift φ hmul he (T.wCls r) = φ r := by
  simp [wLift, wCls]

theorem W.hom_ext {M : Type*} [AddCommGroup M] {f g : T.W →+ M}
    (h : ∀ r, f (T.wCls r) = g (T.wCls r)) : f = g := by
  refine QuotientAddGroup.addMonoidHom_ext _ (Finsupp.addHom_ext fun r n ↦ ?_)
  change f (QuotientAddGroup.mk _) = g (QuotientAddGroup.mk _)
  rw [mk_single, map_zsmul, map_zsmul, h]

variable {T} {V' R' : Type} {T' : Mult V' R'}

/-- **Isomorphic tables have isomorphic scalar-weight groups.** -/
def wEquiv (m : R ≃ R') (ν : V ≃ V') (hmul : ∀ r s, T'.mul (m r) (m s) = (T.mul r s).map m)
    (he : ∀ x, m (T.e x) = T'.e (ν x)) : T.W ≃+ T'.W := by
  have hmul' : ∀ r' s', T.mul (m.symm r') (m.symm s') = (T'.mul r' s').map m.symm := by
    intro r' s'
    have := hmul (m.symm r') (m.symm s')
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    rw [this, Option.map_map, Equiv.symm_comp_self, Option.map_id, id]
  have he' : ∀ x', m.symm (T'.e x') = T.e (ν.symm x') := by
    intro x'
    rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply]
  let f : T.W →+ T'.W := T.wLift (fun r ↦ T'.wCls (m r)) (fun r s t h ↦ by
      have := hmul r s
      rw [h, Option.map_some] at this
      exact T'.wCls_mul this) (fun x ↦ by simp only [he, wCls_e])
  let g : T'.W →+ T.W := T'.wLift (fun r' ↦ T.wCls (m.symm r')) (fun r s t h ↦ by
      have := hmul' r s
      rw [h, Option.map_some] at this
      exact T.wCls_mul this) (fun x ↦ by simp only [he', wCls_e])
  have hgf : g.comp f = AddMonoidHom.id _ := W.hom_ext T fun r ↦ by
    simp [f, g, wLift_cls]
  have hfg : f.comp g = AddMonoidHom.id _ := W.hom_ext T' fun r ↦ by
    simp [f, g, wLift_cls]
  exact AddEquiv.ofBijective f ⟨fun a b hab ↦ by
    have := congrArg g hab
    rwa [← AddMonoidHom.comp_apply, hgf, ← AddMonoidHom.comp_apply, hgf] at this,
    fun b ↦ ⟨g b, by rw [← AddMonoidHom.comp_apply, hfg, AddMonoidHom.id_apply]⟩⟩

end RaySys.Mult

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open CategoryTheory CatAlg

attribute [local instance] Classical.decEq Classical.propDecidable

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

include hF in
theorem nz_of_deckV_ne {x y : D.PV} {g : Deck Q v₀} (h : deckV D v₀ hF x y g ≠ 0) :
    NZ Q c v₀ D (x, y, g) := by
  intro hb
  apply h
  have := deckV_mem D v₀ hF x y g
  rw [hb, Submodule.mem_bot] at this
  exact this

/-- A nonzero product of deck vectors is a product in the table of `A₀`. -/
theorem A0Mult_mul_of {x y z : D.PV} {g h : Deck Q v₀}
    (hne : deckV D v₀ hF x y g ≫ deckV D v₀ hF y z h ≠ 0) :
    (A0Mult D v₀ hF).mul
        ⟨(y, z, h), nz_of_deckV_ne hF (fun h0 ↦ hne (by rw [h0, Limits.comp_zero]))⟩
        ⟨(x, y, g), nz_of_deckV_ne hF (fun h0 ↦ hne (by rw [h0, Limits.zero_comp]))⟩ =
      some ⟨(x, z, g * h), nz_of_deckV_ne hF (by
        rcases deckV_mul D v₀ hF x y z g h with h0 | h1
        · exact absurd h0 hne
        · rw [← h1]; exact hne)⟩ := by
  apply (RaySys.OfBasis.mulB_eq_some _).2
  rw [basisR_apply, basisR_apply, basisR_apply, ← MulOpposite.op_mul, unitM_mul]
  congr 2
  rcases deckV_mul D v₀ hF x y z g h with h0 | h1
  · exact absurd h0 hne
  · exact h1

/-- **`W(ray A₀) = W(P)`**: the scalar-weight group of the table of `A₀` is the group `WP`
of deck pieces. -/
def wA0Equiv : (A0Mult D v₀ hF).W ≃+ WP Q c v₀ D := by
  have hcls_e : ∀ x, cls Q c v₀ D ((A0Mult D v₀ hF).e x).1 = 0 := by
    intro x
    have h := cls_mul_A0 D v₀ hF ((A0Mult D v₀ hF).e_mul ((A0Mult D v₀ hF).e x))
    rw [(A0Mult D v₀ hF).src_e] at h
    simpa using h
  let f : (A0Mult D v₀ hF).W →+ WP Q c v₀ D := (A0Mult D v₀ hF).wLift
    (fun t ↦ cls Q c v₀ D t.1) (fun r s t h ↦ cls_mul_A0 D v₀ hF h) hcls_e
  let g : WP Q c v₀ D →+ (A0Mult D v₀ hF).W := QuotientAddGroup.lift _
    (Finsupp.liftAddHom fun t ↦ if h : NZ Q c v₀ D t then
      zmultiplesHom _ ((A0Mult D v₀ hF).wCls ⟨t, h⟩) else 0) (by
    rw [relW, AddSubgroup.closure_le]
    rintro w (⟨x, y, z, g, h, φ, φ', hφ, hφ', hφφ, rfl⟩ | ⟨t, ht, rfl⟩)
    · obtain ⟨a, rfl⟩ := deckV_span D v₀ hF x y g φ hφ
      obtain ⟨a', rfl⟩ := deckV_span D v₀ hF y z h φ' hφ'
      have hne : deckV D v₀ hF x y g ≫ deckV D v₀ hF y z h ≠ 0 := by
        intro h0
        apply hφφ
        rw [Linear.smul_comp, Linear.comp_smul, h0, smul_zero, smul_zero]
      have hm := (A0Mult D v₀ hF).wCls_mul (A0Mult_mul_of hF hne)
      have h1 : NZ Q c v₀ D (x, y, g) :=
        nz_of_deckV_ne hF (fun h0 ↦ hne (by rw [h0, Limits.zero_comp]))
      have h2 : NZ Q c v₀ D (y, z, h) :=
        nz_of_deckV_ne hF (fun h0 ↦ hne (by rw [h0, Limits.comp_zero]))
      have h3 : NZ Q c v₀ D (x, z, g * h) := nz_of_deckV_ne hF (by
        rcases deckV_mul D v₀ hF x y z g h with h0 | h1
        · exact absurd h0 hne
        · rw [← h1]; exact hne)
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, Finsupp.liftAddHom_apply_single,
        dif_pos h1, dif_pos h2, dif_pos h3, zmultiplesHom_apply, one_smul]
      rw [hm]
      abel
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Finsupp.liftAddHom_apply_single,
        dif_neg ht, AddMonoidHom.zero_apply])
  have hg : ∀ t n, g (QuotientAddGroup.mk (Finsupp.single t n)) =
      if h : NZ Q c v₀ D t then n • (A0Mult D v₀ hF).wCls ⟨t, h⟩ else 0 := by
    intro t n
    change (Finsupp.liftAddHom fun t ↦ if h : NZ Q c v₀ D t then
      zmultiplesHom _ ((A0Mult D v₀ hF).wCls ⟨t, h⟩) else 0) (Finsupp.single t n) = _
    rw [Finsupp.liftAddHom_apply_single]
    split_ifs <;> simp
  have hmk : ∀ t n, (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) =
      n • cls Q c v₀ D t := fun t n ↦ by
    rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hgf : g.comp f = AddMonoidHom.id _ := RaySys.Mult.W.hom_ext _ fun r ↦ by
    simp only [AddMonoidHom.comp_apply, f, RaySys.Mult.wLift_cls, AddMonoidHom.id_apply]
    change g (QuotientAddGroup.mk (Finsupp.single r.1 1)) = _
    rw [hg, dif_pos (show NZ Q c v₀ D r.1 from r.2), one_smul]
  have hfg : f.comp g = AddMonoidHom.id _ := by
    refine QuotientAddGroup.addMonoidHom_ext _ (Finsupp.addHom_ext fun t n ↦ ?_)
    change f (g (QuotientAddGroup.mk (Finsupp.single t n))) = QuotientAddGroup.mk (Finsupp.single t n)
    rw [hg, hmk]
    by_cases ht : NZ Q c v₀ D t
    · rw [dif_pos ht, map_zsmul, RaySys.Mult.wLift_cls]
    · rw [dif_neg ht, map_zero, cls_of_not_nz ht, smul_zero]
  exact AddEquiv.ofBijective f ⟨fun a b hab ↦ by
    have := congrArg g hab
    rwa [← AddMonoidHom.comp_apply, hgf, ← AddMonoidHom.comp_apply, hgf] at this,
    fun b ↦ ⟨g b, by rw [← AddMonoidHom.comp_apply, hfg, AddMonoidHom.id_apply]⟩⟩

end MeshWalk

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys.Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] {T : Mult V R}
  {k : Type u} [Field k] [IsAlgClosed k]

/-- **`W(Q)` is free for a connected table presenting its own representation-finite basic
linearization**: `Q` is identified with the ray table of `A₀`, whose scalar-weight group is free
(Proposition 7.2(1)). -/
theorem W_free_of_rayPres (hbasic : IsBasicAlgebra (T.Lin k))
    (hfin : IsRepresentationFinite k (T.Lin k)) (r₀ : R) {F : PrimitiveIdempotents (T.Lin k)}
    {ι : V ≃ Fin F.m} (hP : F.IsRayPres (k := k) T ι (T.b k)) (hc : T.Conn) :
    Module.Free ℤ T.W := by
  classical
  letI : IsNoetherianRing (T.Lin k)ᵐᵒᵖ := IsNoetherianRing.of_finite k (T.Lin k)ᵐᵒᵖ
  haveI hn : Nontrivial (T.Lin k) := ⟨⟨T.b k r₀, 0, Mult.b_ne_zero _ k _⟩⟩
  obtain ⟨S⟩ := exists_indSkeleton hfin
  obtain ⟨b, v₀, hF, F₁, ι₁, β₁, h₁⟩ := rayA_eq_rayA0 k (T.Lin k) hbasic hfin hn S
  obtain ⟨ψ', σ, hψ'⟩ := exists_algEquiv_idempotents (k := k) hbasic F F₁
  have hP₁ := hP.map ψ' F₁ σ hψ'
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  obtain ⟨m, ν, hmul, he⟩ := hP₁.exists_tableIso hfin h₁
  have hc' : (S.A0MultAR b v₀ hF).Conn := hP₁.conn h₁ hc
  have hA0 : MeshWalk.A0Conn S.arTranslationQuiver (S.arCoefficients b) v₀ (S.arMeshData b)
      (ν (T.src r₀)) := by
    intro x
    have key : ∀ a a', Relation.EqvGen (fun x y ↦ ∃ r, (S.A0MultAR b v₀ hF).src r = x ∧
        (S.A0MultAR b v₀ hF).tgt r = y) a a' →
        Relation.EqvGen (fun x y ↦ ∃ g, MeshWalk.NZ S.arTranslationQuiver (S.arCoefficients b) v₀
          (S.arMeshData b) (x, y, g)) a a' := by
      intro a a' h
      induction h with
      | rel a a' hr =>
        obtain ⟨⟨⟨y, z, g⟩, hnz⟩, rfl, rfl⟩ := hr
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨g, hnz⟩)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
    exact key _ _ (hc' (ν (T.src r₀)) x)
  have := MeshWalk.WP_free hF hA0
  exact Module.Free.of_equiv
    ((wEquiv m ν hmul he).trans (MeshWalk.wA0Equiv hF)).symm.toIntLinearEquiv

theorem W_free_of_isEmpty [IsEmpty R] : Module.Free ℤ T.W := by
  haveI : Subsingleton T.W := ⟨fun a b ↦ by
    induction a using QuotientAddGroup.induction_on with
    | H u =>
    induction b using QuotientAddGroup.induction_on with
    | H u' => rw [Subsingleton.elim u u']⟩
  exact Module.Free.of_subsingleton ℤ T.W

end RaySys.Mult

namespace RaySys.Tab

variable {V R L : Type} [AddCommGroup L] [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R]
  {P : Tab V R L}

open Classical in
/-- **`W` splits along a union of components.** -/
def wSplit {C : V → Prop} (hC : P.Closed C) :
    P.toMult.W ≃+ (P.sub (compData hC)).toMult.W × (P.sub (compData hC.compl)).toMult.W := by
  let P₁ := (P.sub (compData hC)).toMult
  let P₂ := (P.sub (compData hC.compl)).toMult
  let φ : R → P₁.W × P₂.W := fun r ↦
    if h : C (P.src r) then (P₁.wCls ⟨r, h⟩, 0) else (0, P₂.wCls ⟨r, h⟩)
  have hφ : ∀ r s t, P.mul r s = some t → φ t = φ r + φ s := by
    intro r s t h
    have ht : P.src t = P.src r := P.mul_src r s t h
    have hs : P.src s = P.tgt r := (P.mul_mid r s t h).symm
    by_cases hr : C (P.src r)
    · have hs' : C (P.src s) := by rw [hs]; exact hC.fwd r hr
      have ht' : C (P.src t) := by rw [ht]; exact hr
      simp only [φ, dif_pos hr, dif_pos hs', dif_pos ht', Prod.mk_add_mk, add_zero]
      exact Prod.ext (P₁.wCls_mul
        ((compMul_eq_some hC (r := ⟨r, hr⟩) (s := ⟨s, hs'⟩) (t := ⟨t, ht'⟩)).2 h)) rfl
    · have hs' : ¬ C (P.src s) := fun h' ↦ hr (hC.bwd r (by rw [← hs]; exact h'))
      have ht' : ¬ C (P.src t) := by rw [ht]; exact hr
      simp only [φ, dif_neg hr, dif_neg hs', dif_neg ht', Prod.mk_add_mk, add_zero]
      exact Prod.ext rfl (P₂.wCls_mul ((compMul_eq_some hC.compl (r := ⟨r, hr⟩) (s := ⟨s, hs'⟩)
        (t := ⟨t, ht'⟩)).2 h))
  have he : ∀ x, φ (P.e x) = 0 := by
    intro x
    by_cases hx : C (P.src (P.e x))
    · simp only [φ, dif_pos hx]
      have hx' : C x := by rwa [P.src_e] at hx
      have := P₁.wCls_e ⟨x, hx'⟩
      rw [Prod.mk_eq_zero]
      exact ⟨this, rfl⟩
    · simp only [φ, dif_neg hx]
      have hx' : ¬ C x := by rwa [P.src_e] at hx
      have := P₂.wCls_e ⟨x, hx'⟩
      rw [Prod.mk_eq_zero]
      exact ⟨rfl, this⟩
  let f : P.toMult.W →+ P₁.W × P₂.W := P.toMult.wLift φ hφ he
  let g₁ : P₁.W →+ P.toMult.W := P₁.wLift (fun r ↦ P.toMult.wCls r.1)
    (fun r s t h ↦ P.toMult.wCls_mul ((compMul_eq_some hC).1 h)) (fun x ↦ P.toMult.wCls_e x.1)
  let g₂ : P₂.W →+ P.toMult.W := P₂.wLift (fun r ↦ P.toMult.wCls r.1)
    (fun r s t h ↦ P.toMult.wCls_mul ((compMul_eq_some hC.compl).1 h))
    (fun x ↦ P.toMult.wCls_e x.1)
  let g : P₁.W × P₂.W →+ P.toMult.W := g₁.coprod g₂
  have hgf : g.comp f = AddMonoidHom.id _ := Mult.W.hom_ext _ fun r ↦ by
    change g (P.toMult.wLift φ hφ he (P.toMult.wCls r)) = P.toMult.wCls r
    rw [Mult.wLift_cls]
    by_cases h : C (P.src r)
    · change g (if h : C (P.src r) then (P₁.wCls ⟨r, h⟩, 0) else (0, P₂.wCls ⟨r, h⟩)) = _
      rw [dif_pos h, AddMonoidHom.coprod_apply, map_zero, add_zero]
      exact Mult.wLift_cls _ _ _ _ _
    · change g (if h : C (P.src r) then (P₁.wCls ⟨r, h⟩, 0) else (0, P₂.wCls ⟨r, h⟩)) = _
      rw [dif_neg h, AddMonoidHom.coprod_apply, map_zero, zero_add]
      exact Mult.wLift_cls _ _ _ _ _
  have h1 : f.comp g₁ = AddMonoidHom.inl _ _ := Mult.W.hom_ext _ fun r ↦ by
    change P.toMult.wLift φ hφ he (g₁ (P₁.wCls r)) = (P₁.wCls r, 0)
    rw [show g₁ (P₁.wCls r) = P.toMult.wCls r.1 from Mult.wLift_cls _ _ _ _ _, Mult.wLift_cls]
    change (if h : C (P.src r.1) then (P₁.wCls ⟨r.1, h⟩, 0) else (0, P₂.wCls ⟨r.1, h⟩)) = _
    rw [dif_pos (show C (P.src r.1) from r.2)]
  have h2 : f.comp g₂ = AddMonoidHom.inr _ _ := Mult.W.hom_ext _ fun r ↦ by
    change P.toMult.wLift φ hφ he (g₂ (P₂.wCls r)) = (0, P₂.wCls r)
    rw [show g₂ (P₂.wCls r) = P.toMult.wCls r.1 from Mult.wLift_cls _ _ _ _ _, Mult.wLift_cls]
    change (if h : C (P.src r.1) then (P₁.wCls ⟨r.1, h⟩, 0) else (0, P₂.wCls ⟨r.1, h⟩)) = _
    rw [dif_neg (show ¬ C (P.src r.1) from r.2)]
  have hfg : ∀ a, f (g a) = a := by
    rintro ⟨a, b⟩
    simp only [g, AddMonoidHom.coprod_apply, map_add]
    rw [← AddMonoidHom.comp_apply f g₁, ← AddMonoidHom.comp_apply f g₂, h1, h2,
      AddMonoidHom.inl_apply, AddMonoidHom.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  exact AddEquiv.ofBijective f ⟨fun a b hab ↦ by
    have := congrArg g hab
    rwa [← AddMonoidHom.comp_apply, hgf, ← AddMonoidHom.comp_apply, hgf] at this,
    fun b ↦ ⟨g b, hfg b⟩⟩

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **`W` of a representation-finite ray table is free** (Proposition 8.3(3) for ray tables),
by strong induction on the number of rays, splitting along components. -/
theorem W_free (n : ℕ) : ∀ (V R L : Type) [AddCommGroup L] [Fintype V] [DecidableEq V]
    [Fintype R] [DecidableEq R] (P : Tab V R L), Fintype.card R < n →
      IsRepresentationFinite k (P.Lin k) → Module.Free ℤ P.toMult.W := by
  induction n with
  | zero => intro V R L _ _ _ _ _ P hP; omega
  | succ n ih =>
    intro V R L _ _ _ _ _ P hP hfin
    classical
    rcases isEmpty_or_nonempty R with hR | hR
    · exact Mult.W_free_of_isEmpty
    obtain ⟨r₀⟩ := hR
    by_cases hc : P.Conn
    · let S := P.toSys k hfin
      exact Mult.W_free_of_rayPres (P.isBasic_lin k) hfin r₀ (S.self_rayPres k hfin) hc
    · obtain ⟨C, hC, hxC, hx⟩ := exists_split hc
      have hx' : ∃ x, ¬ ¬ C x := by
        obtain ⟨y, hy⟩ := hxC
        exact ⟨y, not_not.2 hy⟩
      have := ih _ _ _ (P.sub (compData hC)) (by
          obtain ⟨y, hy⟩ := hx
          have := Fintype.card_subtype_lt (p := (compData hC).pR) (x := P.e y)
            (by change ¬ C (P.src (P.e y)); rw [P.src_e]; exact hy)
          exact lt_of_lt_of_le this (by omega))
        (comp_isRepresentationFinite hC k hfin)
      have := ih _ _ _ (P.sub (compData hC.compl)) (by
          obtain ⟨y, hy⟩ := hxC
          have := Fintype.card_subtype_lt (p := (compData hC.compl).pR) (x := P.e y)
            (by change ¬ ¬ C (P.src (P.e y)); rw [P.src_e]; exact not_not.2 hy)
          exact lt_of_lt_of_le this (by omega))
        (comp_isRepresentationFinite hC.compl k hfin)
      exact Module.Free.of_equiv (wSplit hC).symm.toIntLinearEquiv

end RaySys.Tab

namespace MeshWalk

open CategoryTheory CatAlg

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

/-- **`W(ray A₀)` is free**, also for disconnected `A₀`. -/
theorem W_A0_free : Module.Free ℤ (A0Mult D v₀ hF).W :=
  RaySys.Tab.W_free k _ _ _ _ (A0Tab D v₀ hF) (Nat.lt_succ_self _)
    (A0Tab_isRepresentationFinite D v₀ hF)

end MeshWalk

namespace RaySys.Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] {T : Mult V R}
  {k : Type u} [Field k] [IsAlgClosed k]

/-- **Theorem 11.8(3), freeness of `W(Q)`**: for a finite ray category `Q` with `kQ`
representation-finite, `W(Q)` is free abelian. `Q` is identified with the ray table of the
algebra `A₀` of `kQ` (Theorem 11.8(1) and Lemma 3.6), whose scalar-weight group is free. -/
theorem W_free_of_isFiniteRayCategory (hQ : T.IsFiniteRayCategory k)
    (hfin : IsRepresentationFinite k (T.Lin k)) : Module.Free ℤ T.W := by
  classical
  have hbasic := isBasic_of_isFiniteRayCategory hQ
  letI : IsNoetherianRing (T.Lin k)ᵐᵒᵖ := IsNoetherianRing.of_finite k (T.Lin k)ᵐᵒᵖ
  rcases isEmpty_or_nonempty R with hR | hR
  · exact W_free_of_isEmpty
  obtain ⟨r₀⟩ := hR
  haveI hn : Nontrivial (T.Lin k) := ⟨⟨T.b k r₀, 0, Mult.b_ne_zero _ k _⟩⟩
  obtain ⟨S⟩ := exists_indSkeleton hfin
  obtain ⟨b, v₀, hF, F₁, ι₁, β₁, h₁⟩ := rayA_eq_rayA0 k (T.Lin k) hbasic hfin hn S
  obtain ⟨-, F, ι, -, -, hP⟩ := hQ
  obtain ⟨ψ', σ, hψ'⟩ := exists_algEquiv_idempotents (k := k) hbasic F F₁
  have hP₁ := hP.map ψ' F₁ σ hψ'
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y) :=
    fun x y ↦ S.finiteDimensional_meshHom b x y
  obtain ⟨m, ν, hmul, he⟩ := hP₁.exists_tableIso hfin h₁
  have : Module.Free ℤ (S.A0MultAR b v₀ hF).W := MeshWalk.W_A0_free (S.arMeshData b) v₀ hF
  exact Module.Free.of_equiv (wEquiv m ν hmul he).symm.toIntLinearEquiv

end RaySys.Mult

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u

/-- **Theorem 11.8(3)** (`thm:final-standardness`): for every finite ray category `Q` with `kQ`
representation-finite, over an algebraically closed field of any characteristic, `W(Q)` is free
abelian and `kQ` is standard, `k(Γ_{kQ}) ≃ ind(mod kQ)`. -/
theorem finalStandardness_rayCategory (k : Type u) [Field k] [IsAlgClosed k] {V R : Type}
    [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (Q : RaySys.Mult V R)
    (hQ : Q.IsFiniteRayCategory k) (hfin : IsRepresentationFinite k (Q.Lin k)) :
    Module.Free ℤ Q.W ∧ IsStandard k (Q.Lin k) :=
  ⟨RaySys.Mult.W_free_of_isFiniteRayCategory hQ hfin,
    RaySys.Mult.isStandard_of_isFiniteRayCategory hQ hfin⟩

end MultiplicativeBasisDeformations
