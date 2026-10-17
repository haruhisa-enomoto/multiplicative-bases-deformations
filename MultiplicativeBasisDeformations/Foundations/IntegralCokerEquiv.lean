import MultiplicativeBasisDeformations.Foundations.IntegralCokerIso

/-!
# Lemma B.2 as a linear isomorphism

`lem:integral-mesh-cokernels`: "`⊕_{m≥2} coker D_m(E₄) ≅ ⊕_{i∈I} (𝒪/(2))_{χ_i}`. The summand
indexed by `i` belongs to `coker D_{d_i−1}`, where `d_i = 2s_i + 2` is its mesh path degree."

`integralMeshCokernels` proves that the rows of Proposition 6.1 generate each cokernel over
`𝒪 = ℤ/4`, that twice each is a derivative, and that a combination is a derivative exactly when
all coefficients are even. Here this is assembled into an explicit isomorphism of `𝒪`-modules in
each degree: `coker D_m(E₄) = F_{m+1}/(im D_m ∩ F_{m+1}) ≅ ⊕_{R} 𝒪/(2)`, the sum over the rows `R`
of degree `m + 1`, sending the class of the row `R` to the generator of its summand
(`integralMeshCokernels_equiv`). Summing over `m ≥ 2` gives the displayed isomorphism, the row `i`
lying in degree `m = d_i − 1`. The weight labels `χ_i` are `integralMeshCokernels_weights`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe v w

namespace ScalarMeshCategory

open LinearPaths TranslationQuiver

section Ring

variable {k : Type*} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

/-- The mesh families of degree `n`. -/
def famDegR (n : ℕ) : Submodule k (MeshFamily c) where
  carrier := {g | ∀ x, g x ∈ degreePart c n _ _}
  add_mem' ha hb x := add_mem (ha x) (hb x)
  zero_mem' _ := zero_mem _
  smul_mem' t _ hg x := Submodule.smul_mem _ t (hg x)

theorem comp_mem_degreePartR {d e : ℕ} {x y z : V} {f : obj c x ⟶ obj c y}
    {g : obj c y ⟶ obj c z} (hf : f ∈ degreePart c d x y) (hg : g ∈ degreePart c e y z) :
    f ≫ g ∈ degreePart c (d + e) x z := by
  obtain ⟨F, hF, rfl⟩ := hf
  obtain ⟨G, hG, rfl⟩ := hg
  refine ⟨F ≫ G, LinearPaths.comp_mem_degreePart hF hG, ?_⟩
  change (RelationCategory.functor k (meshRelations c)).map (F ≫ G) = _
  rw [Functor.map_comp]
  rfl

theorem imageD_le_famDegR (m : ℕ) : imageD c m ≤ famDegR c (m + 1) := by
  rintro _ ⟨f, hf, rfl⟩ x
  rw [meshDerivativeₗ_apply]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
  · exact comp_mem_degreePartR c (hf ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)
      ⟨_, LinearPaths.arrow_mem_degreePart a.2, rfl⟩
  · have := comp_mem_degreePartR c ⟨_, LinearPaths.arrow_mem_degreePart
      (Q.mate x a.1 a.2), rfl⟩ (hf ⟨a.1, x.1, a.2⟩)
    rwa [add_comm] at this

/-- **The cokernel of `D_m`** on the degree-`(m+1)` mesh families. -/
abbrev CokerDegR (m : ℕ) :=
  famDegR c (m + 1) ⧸ (imageD c m).comap (famDegR c (m + 1)).subtype

theorem row_mem_famDegR [DecidableEq V] {m : ℕ} (x : Q.nonprojective)
    (p : Quiver.Path (Q.tau x).1 x.1) (hp : p.length = m + 1) : row c x p ∈ famDegR c (m + 1) := by
  intro x'
  by_cases hx : x' = x
  · subst hx; simp only [row, Pi.single_eq_same]; rw [← hp]; exact pathMor_mem_degreePart c p
  · simp only [row, Pi.single_eq_of_ne hx]; exact zero_mem _

end Ring

theorem mem_span_two_iff (a : ZMod 4) : a ∈ Ideal.span {(2 : ZMod 4)} ↔ Z4.red a = 0 := by
  rw [Ideal.mem_span_singleton']
  revert a; decide

variable {V : Type v} [Quiver.{w} V]
  [Fintype V] [DecidableEq V] [∀ x y : V, Fintype (x ⟶ y)] [∀ x y : V, DecidableEq (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {Q : TranslationQuiver V} [DecidablePred (· ∈ Q.nonprojective)] [Fintype Q.nonprojective]
  {c : MeshCoefficients 𝔽₂ Q} {u : MeshCoefficients (ZMod 4) Q}
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

/-- The rows of `S` of degree `m + 1`. -/
abbrev RowsDeg (S : RowSet Q) (m : ℕ) :=
  {R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1 // R ∈ S ∧ R.2.length = m + 1}

include hred in
/-- **Lemma B.2** (`lem:integral-mesh-cokernels`) **as an isomorphism**: for `E₄` (unit
coefficients `u` over `𝒪 = ℤ/4` reducing to the coefficients of `C⁽²⁾`), there are rows `S` as in
Proposition 6.1 (periodic, one per residual component, with the degrees `d_i = 2s_i + 2` of the
models) such that, in every degree `m ≥ 2`, `coker D_m(E₄) ≅ ⊕_{R ∈ S, deg R = m + 1} 𝒪/(2)`,
sending the class of each row `R` to the generator of its summand. -/
theorem integralMeshCokernels_equiv (hQ : HasAtMostOneArrow V) [DecidablePred (· ∈ Q.periodic)]
    (hfin : ∀ x y : V, FiniteDimensional 𝔽₂ (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (hbrick : BrickHypothesis c) :
    ∃ S : RowSet Q, (∀ R ∈ S, R.1.1 ∈ Q.periodic) ∧
      (∀ R ∈ S, ∀ R' ∈ S, R'.1.1 ∈ Q.component R.1.1 → R = R') ∧
      (∀ r ∈ Q.periodic, Residual c r ↔ ∃ R ∈ S, R.1.1 ∈ Q.component r) ∧
      (∀ R ∈ S, ∃ x, x ∈ Q.periodic ∧ R.1.1 ∈ Q.component x ∧
        ∃ R₀ : (Σ y : (TranslationQuiver.restrict (TranslationQuiver.isTauClosed_component
            (Q := Q) x)).nonprojective,
          Quiver.Path ((TranslationQuiver.restrict (TranslationQuiver.isTauClosed_component
            (Q := Q) x)).tau y).1 y.1),
          StarTrace.DEModel (TranslationQuiver.restrict_isStable (Q := Q) x) R₀ ∧
            R₀.2.length = R.2.length) ∧
      ∀ m, 2 ≤ m → ∃ (_ : Fintype (RowsDeg S m))
        (e : CokerDegR u m ≃ₗ[ZMod 4] (RowsDeg S m → ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)})),
        ∀ R : RowsDeg S m, e (Submodule.Quotient.mk ⟨row u R.1.1 R.1.2,
          row_mem_famDegR u R.1.1 R.1.2 R.2.2⟩) = Pi.single R (Submodule.Quotient.mk 1) := by
  classical
  obtain ⟨S, hper, huniq, hres, hmod, hdeg⟩ := integralMeshCokernels hred hQ hfin hbrick
  refine ⟨S, hper, huniq, hres, hmod, fun m hm ↦ ?_⟩
  obtain ⟨hspan, -, hindep⟩ := hdeg m hm
  -- finiteness: one row per component
  have hfinS : S.Finite := by
    refine Set.Finite.of_finite_image (f := fun R ↦ R.1) (Set.toFinite _) ?_
    intro R hR R' hR' h
    exact huniq R hR R' hR' (by
      have : R'.1.1 = R.1.1 := congrArg Subtype.val h.symm
      rw [this]; exact mem_component_self (hper R hR))
  have := hfinS.to_subtype
  have : Finite (RowsDeg S m) :=
    Finite.of_injective (fun R : RowsDeg S m ↦ (⟨R.1, R.2.1⟩ : S)) (fun R R' h ↦
      Subtype.ext (by simpa using h))
  letI : Fintype (RowsDeg S m) := Fintype.ofFinite _
  refine ⟨this, ?_⟩
  -- the combination map
  let ψ : (RowsDeg S m → ZMod 4) →ₗ[ZMod 4] MeshFamily u :=
    Fintype.linearCombination (ZMod 4) (fun R : RowsDeg S m ↦ row u R.1.1 R.1.2)
  have hψmem : ∀ l, ψ l ∈ famDegR u (m + 1) := fun l ↦
    Submodule.sum_mem _ fun R _ ↦ Submodule.smul_mem _ _ (row_mem_famDegR u R.1.1 R.1.2 R.2.2)
  let φ : (RowsDeg S m → ZMod 4) →ₗ[ZMod 4] CokerDegR u m :=
    (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (famDegR u (m + 1)) ψ hψmem
  have hφ : ∀ l, φ l = Submodule.Quotient.mk ⟨ψ l, hψmem l⟩ := fun l ↦ rfl
  have hψsingle : ∀ R : RowsDeg S m, ψ (Pi.single R 1) = row u R.1.1 R.1.2 := by
    intro R
    simp [ψ, Fintype.linearCombination_apply_single]
  -- `ψ l` as a combination over a finset of rows
  have hψsum : ∀ l, ψ l = ∑ R ∈ (Finset.univ : Finset (RowsDeg S m)).map
      (Function.Embedding.subtype (fun R ↦ R ∈ S ∧ R.2.length = m + 1)),
      (fun R ↦ if h : R ∈ S ∧ R.2.length = m + 1 then l ⟨R, h⟩ else 0) R • row u R.1 R.2 := by
    intro l
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun R _ ↦ ?_
    simp only [Function.Embedding.coe_subtype, dif_pos R.2]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨F, l, hF, hFl, hgl⟩ := hspan g hg
    have hmem : ∑ R ∈ F, l R • row u R.1 R.2 ∈ LinearMap.range ψ := by
      refine Submodule.sum_mem _ fun R hR ↦ Submodule.smul_mem _ _ ?_
      exact ⟨Pi.single ⟨R, hF hR, hFl R hR⟩ 1, hψsingle _⟩
    obtain ⟨l', hl'⟩ := hmem
    refine ⟨l', ?_⟩
    rw [hφ, eq_comm, Submodule.Quotient.eq]
    change g - ψ l' ∈ imageD u m
    rw [hl']
    exact hgl
  have hker : LinearMap.ker φ = Submodule.pi Set.univ (fun _ ↦ Ideal.span {(2 : ZMod 4)}) := by
    ext l
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_pi]
    change ψ l ∈ imageD u m ↔ _
    rw [hψsum, hindep _ (by
        intro R hR; obtain ⟨R', -, rfl⟩ := Finset.mem_map.1 hR; exact R'.2.1)
      (by intro R hR; obtain ⟨R', -, rfl⟩ := Finset.mem_map.1 hR; exact R'.2.2)]
    constructor
    · intro h R _
      have := h R.1 (Finset.mem_map_of_mem _ (Finset.mem_univ R))
      rw [dif_pos R.2] at this
      exact (mem_span_two_iff _).2 this
    · intro h R hR
      obtain ⟨R', -, rfl⟩ := Finset.mem_map.1 hR
      rw [Function.Embedding.coe_subtype, dif_pos R'.2]
      exact (mem_span_two_iff _).1 (h R' (Set.mem_univ _))
  let e : CokerDegR u m ≃ₗ[ZMod 4] (RowsDeg S m → ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)}) :=
    (LinearMap.quotKerEquivOfSurjective φ hsurj).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi _))
  refine ⟨e, fun R ↦ ?_⟩
  have hrow : (Submodule.Quotient.mk ⟨row u R.1.1 R.1.2, row_mem_famDegR u R.1.1 R.1.2 R.2.2⟩ :
      CokerDegR u m) = φ (Pi.single R 1) := by
    rw [hφ]; congr 1; exact Subtype.ext (hψsingle R).symm
  rw [hrow]
  simp only [e, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk]
  funext R'
  rw [Submodule.quotientPi_apply]
  by_cases h : R' = R
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end ScalarMeshCategory

end MultiplicativeBasisDeformations
