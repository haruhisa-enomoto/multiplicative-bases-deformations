module

public import MultiplicativeBasisDeformations.Foundations.ComponentSpan
public import MultiplicativeBasisDeformations.Foundations.PeriodicLocalization
public import MultiplicativeBasisDeformations.Foundations.ObjectQuotients
public import MultiplicativeBasisDeformations.Foundations.A0Normed

/-!
# Proposition 5.1: the periodic localization of the derivative cokernels

`mesh-deformations.tex` (`prop:periodic-localization`): "Let `T` be the set of vertices
periodic under `τ`, and let `C_T` be the quotient by the identities outside `T`. For the
derivative `D_m`, the quotient induces isomorphisms `coker D_m(C) ≅ coker D_m(C_T)`
(`m ≥ 2`)."

`C_T` is the scalar mesh category of the full translation subquiver `Q_T` with the restricted
coefficients (`eq:mesh-object-quotient`, `restrictQuotEquiv`). The quotient acts on Hom spaces
between vertices of `T` by restricting path combinations (`resE`); a composite through a vertex
outside `T` goes to zero, so the restriction commutes with the mesh derivative (`resF_D`). On
the degree-`(m+1)` cokernels (`CokerDeg`) the induced map (`cokerRes`) is bijective
(`cokerRes_bijective`): surjective since every family on `Q_T` is the restriction of its
inclusion; injective since a family of `Q` differs from the inclusion of its restriction by
rows leaving `T`, which lie in the image of `D_m` (`row_mem_imageD_of_not_periodic`), while the
inclusion of a derivative of `Q_T` is a derivative of `Q` up to such rows (`inclRow_mem_imageD`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

open ScalarMeshCategory TranslationQuiver

namespace ScalarMeshCategory

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {S : Set V} (hS : Q.IsTauClosed S)
  (c : MeshCoefficients k Q)

/-! ### Restriction on Hom spaces -/

/-- The quotient `C → C_S` on Hom spaces between vertices of `S`. -/
def resE {a b : FullSub S} (φ : obj c a.val ⟶ obj c b.val) :
    obj (c.restrict hS) a ⟶ obj (c.restrict hS) b :=
  (RelationCategory.functor k (meshRelations (c.restrict hS))).map
    (FullSub.restrict k a b (Classical.choose
      (RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ)))

theorem resE_map {a b : FullSub S} (Φ : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val) :
    resE hS c ((RelationCategory.functor k (meshRelations c)).map Φ) =
      (RelationCategory.functor k (meshRelations (c.restrict hS))).map
        (FullSub.restrict k a b Φ) := by
  unfold resE
  have h := Classical.choose_spec (RelationCategory.functor_map_surjective (k := k)
    (meshRelations c) ((RelationCategory.functor k (meshRelations c)).map Φ))
  generalize Classical.choose (RelationCategory.functor_map_surjective (k := k)
    (meshRelations c) ((RelationCategory.functor k (meshRelations c)).map Φ)) = Φ' at h ⊢
  rw [← sub_eq_zero, ← Functor.map_sub, ← map_sub, RelationCategory.functor_map_eq_zero_iff]
  rw [← sub_eq_zero, ← Functor.map_sub, RelationCategory.functor_map_eq_zero_iff] at h
  exact restrict_mem_meshIdealSub hS c h

theorem resE_add {a b : FullSub S} (φ ψ : obj c a.val ⟶ obj c b.val) :
    resE hS c (φ + ψ) = resE hS c φ + resE hS c ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) ψ
  rw [← Functor.map_add, resE_map, resE_map, resE_map, map_add, Functor.map_add]

theorem resE_smul {a b : FullSub S} (t : k) (φ : obj c a.val ⟶ obj c b.val) :
    resE hS c (t • φ) = t • resE hS c φ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ
  rw [← Functor.map_smul, resE_map, resE_map, map_smul, Functor.map_smul]

theorem resE_zero {a b : FullSub S} : resE hS c (0 : obj c a.val ⟶ obj c b.val) = 0 := by
  have := resE_smul hS c (0 : k) (0 : obj c a.val ⟶ obj c b.val)
  rwa [zero_smul, zero_smul] at this

theorem resE_sum {a b : FullSub S} {ι : Type*} (s : Finset ι) (φ : ι → (obj c a.val ⟶ obj c b.val)) :
    resE hS c (∑ i ∈ s, φ i) = ∑ i ∈ s, resE hS c (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [resE_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, resE_add, ih]

theorem resE_comp {a b d : FullSub S} (φ : obj c a.val ⟶ obj c b.val)
    (ψ : obj c b.val ⟶ obj c d.val) : resE hS c (φ ≫ ψ) = resE hS c φ ≫ resE hS c ψ := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) ψ
  rw [← Functor.map_comp, resE_map, resE_map, resE_map, FullSub.restrict_comp, Functor.map_comp]

/-- **A composite through a vertex outside `S` vanishes in `C_S`.** -/
theorem resE_comp_out {a d : FullSub S} {y : V} (hy : y ∉ S) (φ : obj c a.val ⟶ obj c y)
    (ψ : obj c y ⟶ obj c d.val) : resE hS c (φ ≫ ψ) = 0 := by
  obtain ⟨Φ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) φ
  obtain ⟨Ψ, rfl⟩ := RelationCategory.functor_map_surjective (k := k) (meshRelations c) ψ
  rw [← Functor.map_comp, resE_map, FullSub.restrict_eq_zero_of_mem_outside (k := k),
    Functor.map_zero]
  rw [outside_eq_through]
  exact comp_mem_through (D := Sᶜ) hy Φ Ψ

theorem resE_arrowMor {a b : FullSub S} (e : a ⟶ b) :
    resE hS c (arrowMor c (show a.val ⟶ b.val from e)) = arrowMor (c.restrict hS) e := by
  have h : arrowMor c (show a.val ⟶ b.val from e) = (RelationCategory.functor k
      (meshRelations c)).map (FullSub.inclL k a b (LinearPaths.arrow e)) := by
    rw [FullSub.inclL, LinearPaths.mapPaths_arrow]; rfl
  rw [h, resE_map, FullSub.restrict_inclL]; rfl

theorem restrict_mem_degreePart {a b : FullSub S} {n : ℕ}
    {Φ : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val}
    (hΦ : Φ ∈ LinearPaths.degreePart (k := k) n a.val b.val) :
    FullSub.restrict k a b Φ ∈ LinearPaths.degreePart (k := k) n a b := by
  classical
  induction hΦ using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      simp only [FullSub.restrict, LinearPaths.extend_path, FullSub.restrictPath]
      split_ifs with h
      · rw [← hp, ← FullSub.length_liftPath p h]; exact LinearPaths.path_mem_degreePart _
      · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [map_smul]; exact Submodule.smul_mem _ t hf

theorem resE_degreePart {a b : FullSub S} {n : ℕ} {φ : obj c a.val ⟶ obj c b.val}
    (hφ : φ ∈ degreePart c n a.val b.val) : resE hS c φ ∈ degreePart (c.restrict hS) n a b := by
  obtain ⟨Φ, hΦ, rfl⟩ := hφ
  change resE hS c ((RelationCategory.functor k (meshRelations c)).map Φ) ∈ _
  rw [resE_map]
  exact ⟨_, restrict_mem_degreePart hΦ, rfl⟩

theorem resE_comp_arrow {a b d : FullSub S} (φ : obj c a.val ⟶ obj c b.val) (e : b ⟶ d) :
    resE hS c (φ ≫ arrowMor c (show b.val ⟶ d.val from e)) =
      resE hS c φ ≫ arrowMor (c.restrict hS) e := by
  rw [resE_comp, resE_arrowMor]

theorem resE_arrow_comp {a b d : FullSub S} (e : a ⟶ b) (φ : obj c b.val ⟶ obj c d.val) :
    resE hS c (arrowMor c (show a.val ⟶ b.val from e) ≫ φ) =
      arrowMor (c.restrict hS) e ≫ resE hS c φ := by
  rw [resE_comp, resE_arrowMor]

/-! ### Restriction of families -/

/-- The restriction of a mesh family to `Q_S`. -/
def resF (g : MeshFamily c) : MeshFamily (c.restrict hS) := fun xS ↦
  resE hS c (g (restrictNonproj hS xS))

/-- The restriction of an arrow family to `Q_S`. -/
def resA (f : ArrowFamily c) : ArrowFamily (c.restrict hS) := fun b ↦
  resE hS c (f ⟨b.1.val, b.2.1.val, b.2.2⟩)

/-- **Restriction commutes with the mesh derivative.** -/
theorem resF_D (f : ArrowFamily c) :
    resF hS c (meshDerivative c f) = meshDerivative (c.restrict hS) (resA hS c f) := by
  classical
  funext xS
  set x' := restrictNonproj hS xS
  unfold resF meshDerivative
  rw [resE_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Σ y : V, y ⟶ x'.1 ↦ a.1 ∈ S)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun a : Σ y : V, y ⟶ x'.1 ↦ a.1 ∉ S),
    add_zero]
  swap
  · intro a ha
    have ha' := (Finset.mem_filter.1 ha).2
    rw [resE_smul, resE_add, resE_comp_out hS c ha', resE_comp_out hS c ha', add_zero, smul_zero]
  symm
  refine Finset.sum_bij' (fun b _ ↦ ⟨b.1.val, b.2⟩)
    (fun a ha ↦ ⟨FullSub.mk a.1 (Finset.mem_filter.1 ha).2, a.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro b _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact b.1.val_mem
  · intro a _; exact Finset.mem_univ _
  · intro b _; rfl
  · intro a _; rfl
  · intro b _
    rw [resE_smul, resE_add]
    have h1 := resE_comp_arrow hS c (a := ((TranslationQuiver.restrict hS).tau xS).1) (b := b.1)
      (d := xS.1) (f ⟨(Q.tau x').1, b.1.val, Q.mate x' b.1.val b.2⟩) b.2
    have h2 := resE_arrow_comp hS c (a := ((TranslationQuiver.restrict hS).tau xS).1) (b := b.1)
      (d := xS.1) ((TranslationQuiver.restrict hS).mate xS b.1 b.2) (f ⟨b.1.val, x'.1, b.2⟩)
    exact (congrArg₂ (fun u v ↦ ((c x' b.1.val b.2 : kˣ) : k) • (u + v)) h1 h2).symm

/-! ### The degree-`(m+1)` cokernels -/

/-- The mesh families of degree `n`. -/
def famDeg (n : ℕ) : Submodule k (MeshFamily c) where
  carrier := {g | ∀ x, g x ∈ degreePart c n _ _}
  add_mem' ha hb x := add_mem (ha x) (hb x)
  zero_mem' _ := zero_mem _
  smul_mem' t _ hg x := Submodule.smul_mem _ t (hg x)

theorem imageD_le_famDeg (m : ℕ) : imageD c m ≤ famDeg c (m + 1) := by
  rintro _ ⟨f, hf, rfl⟩ x
  rw [meshDerivativeₗ_apply]
  refine Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (add_mem ?_ ?_)
  · exact comp_mem_degreePart' c (hf ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)
      ⟨_, LinearPaths.arrow_mem_degreePart a.2, rfl⟩
  · have := comp_mem_degreePart' c ⟨_, LinearPaths.arrow_mem_degreePart
      (Q.mate x a.1 a.2), rfl⟩ (hf ⟨a.1, x.1, a.2⟩)
    rwa [add_comm] at this

/-- **The cokernel of `D_m`** on the degree-`(m+1)` mesh families. -/
abbrev CokerDeg (m : ℕ) :=
  famDeg c (m + 1) ⧸ (imageD c m).comap (famDeg c (m + 1)).subtype

/-- The restriction of families as a linear map. -/
def resFL : MeshFamily c →ₗ[k] MeshFamily (c.restrict hS) where
  toFun := resF hS c
  map_add' _ _ := funext fun _ ↦ resE_add hS c _ _
  map_smul' t _ := funext fun _ ↦ resE_smul hS c t _

theorem resF_famDeg {n : ℕ} {g : MeshFamily c} (hg : g ∈ famDeg c n) :
    resF hS c g ∈ famDeg (c.restrict hS) n := fun xS ↦ resE_degreePart hS c (hg _)

theorem resF_imageD {m : ℕ} {g : MeshFamily c} (hg : g ∈ imageD c m) :
    resF hS c g ∈ imageD (c.restrict hS) m := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨resA hS c f, fun b ↦ resE_degreePart hS c (hf ⟨b.1.val, b.2.1.val, b.2.2⟩), by
    rw [meshDerivativeₗ_apply, meshDerivativeₗ_apply, resF_D]⟩

/-- **The map `coker D_m(C) → coker D_m(C_S)`** induced by the quotient. -/
def cokerRes (m : ℕ) : CokerDeg c m →ₗ[k] CokerDeg (c.restrict hS) m :=
  Submodule.mapQ _ _ ((resFL hS c).restrict fun _ hg ↦ resF_famDeg hS c hg)
    (fun g hg ↦ resF_imageD hS c hg)

/-! ### Bijectivity -/

section Bij

variable [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ S)]
  [DecidablePred (· ∈ Q.nonprojective)]

theorem end_mem_vertices {a b : V} (p : Quiver.Path a b) : b ∈ p.vertices := by
  cases p with
  | nil => simp [Quiver.Path.vertices_nil]
  | cons p e => simp [Quiver.Path.vertices_cons]

theorem inclRow_of_mem (G : RowFam (k := k) hS) (x : Q.nonprojective) (hx : x.1 ∈ S) :
    inclRow hS c G x = (RelationCategory.functor k (meshRelations c)).map
      (FullSub.inclL k ((TranslationQuiver.restrict hS).tau ⟨FullSub.mk x.1 hx, x.2⟩).1
        (FullSub.mk x.1 hx) (G ⟨FullSub.mk x.1 hx, x.2⟩)) := by
  unfold inclRow; rw [dif_pos hx]

theorem inclRow_of_not_mem (G : RowFam (k := k) hS) (x : Q.nonprojective) (hx : x.1 ∉ S) :
    inclRow hS c G x = 0 := by
  unfold inclRow; rw [dif_neg hx]

theorem resF_inclRow (G : RowFam (k := k) hS) (xS : (TranslationQuiver.restrict hS).nonprojective) :
    resF hS c (inclRow hS c G) xS =
      (RelationCategory.functor k (meshRelations (c.restrict hS))).map (G xS) := by
  rcases xS with ⟨⟨v, hv⟩, h⟩
  unfold resF
  rw [inclRow_of_mem hS c G _ hv, resE_map]
  exact congrArg _ (FullSub.restrict_inclL k _)

theorem cokerRes_surjective (m : ℕ) : Function.Surjective (cokerRes hS c m) := by
  intro z
  obtain ⟨⟨G, hG⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  choose G' hG' hG'' using fun xS ↦ hG xS
  have hdeg : inclRow hS c G' ∈ famDeg c (m + 1) := fun x ↦ by
    by_cases hx : x.1 ∈ S
    · rw [inclRow_of_mem hS c G' x hx]
      exact ⟨_, LinearPaths.mapPaths_mem_degreePart (FullSub.incl S)
        (hG' ⟨FullSub.mk x.1 hx, x.2⟩), rfl⟩
    · rw [inclRow_of_not_mem hS c G' x hx]; exact zero_mem _
  refine ⟨Submodule.Quotient.mk ⟨inclRow hS c G', hdeg⟩, ?_⟩
  rw [cokerRes, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext xS
  change resF hS c (inclRow hS c G') xS = G xS
  rw [resF_inclRow]
  exact hG'' xS

variable {m : ℕ}
  (hout : ∀ (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1), w.length = m + 1 →
    (∃ v ∈ w.vertices, v ∉ S) → row c x w ∈ imageD c m)

include hout in
theorem cokerRes_injective [Fintype V] [Fintype Q.nonprojective] :
    Function.Injective (cokerRes hS c m) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, cokerRes, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  change resF hS c g ∈ imageD (c.restrict hS) m at hz
  rw [Submodule.Quotient.mk_eq_zero]
  change g ∈ imageD c m
  choose Φ hΦ hΦ'' using fun x ↦ hg x
  have hΦ' : ∀ x, (RelationCategory.functor k (meshRelations c)).map (Φ x) = g x := hΦ''
  let G' : RowFam (k := k) hS := fun xS ↦ FullSub.restrict k _ _ (Φ (restrictNonproj hS xS))
  have hG'd : ∀ xS, G' xS ∈ LinearPaths.degreePart (k := k) (m + 1) _ _ := fun xS ↦
    restrict_mem_degreePart (hΦ _)
  have hmap : (fun xS ↦ (RelationCategory.functor k (meshRelations (c.restrict hS))).map
      (G' xS)) = resF hS c g := by
    funext xS
    unfold resF
    rw [← hΦ' (restrictNonproj hS xS), resE_map]
  have hincl := inclRow_mem_imageD hS c (fun x w hw _ hv ↦ hout x w hw hv) G' hG'd
    (by rw [hmap]; exact hz)
  have hdiff : g - inclRow hS c G' ∈ imageD c m := by
    rw [← Finset.univ_sum_single (g - inclRow hS c G')]
    refine Submodule.sum_mem _ fun x _ ↦ ?_
    by_cases hx : x.1 ∈ S
    · have e : (g - inclRow hS c G') x = (RelationCategory.functor k (meshRelations c)).map
          (Φ x - FullSub.inclL k ((TranslationQuiver.restrict hS).tau ⟨FullSub.mk x.1 hx, x.2⟩).1
            (FullSub.mk x.1 hx) (FullSub.restrict k _ _ (Φ x))) := by
        rw [Pi.sub_apply, Functor.map_sub, hΦ' x, inclRow_of_mem hS c G' x hx]
      rw [e]
      refine single_mem_imageD_of_mem_sup c (fun x w hw _ hv ↦ hout x w hw hv) x hx
        (Submodule.mem_sup_right (FullSub.sub_inclL_restrict_mem k
          (a := ((TranslationQuiver.restrict hS).tau ⟨FullSub.mk x.1 hx, x.2⟩).1)
          (b := FullSub.mk x.1 hx) (Φ x))) ?_
      exact sub_mem (hΦ x) (LinearPaths.mapPaths_mem_degreePart (FullSub.incl S)
        (restrict_mem_degreePart (a := ((TranslationQuiver.restrict hS).tau
          ⟨FullSub.mk x.1 hx, x.2⟩).1) (b := FullSub.mk x.1 hx) (hΦ x)))
    · have e : (g - inclRow hS c G') x = (RelationCategory.functor k (meshRelations c)).map (Φ x) := by
        rw [Pi.sub_apply, hΦ' x, inclRow_of_not_mem hS c G' x hx, sub_zero]
      rw [e]
      have hspan := hΦ x
      generalize Φ x = F at hspan ⊢
      induction hspan using Submodule.span_induction with
      | mem f hf =>
          obtain ⟨p, hp, rfl⟩ := hf
          exact hout x p hp ⟨x.1, end_mem_vertices p, hx⟩
      | zero => rw [Functor.map_zero, Pi.single_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [Functor.map_add, Pi.single_add]; exact add_mem ha hb
      | smul t a _ ha => rw [Functor.map_smul, Pi.single_smul]; exact Submodule.smul_mem _ t ha
  have := add_mem hdiff hincl
  rwa [sub_add_cancel] at this

end Bij

/-! ### The periodic vertices -/

theorem isTauClosed_periodic : Q.IsTauClosed Q.periodic := fun x hx ↦ by
  constructor
  · intro h
    obtain ⟨h', hτ⟩ := (isTauPeriodic_iff x).1 h
    exact hτ
  · intro h
    exact (isTauPeriodic_iff x).2 ⟨hx, h⟩

/-- **Proposition 5.1** (`prop:periodic-localization`): the quotient `C → C_T` by the
identities outside the periodic vertices `T` induces isomorphisms
`coker D_m(C) ≅ coker D_m(C_T)` (for every `m`; the source states `m ≥ 2`). Here `C_T` is the
scalar mesh category of `Q_T` (`eq:mesh-object-quotient`). -/
theorem periodicLocalization [Fintype V] [Fintype Q.nonprojective] [DecidableEq V]
    [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.periodic)]
    [DecidablePred (· ∈ Q.nonprojective)] (m : ℕ) :
    Function.Bijective (cokerRes isTauClosed_periodic c m) :=
  ⟨cokerRes_injective isTauClosed_periodic c fun x w hw ⟨v, hv, hvT⟩ ↦
      row_mem_imageD_of_not_periodic c x w hw hv hvT,
    cokerRes_surjective isTauClosed_periodic c m⟩

end ScalarMeshCategory

end MultiplicativeBasisDeformations
