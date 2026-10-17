import MultiplicativeBasisDeformations.Foundations.FibreRays
import MultiplicativeBasisDeformations.Foundations.RayProduct
import MultiplicativeBasisDeformations.Foundations.RayTransport

/-!
# Ray presentations

A *ray presentation* of an algebra `B` (with primitive idempotents `F`) by a ray table `T`
is a family of vectors `β r`, one in each nonzero ray, such that the ray products of `B`
(Definition 3.4: `[f][h] = [fh]` unless `fh ∈ M(f, h)`) are the products of `T`. This is the
content of "`ray A_t = P` with the specified representatives" (Proposition 11.3(3),
`binary-families.tex`) and of Definition 3.9(3).

The transported rays of a fibre of the zero-product family present `B` by `P` (`fibre_rayPres`):
"If `n ∈ rad R_y`, the product `rn` is a combination of proper rays, so `(rn)·s = (rn)s` …
Each correction `r*s = rq_ys` belongs to this subspace." With zero coefficients this shows
that a representation-finite ray table presents its own linearization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

/-- **The weight-lifting property** of a ray table: additive weights modulo two lift to integer
additive weights (the form in which freeness of `W(Q)` is used, `hW` of Theorem 9.1). -/
def Mult.Lift2 {V R : Type} (T : Mult V R) : Prop :=
  ∀ w : R → ZMod 2, (∀ r s t, T.mul r s = some t → w t = w r + w s) →
    ∃ ω : R → ℤ, (∀ r s t, T.mul r s = some t → ω t = ω r + ω s) ∧ ∀ r, (ω r : ZMod 2) = w r

/-- A connected table: every two vertices are joined by a zigzag of rays. -/
def Mult.Conn {V R : Type} (T : Mult V R) : Prop :=
  ∀ x y : V, Relation.EqvGen (fun x y ↦ ∃ r, T.src r = x ∧ T.tgt r = y) x y

end RaySys

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] {B : Type u} [Ring B] [Algebra k B]

/-- **A ray presentation of `B` by the table `T`.** -/
structure IsRayPres (F : PrimitiveIdempotents B) {V R : Type} (T : RaySys.Mult V R)
    (ι : V ≃ Fin F.m) (β : R → B) : Prop where
  corner : ∀ r, β r ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt r))
  ne : ∀ r, β r ≠ 0
  inj : ∀ r s, β r ∈ F.ray (k := k) (ι (T.src s)) (ι (T.tgt s)) (β s) → r = s
  surj : ∀ x y (f : B), f ∈ F.corner (k := k) x y → f ≠ 0 →
    ∃ r, ι (T.src r) = x ∧ ι (T.tgt r) = y ∧ f ∈ F.ray (k := k) x y (β r)
  mul_some : ∀ r s t, T.mul r s = some t →
    β r * β s ∉ F.insertionSpan (k := k) (ι (T.src r)) (ι (T.tgt r)) (ι (T.tgt s)) (β r) (β s) ∧
      β r * β s ∈ F.ray (k := k) (ι (T.src t)) (ι (T.tgt t)) (β t)
  mul_none : ∀ r s, T.mul r s = none → T.tgt r = T.src s →
    β r * β s ∈ F.insertionSpan (k := k) (ι (T.src r)) (ι (T.tgt r)) (ι (T.tgt s)) (β r) (β s)

section Unique

variable [IsAlgClosed k] [FiniteDimensional k B] {F : PrimitiveIdempotents B}
  {V R V' R' : Type} {T : RaySys.Mult V R} {T' : RaySys.Mult V' R'} {ι : V ≃ Fin F.m}
  {ι' : V' ≃ Fin F.m} {β : R → B} {β' : R' → B}

/-- The ray of `β r` among the rays of the second presentation. -/
theorem IsRayPres.exists_match (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β')
    (r : R) : ∃ r', ι' (T'.src r') = ι (T.src r) ∧ ι' (T'.tgt r') = ι (T.tgt r) ∧
      β r ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt r)) (β' r') := by
  obtain ⟨r', h1, h2, h3⟩ := h'.surj _ _ (β r) (h.corner r) (h.ne r)
  exact ⟨r', h1, h2, h3⟩

theorem ray_symm {x y : Fin F.m} {f g : B} (hf : f ∈ F.corner (k := k) x y)
    (hg : g ∈ F.ray (k := k) x y f) : f ∈ F.ray (k := k) x y g := by
  rw [F.ray_eq_of_mem hf hg]; exact F.mem_ray_self hf

theorem ray_trans {x y : Fin F.m} {f g h : B} (hg : g ∈ F.corner (k := k) x y)
    (h1 : f ∈ F.ray (k := k) x y g) (h2 : g ∈ F.ray (k := k) x y h)
    (hh : h ∈ F.corner (k := k) x y) : f ∈ F.ray (k := k) x y h := by
  rw [← F.ray_eq_of_mem hh h2]; exact h1

/-- **Two ray presentations of the same algebra have isomorphic tables** (Lemma 3.6). -/
theorem IsRayPres.mul_iff (hB : IsRepresentationFinite k B) (h : F.IsRayPres (k := k) T ι β)
    (h' : F.IsRayPres (k := k) T' ι' β') {r s t : R} {r' s' t' : R'}
    (hr : ι' (T'.src r') = ι (T.src r) ∧ ι' (T'.tgt r') = ι (T.tgt r) ∧
      β r ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt r)) (β' r'))
    (hs : ι' (T'.src s') = ι (T.src s) ∧ ι' (T'.tgt s') = ι (T.tgt s) ∧
      β s ∈ F.ray (k := k) (ι (T.src s)) (ι (T.tgt s)) (β' s'))
    (ht : ι' (T'.src t') = ι (T.src t) ∧ ι' (T'.tgt t') = ι (T.tgt t) ∧
      β t ∈ F.ray (k := k) (ι (T.src t)) (ι (T.tgt t)) (β' t'))
    (hrst : T.mul r s = some t) : T'.mul r' s' = some t' := by
  obtain ⟨hM, hray⟩ := h.mul_some r s t hrst
  have hmid := T.mul_mid r s t hrst
  have hsrc := T.mul_src r s t hrst
  have htgt := T.mul_tgt r s t hrst
  -- corners of the second presentation, in the indices of the first
  have hcr' : β' r' ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt r)) := by
    rw [← hr.1, ← hr.2.1]; exact h'.corner r'
  have hcs' : β' s' ∈ F.corner (k := k) (ι (T.src s)) (ι (T.tgt s)) := by
    rw [← hs.1, ← hs.2.1]; exact h'.corner s'
  have hct' : β' t' ∈ F.corner (k := k) (ι (T.src t)) (ι (T.tgt t)) := by
    rw [← ht.1, ← ht.2.1]; exact h'.corner t'
  have hr1 : β' r' ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt r)) (β r) :=
    F.ray_symm hcr' hr.2.2
  have hs1 : β' s' ∈ F.ray (k := k) (ι (T.tgt r)) (ι (T.tgt s)) (β s) := by
    rw [hmid]; exact F.ray_symm hcs' hs.2.2
  have hcs : β s ∈ F.corner (k := k) (ι (T.tgt r)) (ι (T.tgt s)) := by rw [hmid]; exact h.corner s
  obtain ⟨hMiff, hrayeq⟩ := F.rayProduct_independent_of hB (h.corner r) (h.ne r) hcs (h.ne s) hr1 hs1
  have hM' : β' r' * β' s' ∉ F.insertionSpan (k := k) (ι (T.src r)) (ι (T.tgt r)) (ι (T.tgt s))
      (β' r') (β' s') := fun h0 ↦ hM (hMiff.2 h0)
  obtain ⟨-, hreq⟩ := hrayeq hM
  -- the composable pair of the second table
  have hmid' : T'.tgt r' = T'.src s' := ι'.injective (by rw [hr.2.1, hs.1, hmid])
  cases hm : T'.mul r' s' with
  | none =>
    exfalso
    have := h'.mul_none r' s' hm hmid'
    rw [hr.1, hr.2.1, show ι' (T'.tgt s') = ι (T.tgt s) from hs.2.1] at this
    exact hM' this
  | some t'' =>
    obtain ⟨-, hray''⟩ := h'.mul_some r' s' t'' hm
    have hsrc'' := T'.mul_src r' s' t'' hm
    have htgt'' := T'.mul_tgt r' s' t'' hm
    rw [hsrc'', htgt'', hr.1, hs.2.1] at hray''
    -- `β' t''` and `β' t'` lie in the ray of `β t`
    have hfh : β r * β s ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt s)) :=
      F.corner_mul_corner (h.corner r) hcs
    rw [hsrc, htgt] at hray
    have hcs'' : β' s' ∈ F.corner (k := k) (ι (T.tgt r)) (ι (T.tgt s)) := by
      rw [hmid]; exact hcs'
    have hfh' : β' r' * β' s' ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt s)) :=
      F.corner_mul_corner hcr' hcs''
    have a3 : β' r' * β' s' ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt s)) (β r * β s) := by
      rw [hreq]; exact F.mem_ray_self hfh'
    have hct : β t ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt s)) := by
      rw [← hsrc, ← htgt]; exact h.corner t
    have hct'' : β' t'' ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt s)) := by
      rw [← hr.1, ← hs.2.1, ← hsrc'', ← htgt'']; exact h'.corner t''
    have a2 : β' t'' ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt s)) (β' r' * β' s') :=
      F.ray_symm hct'' hray''
    have inner := F.ray_trans hfh a3 hray hct
    have h3 : β' t'' ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt s)) (β t) :=
      F.ray_trans hfh' a2 inner hct
    have h4 : β' t'' ∈ F.ray (k := k) (ι' (T'.src t')) (ι' (T'.tgt t')) (β' t') := by
      rw [ht.1, ht.2.1, hsrc, htgt]
      exact F.ray_trans hct h3 (by rw [← hsrc, ← htgt]; exact ht.2.2) (by
        rw [← hsrc, ← htgt]; exact hct')
    rw [h'.inj t'' t' h4]

/-- The matching ray of the second presentation, as a function. -/
def IsRayPres.matchFn (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β') :
    R → R' := fun r ↦ (h.exists_match h' r).choose

theorem IsRayPres.matchFn_spec (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β')
    (r : R) : ι' (T'.src (h.matchFn h' r)) = ι (T.src r) ∧ ι' (T'.tgt (h.matchFn h' r)) = ι (T.tgt r) ∧
      β r ∈ F.ray (k := k) (ι (T.src r)) (ι (T.tgt r)) (β' (h.matchFn h' r)) :=
  (h.exists_match h' r).choose_spec

theorem IsRayPres.matchFn_left_inv (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β')
    (r : R) : h'.matchFn h (h.matchFn h' r) = r := by
  obtain ⟨a1, a2, a3⟩ := h.matchFn_spec h' r
  obtain ⟨b1, b2, b3⟩ := h'.matchFn_spec h (h.matchFn h' r)
  set r' := h.matchFn h' r
  set r'' := h'.matchFn h r'
  rw [a1] at b1
  rw [a2] at b2
  rw [a1, a2] at b3
  -- `β r ∈ [β' r'] ∋ β r''` …
  have hc' : β' r' ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt r)) := by
    rw [← a1, ← a2]; exact h'.corner r'
  have hc'' : β r'' ∈ F.corner (k := k) (ι (T.src r)) (ι (T.tgt r)) := by
    rw [← b1, ← b2]; exact h.corner r''
  have : β r ∈ F.ray (k := k) (ι (T.src r'')) (ι (T.tgt r'')) (β r'') := by
    rw [b1, b2]; exact F.ray_trans hc' a3 b3 hc''
  exact (h.inj r r'' this).symm

/-- **Weight lifting transfers along ray presentations of one algebra.** -/
theorem IsRayPres.lift2 (hB : IsRepresentationFinite k B) (h : F.IsRayPres (k := k) T ι β)
    (h' : F.IsRayPres (k := k) T' ι' β') (hL : T'.Lift2) : T.Lift2 := by
  intro w hw
  set φ := h.matchFn h'
  set ψ := h'.matchFn h
  obtain ⟨ω', hω', hωw⟩ := hL (w ∘ ψ) fun r' s' t' hm ↦ by
    simp only [Function.comp]
    exact hw _ _ _ (h'.mul_iff hB h (h'.matchFn_spec h r') (h'.matchFn_spec h s')
      (h'.matchFn_spec h t') hm)
  refine ⟨ω' ∘ φ, fun r s t hm ↦ ?_, fun r ↦ ?_⟩
  · exact hω' _ _ _ (h.mul_iff hB h' (h.matchFn_spec h' r) (h.matchFn_spec h' s)
      (h.matchFn_spec h' t) hm)
  · simp only [Function.comp, hωw, ψ, φ, h.matchFn_left_inv h']

/-- **Ray presentations transport along algebra isomorphisms.** -/
theorem IsRayPres.map {B' : Type u} [Ring B'] [Algebra k B'] [FiniteDimensional k B']
    (ψ : B ≃ₐ[k] B') (F' : PrimitiveIdempotents B') (σ : Fin F.m ≃ Fin F'.m)
    (hψ : ∀ i, ψ (F.e i) = F'.e (σ i)) (h : F.IsRayPres (k := k) T ι β) :
    F'.IsRayPres (k := k) T (ι.trans σ) (ψ ∘ β) := by
  have hsym := F.symm_e ψ F' σ hψ
  refine ⟨fun r ↦ F.corner_fwd ψ F' σ hψ (h.corner r), fun r h0 ↦ h.ne r (ψ.injective (by
    rw [Function.comp_apply] at h0; rw [h0, map_zero])), fun r s hrs ↦ ?_, fun x y f hf hf0 ↦ ?_,
    fun r s t hm ↦ ?_, fun r s hm hmid ↦ ?_⟩
  · have := F'.ray_fwd ψ.symm F σ.symm hsym hrs
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Function.comp_apply,
      AlgEquiv.symm_apply_apply] at this
    exact h.inj r s this
  · have hf' := F'.corner_fwd ψ.symm F σ.symm hsym hf
    obtain ⟨r, h1, h2, h3⟩ := h.surj _ _ _ hf' (fun h0 ↦ hf0 (by
      rw [← ψ.apply_symm_apply f, h0, map_zero]))
    refine ⟨r, by simp [h1], by simp [h2], ?_⟩
    have := F.ray_fwd ψ F' σ hψ h3
    rwa [σ.apply_symm_apply, σ.apply_symm_apply, ψ.apply_symm_apply] at this
  · obtain ⟨hM, hray⟩ := h.mul_some r s t hm
    refine ⟨fun hM' ↦ hM ?_, ?_⟩
    · have := F'.insertionSpan_fwd ψ.symm F σ.symm hsym hM'
      simpa only [Equiv.trans_apply, Equiv.symm_apply_apply, Function.comp_apply,
        AlgEquiv.symm_apply_apply, map_mul] using this
    · have := F.ray_fwd ψ F' σ hψ hray
      simpa only [Equiv.trans_apply, Function.comp_apply, map_mul] using this
  · have := F.insertionSpan_fwd ψ F' σ hψ (h.mul_none r s hm hmid)
    simpa only [Equiv.trans_apply, Function.comp_apply, map_mul] using this

/-- **Connectivity transfers along ray presentations of one algebra.** -/
theorem IsRayPres.conn (h : F.IsRayPres (k := k) T ι β) (h' : F.IsRayPres (k := k) T' ι' β')
    (hc : T.Conn) : T'.Conn := by
  set ν : V → V' := fun x ↦ ι'.symm (ι x)
  have hrel : ∀ x y, Relation.EqvGen (fun x y ↦ ∃ r, T.src r = x ∧ T.tgt r = y) x y →
      Relation.EqvGen (fun x y ↦ ∃ r', T'.src r' = x ∧ T'.tgt r' = y) (ν x) (ν y) := by
    intro x y hxy
    induction hxy with
    | rel x y hr =>
      obtain ⟨r, rfl, rfl⟩ := hr
      obtain ⟨h1, h2, -⟩ := h.matchFn_spec h' r
      refine Relation.EqvGen.rel _ _ ⟨h.matchFn h' r, ?_, ?_⟩
      · simp only [ν, ← h1, Equiv.symm_apply_apply]
      · simp only [ν, ← h2, Equiv.symm_apply_apply]
    | refl => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro x' y'
  have hx : ν (ι.symm (ι' x')) = x' := by simp [ν]
  have hy : ν (ι.symm (ι' y')) = y' := by simp [ν]
  rw [← hx, ← hy]
  exact hrel _ _ (hc _ _)

end Unique

end PrimitiveIdempotents

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  (hfin : IsRepresentationFinite k (S.P.Lin k)) (c : R → R → k)

local notation:max "⌜" r "⌝" => Sys.rr S r

include hfin in
/-- **Corrections vanish below a ray**: on elements of `U(r)` of degree above `r`. -/
theorem coch_below {r : R} {x : S.P.Lin k}
    (hx : x ∈ S.USp k r ⊓ S.P.degSp k (S.P.deg (S.P.wt r) + 1)) (s : R) :
    S.coch k c x (S.P.b k s) = 0 := by
  have hx' : x ∈ Submodule.span k (S.P.basis k ''
      {t | S.InU t r ∧ S.P.deg (S.P.wt r) + 1 ≤ S.P.deg (S.P.wt t)}) := by
    rw [Module.Basis.mem_span_image]
    intro t ht
    have h1 : x ∈ S.USp k r := hx.1
    have h2 : x ∈ S.P.degSp k (S.P.deg (S.P.wt r) + 1) := hx.2
    rw [USp, Module.Basis.mem_span_image] at h1
    rw [Tab.degSp, Module.Basis.mem_span_image] at h2
    exact ⟨h1 ht, h2 ht⟩
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hz
    rw [Mult.basis_apply, coch_b]
    by_cases h0 : S.eps t s = 0
    · rw [h0, vecM_zero, smul_zero]
    · exfalso
      obtain ⟨-, hg, -, -, -⟩ := S.eps_ne_zero_spec k hfin h0
      obtain ⟨e1, e2, -⟩ := S.inU_endpoints ht1
      have := S.inU_antisymm ht1 (hg r e1.symm e2.symm)
      subst this
      omega
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add z z' _ _ h1 h2 => rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
  | smul t z _ h => rw [map_smul, LinearMap.smul_apply, h, smul_zero]

variable {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B] (Ψ : S.P.Lin k ≃ₗ[k] B)
  (hΨ : ∀ a z, Ψ (a * z + S.coch k c a z) = Ψ a * Ψ z)

local notation "σV" => S.fibreIdx k hfin c Ψ hΨ

include hfin hΨ in
/-- **The corner radical of the fibre** is the span of the positive local rays. -/
theorem fibre_cornerRadical_iff (y : V) {z : B} :
    z ∈ (S.fibreIdem k hfin c Ψ hΨ).cornerRadical (k := k) (σV y) ↔
      Ψ.symm z ∈ S.P.corSp k y y ⊓ S.P.degSp k 1 := by
  have hcorner : ∀ z, z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV y) (σV y) ↔
      Ψ.symm z ∈ S.P.corSp k y y := fun z ↦ by
    rw [S.fibre_mem_corner_iff, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hz, hzr⟩
    have ha := (hcorner z).1 hz
    refine ⟨ha, ?_⟩
    have hn := S.P.local_decomp k ha
    set cc := (S.P.basis k).repr (Ψ.symm z) (S.P.e y)
    by_cases hc : cc = 0
    · have : Ψ.symm z = Ψ.symm z - cc • S.P.b k (S.P.e y) := by rw [hc, zero_smul, sub_zero]
      rw [this]; exact hn.2
    · exfalso
      have hu : S.P.IsLocUnit k y (Ψ.symm z) := by
        have := S.P.isLocUnit_of k hc hn
        rwa [show cc • S.P.b k (S.P.e y) + (Ψ.symm z - cc • S.P.b k (S.P.e y)) = Ψ.symm z by
          abel] at this
      have hu' := (S.fibre_isCornerUnit_iff k hfin c Ψ hΨ (i := σV y)).2 (by
        rw [Equiv.symm_apply_apply]; exact hu)
      obtain ⟨-, z', -, h1, -⟩ := hu'
      apply (S.fibreIdem k hfin c Ψ hΨ).e_not_mem_radical (k := k) (σV y)
      rw [← h1]
      exact Ideal.mul_mem_right _ _ hzr
  · rintro ⟨ha, hd⟩
    have hz : z ∈ (S.fibreIdem k hfin c Ψ hΨ).corner (k := k) (σV y) (σV y) := (hcorner z).2 ha
    by_contra hzr
    have hu := (S.fibreIdem k hfin c Ψ hΨ).isCornerUnit_of_not_mem hz hzr
    rw [S.fibre_isCornerUnit_iff, Equiv.symm_apply_apply] at hu
    obtain ⟨-, a', ha', h1, -⟩ := hu
    have h0 : (0 : ℤ) ≤ 0 := le_rfl
    have hall : ∀ w : S.P.Lin k, w ∈ S.P.degSp k 0 := fun w ↦ by
      rw [S.P.mem_degSp_iff]; intro r _; exact S.P.deg_nonneg r
    have hm := S.P.mul_mem_degSp k hd (hall a')
    rw [add_zero, h1] at hm
    have := S.P.repr_e_of_mem_degSp k (x := y) hm
    rw [← Mult.basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
    exact one_ne_zero this

theorem _root_.MultiplicativeBasisDeformations.RaySys.Tab.e_mem_corSp' (P : Tab V R L) {x : V} :
    P.b k (P.e x) ∈ P.corSp k x x := P.b_mem_corSp' k (P.src_e x) (P.tgt_e x)

include hfin hΨ in
/-- Products through a positive local element are computed in `kP`. -/
theorem fibre_prod5 {r s : R} (hm : S.P.tgt r = S.P.src s) {a' n' w' : S.P.Lin k}
    (ha : a' ∈ S.P.corSp k (S.P.src r) (S.P.src r))
    (hn : n' ∈ S.P.corSp k (S.P.tgt r) (S.P.tgt r) ⊓ S.P.degSp k 1)
    (hw : w' ∈ S.P.corSp k (S.P.tgt s) (S.P.tgt s)) :
    Ψ a' * S.βv k Ψ r * Ψ n' * S.βv k Ψ s * Ψ w' = Ψ (a' * S.P.b k r * n' * S.P.b k s * w') := by
  have hall : ∀ w : S.P.Lin k, w ∈ S.P.degSp k 0 := fun w ↦ by
    rw [S.P.mem_degSp_iff]; intro r _; exact S.P.deg_nonneg r
  have hx : a' * S.P.b k r * n' ∈ S.USp k r ⊓ S.P.degSp k (S.P.deg (S.P.wt r) + 1) := by
    refine ⟨S.mul_mem_USp k rfl rfl ha hn.1, ?_⟩
    have := S.P.mul_mem_degSp k (S.P.mul_mem_degSp k (hall a')
      (S.P.b_mem_degSp k (r := r) le_rfl)) hn.2
    simpa using this
  rw [βv, βv, S.Ψ_mul_left k hfin c Ψ hΨ ha, S.Ψ_mul_right k hfin c Ψ hΨ hn.1, ← hΨ,
    S.coch_below k hfin c hx s, add_zero, S.Ψ_mul_right k hfin c Ψ hΨ hw]

include hfin hΨ in
/-- **`M(β r, β s)` lies in degrees above `deg r + deg s`.** -/
theorem fibre_insertionSpan_le {r s : R} (hm : S.P.tgt r = S.P.src s) :
    (S.fibreIdem k hfin c Ψ hΨ).insertionSpan (k := k) (σV (S.P.src r)) (σV (S.P.tgt r))
        (σV (S.P.tgt s)) (S.βv k Ψ r) (S.βv k Ψ s) ≤
      (S.P.degSp k (S.P.deg (S.P.wt r) + S.P.deg (S.P.wt s) + 1)).map Ψ.toLinearMap := by
  rw [PrimitiveIdempotents.insertionSpan, Submodule.span_le]
  rintro _ ⟨a, ha, n, hn, w, hw, rfl⟩
  rw [S.fibre_mem_corner_iff, Equiv.symm_apply_apply] at ha
  rw [S.fibre_mem_corner_iff, Equiv.symm_apply_apply] at hw
  have hn' := (S.fibre_cornerRadical_iff k hfin c Ψ hΨ (S.P.tgt r)).1 (by rwa [hm] at hn ⊢)
  rw [← Ψ.apply_symm_apply a, ← Ψ.apply_symm_apply n, ← Ψ.apply_symm_apply w]
  rw [hm] at hn'
  rw [← hm] at hn'
  rw [S.fibre_prod5 k hfin c Ψ hΨ hm ha hn' hw]
  refine ⟨_, ?_, rfl⟩
  have hall : ∀ w : S.P.Lin k, w ∈ S.P.degSp k 0 := fun w ↦ by
    rw [S.P.mem_degSp_iff]; intro r _; exact S.P.deg_nonneg r
  have := S.P.mul_mem_degSp k (S.P.mul_mem_degSp k (S.P.mul_mem_degSp k
    (S.P.mul_mem_degSp k (hall (Ψ.symm a)) (S.P.b_mem_degSp k (r := r) le_rfl)) hn'.2)
    (S.P.b_mem_degSp k (r := s) le_rfl)) (hall (Ψ.symm w))
  rw [show (0 : ℤ) + S.P.deg (S.P.wt r) + 1 + S.P.deg (S.P.wt s) + 0 =
    S.P.deg (S.P.wt r) + S.P.deg (S.P.wt s) + 1 by ring] at this
  exact this

include hfin hΨ in
/-- **The transported rays present the fibre by the ray table `P`** (Proposition 11.3(3)). -/
theorem fibre_rayPres :
    (S.fibreIdem k hfin c Ψ hΨ).IsRayPres (k := k) S.P.toMult (S.fibreIdx k hfin c Ψ hΨ)
      (S.βv k Ψ) := by
  set F := S.fibreIdem k hfin c Ψ hΨ
  refine ⟨S.βv_mem_corner k hfin c Ψ hΨ, S.βv_ne_zero k Ψ, fun r s h ↦ ?_,
    fun x y f hf hf0 ↦ S.exists_ray_βv k hfin c Ψ hΨ hf hf0, fun r s t h ↦ ?_, fun r s h hm ↦ ?_⟩
  · -- injectivity on rays
    have hcs := S.βv_mem_corner k hfin c Ψ hΨ s
    have hcr := S.βv_mem_corner k hfin c Ψ hΨ r
    have hcr' := F.ray_subset_corner hcs h
    obtain ⟨e1, e2⟩ := F.corner_unique hcr hcr' (S.βv_ne_zero k Ψ r)
    have h1 : S.InU r s := S.inU_of_mem_ray k hfin c Ψ hΨ h
    have hs : S.βv k Ψ s ∈ F.ray (k := k) (σV (S.P.src r)) (σV (S.P.tgt r)) (S.βv k Ψ r) := by
      rw [e1, e2, F.ray_eq_of_mem hcs h]; exact F.mem_ray_self hcs
    exact S.inU_antisymm h1 (S.inU_of_mem_ray k hfin c Ψ hΨ hs)
  · -- nonzero products
    have hrs : ⌜r⌝ * ⌜s⌝ = ⌜t⌝ := (S.P.rr_mul_rr_eq_rr).2 h
    have hmid := (S.P.mul_eq_rr_of hrs).2.2
    have hprod : S.βv k Ψ r * S.βv k Ψ s = S.βv k Ψ t := by
      rw [βv, βv, ← hΨ, coch_b, S.eps_of_mul_ne (by rw [hrs]; exact S.rr_ne t), vecM_zero,
        smul_zero, add_zero, S.b_mul_b k, hrs, vecM_rr]; rfl
    obtain ⟨t1, t2, -, t4⟩ := S.prod_of hrs
    refine ⟨fun hM ↦ ?_, ?_⟩
    · obtain ⟨z, hz, hzΨ⟩ := S.fibre_insertionSpan_le k hfin c Ψ hΨ hmid hM
      rw [hprod, βv] at hzΨ
      have hz' := Ψ.injective hzΨ
      rw [hz'] at hz
      have := (S.P.mem_degSp_iff k).1 hz t (by
        rw [← Mult.basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same]; exact one_ne_zero)
      rw [t4, map_add] at this
      omega
    · rw [hprod]
      exact F.mem_ray_self (S.βv_mem_corner k hfin c Ψ hΨ t)
  · -- zero products lie in `M(β r, β s)`
    have huv : ⌜r⌝ * ⌜s⌝ = 0 := (S.P.rr_mul_rr_eq_zero).2 h
    have hprod : S.βv k Ψ r * S.βv k Ψ s = c r s • Ψ (S.vecM k (S.eps r s)) := by
      rw [βv, βv, ← hΨ, coch_b, S.b_mul_b k, huv, vecM_zero, zero_add, map_smul]
    rw [hprod]
    refine Submodule.smul_mem _ _ ?_
    by_cases h0 : S.eps r s = 0
    · rw [h0, vecM_zero, map_zero]; exact zero_mem _
    obtain ⟨-, -, -, -, he⟩ := S.eps_ne_zero_spec k hfin h0
    rcases S.q_cases (S.P.tgt r) with hq | ⟨g, hg, g1, g2, gne⟩
    · rw [he, hq, mul_zero, zero_mul] at h0; exact absurd rfl h0
    have hgn : S.P.b k g ∈ S.P.corSp k (S.P.tgt r) (S.P.tgt r) ⊓ S.P.degSp k 1 :=
      ⟨S.P.b_mem_corSp' k g1 g2, S.P.b_mem_degSp k (by
        have := S.P.deg_pos g (by rw [g1]; exact gne); omega)⟩
    have hval : S.vecM k (S.eps r s) =
        S.P.b k (S.P.e (S.P.src r)) * S.P.b k r * S.P.b k g * S.P.b k s *
          S.P.b k (S.P.e (S.P.tgt s)) := by
      rw [Mult.b_e_mul, if_pos rfl, mul_assoc _ (S.P.b k s), Mult.b_mul_e, if_pos rfl,
        S.b_mul_b k r g]
      rw [he, hg] at h0 ⊢
      rcases S.rr_mul_rr_cases r g with h1 | ⟨u, hu⟩
      · rw [h1, zero_mul] at h0; exact absurd rfl h0
      · rw [hu, vecM_rr, S.b_mul_b k]
    rw [hval, ← S.fibre_prod5 k hfin c Ψ hΨ hm (S.P.e_mem_corSp' k) hgn (S.P.e_mem_corSp' k)]
    refine Submodule.subset_span ⟨Ψ (S.P.b k (S.P.e (S.P.src r))), ?_, Ψ (S.P.b k g), ?_,
      Ψ (S.P.b k (S.P.e (S.P.tgt s))), ?_, by simp only [mul_assoc]⟩
    · rw [S.fibre_mem_corner_iff, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact S.P.e_mem_corSp' k
    · exact (S.fibre_cornerRadical_iff k hfin c Ψ hΨ _).2 (by
        rw [LinearEquiv.symm_apply_apply]; exact hgn)
    · rw [S.fibre_mem_corner_iff, Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact S.P.e_mem_corSp' k

end Sys

end RaySys

end MultiplicativeBasisDeformations
