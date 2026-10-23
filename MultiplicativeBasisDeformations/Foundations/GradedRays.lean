module

public import MultiplicativeBasisDeformations.Foundations.RayDegree

/-!
# Homogeneous rays of a length-graded algebra

Proposition 3.8 (`projective-rays.tex`), for a length-graded
representation-finite algebra with idempotents in degree zero and
`deg 0` corners `k e_x` (the case of `A₀`):

1. "each nonzero ray contains the nonzero vectors of a unique homogeneous
   line" (`exists_hom_mem_ray`, `mem_span_of_ray_eq`);
2. "For homogeneous `f, g` of degrees `p, q`, every element of `M(f,g)` has
   homogeneous components only in degrees greater than `p+q`. Thus
   `fg ∈ M(f,g)` exactly when `fg = 0`" (`mul_mem_insertionSpan_iff`);
3. "Associativity of `A₀` now gives (3)" (`rayProduct_assoc`, for arbitrary
   representatives, through Lemma 3.6).

Then a homogeneous normed multiplicative basis containing the `e_x` is, after
reindexing, a ray transversal killing zero ray products (`hasRayBasis_of_graded`):
this is the "ray basis" of Corollary 5.5(2).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

section Reindex

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B]

/-- A normed multiplicative basis stays normed after reindexing. -/
theorem IsNormedMultiplicativeBasis.reindex {ι ι' : Type*} {b : Module.Basis ι k B}
    (hb : IsNormedMultiplicativeBasis b) (e : ι ≃ ι') :
    IsNormedMultiplicativeBasis (b.reindex e) := by
  classical
  refine ⟨fun i j ↦ ?_, ?_, fun n hn ↦ ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    rcases hb.multiplicative (e.symm i) (e.symm j) with h | ⟨l, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨e l, by rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]; exact hl⟩
  · obtain ⟨E, hE, hp⟩ := hb.idempotents
    let σ : E ≃ E.map e.toEmbedding := Equiv.ofBijective
      (fun i ↦ ⟨e i, Finset.mem_map_of_mem _ i.2⟩)
      ⟨fun i j h ↦ Subtype.ext (e.injective (congrArg Subtype.val h)), fun ⟨t, ht⟩ ↦ by
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ht
        exact ⟨⟨i, hi⟩, rfl⟩⟩
    refine ⟨E.map e.toEmbedding, (CompleteOrthogonalIdempotents.equiv σ).1 ?_, fun t ht ↦ ?_⟩
    · have hfun : ((fun i : E.map e.toEmbedding ↦ b.reindex e i) ∘ σ) = fun i : E ↦ b i :=
        funext fun i ↦ by
          change b.reindex e (e i) = b i
          rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
      rw [hfun]; exact hE
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ht
      change IsPrimitiveIdempotent (b.reindex e (e i))
      rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
      exact hp i hi
  · refine Eq.trans ?_ (hb.radicalPow n hn)
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq, Module.Basis.reindex_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨e.symm i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨e i, by rw [Equiv.symm_apply_apply]; exact hi, by
        rw [Equiv.symm_apply_apply]⟩

end Reindex

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Algebra k B]

variable (k) in
/-- `B` has a ray basis for `F`: a normed multiplicative basis indexed by the
nonzero rays, a ray transversal, with zero ray products giving zero products
(Corollary 5.5(2), Theorem 11.7(2)(3)). -/
def HasRayBasis (F : PrimitiveIdempotents B) : Prop :=
  ∃ b : Module.Basis (F.NonzeroRay k) k B, IsNormedMultiplicativeBasis b ∧
    F.IsRayTransversal b ∧ F.KillsZeroRayProducts b

variable [IsAlgClosed k] [FiniteDimensional k B] (G : LenGrading k B) (F : PrimitiveIdempotents B)
  (he0 : ∀ x, G.IsHom 0 (F.e x))
  (hcorner0 : ∀ (x : Fin F.m) (a : B), a ∈ F.corner (k := k) x x → G.IsHom 0 a →
    ∃ c : k, a = c • F.e x)

include he0 hcorner0 in
/-- `M(f, h)` lies in degrees above `p + q`. -/
theorem insertionSpan_ge {x y z : Fin F.m} {f h : B} {p q : ℕ} (hfp : G.IsHom p f)
    (hhq : G.IsHom q h) {w : B} (hw : w ∈ F.insertionSpan (k := k) x y z f h) :
    G.Ge (p + q + 1) w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨a, -, r, hr, b, -, rfl⟩ := hw
      have := G.ge_mul (G.ge_mul (G.ge_mul (G.ge_mul (G.ge_zero a) (G.ge_of_isHom hfp))
        (F.rad_ge G he0 hcorner0 y hr)) (G.ge_of_isHom hhq)) (G.ge_zero b)
      exact G.ge_mono (by omega) this
  | zero => exact fun e _ ↦ map_zero _
  | add w w' _ _ hw hw' => exact G.ge_add hw hw'
  | smul c w _ hw => exact G.ge_smul c hw

include he0 hcorner0 in
/-- **Proposition 3.8(2)**: for homogeneous `f, h`, `fh ∈ M(f,h)` iff `fh = 0`. -/
theorem mul_mem_insertionSpan_iff {x y z : Fin F.m} {f h : B} {p q : ℕ} (hfp : G.IsHom p f)
    (hhq : G.IsHom q h) :
    f * h ∈ F.insertionSpan (k := k) x y z f h ↔ f * h = 0 := by
  refine ⟨fun hM ↦ ?_, fun h0 ↦ h0 ▸ Submodule.zero_mem _⟩
  have hge := F.insertionSpan_ge G he0 hcorner0 hfp hhq hM
  have hhom := G.isHom_mul hfp hhq
  rw [← hhom]
  exact hge (p + q) (by omega)

include he0 hcorner0 in
/-- A homogeneous element of `U(g)` has degree at least that of `g`, and the same
degree only on the line of `g`. -/
theorem hom_mem_endpointSpan {x y : Fin F.m} {g g' : B} (hg : g ∈ F.corner (k := k) x y)
    {d d' : ℕ} (hgd : G.IsHom d g) (hg'd : G.IsHom d' g') (hg'0 : g' ≠ 0)
    (hg' : g' ∈ F.endpointSpan (k := k) x y g) : d ≤ d' ∧ (d' = d → g' ∈ k ∙ g) := by
  rw [F.endpointSpan_eq hg] at hg'
  obtain ⟨v, hv, r, hr, rfl⟩ := Submodule.mem_sup.1 hg'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hrge := F.endpointRadical_ge G he0 hcorner0 hgd hr
  have hproj : ∀ e, e ≤ d → G.proj e (c • g + r) = if d = e then c • g else 0 := fun e he ↦ by
    rw [map_add, map_smul, G.proj_of_isHom hgd, hrge e (by omega), add_zero]
    split_ifs <;> simp
  refine ⟨?_, fun hdd ↦ ?_⟩
  · by_contra hlt
    apply hg'0
    rw [← hg'd, hproj d' (by omega), if_neg (by omega)]
  · rw [hdd] at hg'd
    rw [← hg'd, hproj d le_rfl, if_pos rfl]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self g)

include he0 hcorner0 in
/-- **Proposition 3.8(1), uniqueness**: homogeneous elements of one ray lie on one
line. -/
theorem mem_span_of_ray_eq {x y : Fin F.m} {g g' : B} (hg : g ∈ F.corner (k := k) x y)
    (hg' : g' ∈ F.corner (k := k) x y) (hg'0 : g' ≠ 0) {d d' : ℕ} (hgd : G.IsHom d g)
    (hg'd : G.IsHom d' g') (h : F.ray (k := k) x y g' = F.ray (k := k) x y g) : g' ∈ k ∙ g := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    have := F.mem_ray_self hg'
    rw [h] at this
    obtain ⟨u, w, -, -, hu⟩ := this
    exact hg'0 (by rw [hu, mul_zero, zero_mul])
  have hgg' : g' ∈ F.ray (k := k) x y g := h ▸ F.mem_ray_self hg'
  have hU := F.endpointSpan_eq_of_mem_ray hg hgg'
  have h1 := F.hom_mem_endpointSpan G he0 hcorner0 hg hgd hg'd hg'0
    (hU ▸ F.mem_endpointSpan_self hg')
  have h2 := F.hom_mem_endpointSpan G he0 hcorner0 hg' hg'd hgd hg0
    (hU.symm ▸ F.mem_endpointSpan_self hg)
  exact h1.2 (le_antisymm h2.1 h1.1)

variable [Infinite k] (hA : IsRepresentationFinite k B)

include he0 hcorner0 hA in
/-- **Proposition 3.8(1), existence**: every nonzero ray contains a homogeneous
element. -/
theorem exists_hom_mem_ray {x y : Fin F.m} {f : B} (hf : f ∈ F.corner (k := k) x y)
    (hf0 : f ≠ 0) : ∃ g d, G.IsHom d g ∧ g ≠ 0 ∧ g ∈ F.ray (k := k) x y f := by
  have hU := F.isEndpoint_endpointSpan hf
  have hU0 : F.endpointSpan (k := k) x y f ≠ ⊥ := fun h ↦
    hf0 ((Submodule.mem_bot k).1 (h ▸ F.mem_endpointSpan_self hf))
  obtain ⟨g, d, hgd, hg0, hgU, hUg⟩ := F.layer G he0 hcorner0 hA hU hU0
  have hgC := hU.1 hgU
  refine ⟨g, d, hgd, hg0, ?_⟩
  rw [F.ray_eq_of_endpointSpan_eq hA hgC hg0 hf hUg]
  exact F.mem_ray_self hgC

include he0 hcorner0 hA in
/-- With homogeneous representatives, `fh ∉ M(f,h)` iff `f₀h₀ ≠ 0`, and then
`f₀h₀ ∈ [fh]`. -/
theorem notMem_insertionSpan_iff {x y z : Fin F.m} {f h f₀ h₀ : B}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (hh : h ∈ F.corner (k := k) y z)
    (hh0 : h ≠ 0) (hf₀ : f₀ ∈ F.ray (k := k) x y f) (hh₀ : h₀ ∈ F.ray (k := k) y z h)
    {p q : ℕ} (hfp : G.IsHom p f₀) (hhq : G.IsHom q h₀) :
    (f * h ∉ F.insertionSpan (k := k) x y z f h ↔ f₀ * h₀ ≠ 0) ∧
      (f * h ∉ F.insertionSpan (k := k) x y z f h → f₀ * h₀ ∈ F.ray (k := k) x z (f * h)) := by
  have hind := F.rayProduct_independent_of hA hf hf0 hh hh0 hf₀ hh₀
  have hiff := F.mul_mem_insertionSpan_iff (x := x) (y := y) (z := z) G he0 hcorner0 hfp hhq
  refine ⟨by rw [hind.1, hiff], fun hM ↦ ?_⟩
  obtain ⟨-, hray⟩ := hind.2 hM
  rw [hray]
  exact F.mem_ray_self (F.corner_mul_corner (F.ray_subset_corner hf hf₀)
    (F.ray_subset_corner hh hh₀))

include he0 hcorner0 hA in
/-- **Proposition 3.8(3)**: the ray table is associative. For nonzero
representatives, `([f][g])[h] ≠ 0` iff `[f]([g][h]) ≠ 0` (and then both are the
ray of `fgh`). -/
theorem rayProduct_assoc {x y z w : Fin F.m} {f g h : B}
    (hf : f ∈ F.corner (k := k) x y) (hf0 : f ≠ 0) (hg : g ∈ F.corner (k := k) y z)
    (hg0 : g ≠ 0) (hh : h ∈ F.corner (k := k) z w) (hh0 : h ≠ 0) :
    (f * g ∉ F.insertionSpan (k := k) x y z f g ∧
        f * g * h ∉ F.insertionSpan (k := k) x z w (f * g) h) ↔
      (g * h ∉ F.insertionSpan (k := k) y z w g h ∧
        f * (g * h) ∉ F.insertionSpan (k := k) x y w f (g * h)) := by
  obtain ⟨f₀, p, hfp, -, hf₀⟩ := F.exists_hom_mem_ray G he0 hcorner0 hA hf hf0
  obtain ⟨g₀, q, hgq, -, hg₀⟩ := F.exists_hom_mem_ray G he0 hcorner0 hA hg hg0
  obtain ⟨h₀, r, hhr, -, hh₀⟩ := F.exists_hom_mem_ray G he0 hcorner0 hA hh hh0
  have hfg := F.notMem_insertionSpan_iff G he0 hcorner0 hA hf hf0 hg hg0 hf₀ hg₀ hfp hgq
  have hgh := F.notMem_insertionSpan_iff G he0 hcorner0 hA hg hg0 hh hh0 hg₀ hh₀ hgq hhr
  have hfgc := F.corner_mul_corner hf hg
  have hghc := F.corner_mul_corner hg hh
  constructor
  · rintro ⟨h1, h2⟩
    have hfg0 : f * g ≠ 0 := fun h0 ↦ h1 (h0 ▸ Submodule.zero_mem _)
    have h3 := F.notMem_insertionSpan_iff G he0 hcorner0 hA hfgc hfg0 hh hh0 (hfg.2 h1) hh₀
      (G.isHom_mul hfp hgq) hhr
    have hprod : f₀ * g₀ * h₀ ≠ 0 := h3.1.1 h2
    have hgh0 : g₀ * h₀ ≠ 0 := fun h0 ↦ hprod (by rw [mul_assoc, h0, mul_zero])
    have h4 := hgh.1.2 hgh0
    have hgh' : g * h ≠ 0 := fun h0 ↦ h4 (h0 ▸ Submodule.zero_mem _)
    have h5 := F.notMem_insertionSpan_iff G he0 hcorner0 hA hf hf0 hghc hgh' hf₀ (hgh.2 h4)
      hfp (G.isHom_mul hgq hhr)
    exact ⟨h4, h5.1.2 (by rwa [← mul_assoc])⟩
  · rintro ⟨h1, h2⟩
    have hgh0 : g * h ≠ 0 := fun h0 ↦ h1 (h0 ▸ Submodule.zero_mem _)
    have h3 := F.notMem_insertionSpan_iff G he0 hcorner0 hA hf hf0 hghc hgh0 hf₀ (hgh.2 h1)
      hfp (G.isHom_mul hgq hhr)
    have hprod : f₀ * (g₀ * h₀) ≠ 0 := h3.1.1 h2
    have hfg0 : f₀ * g₀ ≠ 0 := fun h0 ↦ hprod (by rw [← mul_assoc, h0, zero_mul])
    have h4 := hfg.1.2 hfg0
    have hfg' : f * g ≠ 0 := fun h0 ↦ h4 (h0 ▸ Submodule.zero_mem _)
    have h5 := F.notMem_insertionSpan_iff G he0 hcorner0 hA hfgc hfg' hh hh0 (hfg.2 h4) hh₀
      (G.isHom_mul hfp hgq) hhr
    exact ⟨h4, h5.1.2 (by rwa [mul_assoc])⟩

theorem isCornerUnit_smul_e (x : Fin F.m) {c : k} (hc : c ≠ 0) :
    F.IsCornerUnit (k := k) x (c • F.e x) :=
  ⟨Submodule.smul_mem _ c (F.e_mem_corner x), c⁻¹ • F.e x, Submodule.smul_mem _ _ (F.e_mem_corner x),
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, (F.complete.idem x).eq],
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, (F.complete.idem x).eq]⟩

theorem isHom_unique {d d' : ℕ} {a : B} (ha0 : a ≠ 0) (h : G.IsHom d a) (h' : G.IsHom d' a) :
    d = d' := by
  by_contra hdd
  apply ha0
  rw [← h, G.proj_of_isHom h', if_neg (Ne.symm hdd)]

variable {ι : Type*} (b : Module.Basis ι k B)
  (hb : ∀ i, ∃ x y d, b i ∈ F.corner (k := k) x y ∧ G.IsHom d (b i))

include he0 hcorner0 hA hb in
/-- A homogeneous nonzero element of a corner is a nonzero multiple of a basis
vector of that corner. -/
theorem exists_basis_line {x y : Fin F.m} {d : ℕ} {g : B} (hg : g ∈ F.corner (k := k) x y)
    (hgd : G.IsHom d g) (hg0 : g ≠ 0) :
    ∃ (i : ι) (c : k), c ≠ 0 ∧ g = c • b i ∧ b i ∈ F.corner (k := k) x y := by
  classical
  set T := {i | b i ∈ F.corner (k := k) x y ∧ G.IsHom d (b i)}
  have hT : ∀ i, G.proj d (F.e x * b i * F.e y) = if i ∈ T then b i else 0 := by
    intro i
    obtain ⟨x', y', d', hi', hid'⟩ := hb i
    rw [F.proj_corner_basis G he0 b i hi' hid']
    by_cases hiT : i ∈ T
    · obtain ⟨rfl, rfl⟩ := F.corner_unique hi' hiT.1 (b.ne_zero i)
      rw [if_pos ⟨rfl, rfl, isHom_unique G (b.ne_zero i) hid' hiT.2⟩, if_pos hiT]
    · rw [if_neg hiT, if_neg]
      rintro ⟨rfl, rfl, rfl⟩
      exact hiT ⟨hi', hid'⟩
  have hexp : g = ∑ i ∈ (b.repr g).support, b.repr g i • (if i ∈ T then b i else 0) := by
    have h1 : g = G.proj d (F.e x * g * F.e y) := by rw [(F.mem_corner_iff').1 hg, hgd]
    conv_lhs => rw [h1, ← b.linearCombination_repr g, Finsupp.linearCombination_apply,
      Finsupp.sum]
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_smul_comm, smul_mul_assoc, map_smul, hT]
  obtain ⟨w, hw⟩ := F.lines G he0 hcorner0 hA _ (F.corner (k := k) x y) rfl
    (F.corner_isEndpoint x y) d
  have hunique : ∀ i ∈ T, ∀ j ∈ T, i = j := by
    intro i hi j hj
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hw _ hi.1 hi.2)
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 (hw _ hj.1 hj.2)
    have hc'0 : c' ≠ 0 := fun h0 ↦ b.ne_zero j (by rw [← hc', h0, zero_smul])
    have : b i = (c * c'⁻¹) • b j := by rw [← hc, ← hc', smul_smul, mul_assoc,
      inv_mul_cancel₀ hc'0, mul_one]
    by_contra hij
    have hr := congrArg (fun v ↦ b.repr v i) this
    simp only [Module.Basis.repr_self, map_smul, Finsupp.smul_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, smul_zero] at hr
    exact one_ne_zero hr
  obtain ⟨i, hi, hiT⟩ : ∃ i ∈ (b.repr g).support, i ∈ T := by
    by_contra hcon
    push Not at hcon
    apply hg0
    rw [hexp]
    exact Finset.sum_eq_zero fun i hi ↦ by rw [if_neg (hcon i hi), smul_zero]
  refine ⟨i, b.repr g i, Finsupp.mem_support_iff.1 hi, ?_, hiT.1⟩
  conv_lhs => rw [hexp]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (fun h ↦ absurd hi h), if_pos hiT]
  split_ifs with hjT
  · exact absurd (hunique j hjT i hiT) hji
  · rw [smul_zero]

include he0 hcorner0 hA hb in
/-- **The ray basis of a length-graded algebra**: a homogeneous normed
multiplicative basis containing the `e_x` is a ray transversal killing zero ray
products (Proposition 3.8, Corollary 3.3). -/
theorem hasRayBasis_of_graded (hnorm : IsNormedMultiplicativeBasis b)
    (hid : ∀ x, ∃ i, b i = F.e x) : F.HasRayBasis k := by
  classical
  choose cx cy dg hcorner hdeg using hb
  let ρ : ι → F.NonzeroRay k := fun i ↦
    ⟨F.ray (k := k) (cx i) (cy i) (b i), cx i, cy i, b i, hcorner i, b.ne_zero i, rfl⟩
  have hρ : ∀ i x y, b i ∈ F.corner (k := k) x y → (ρ i).1 = F.ray (k := k) x y (b i) := by
    intro i x y hi
    obtain ⟨h1, h2⟩ := F.corner_unique (hcorner i) hi (b.ne_zero i)
    change F.ray (k := k) (cx i) (cy i) (b i) = _
    rw [h1, h2]
  have hinj : Function.Injective ρ := by
    intro i j hij
    have hs := congrArg Subtype.val hij
    have hbj : b j ∈ F.ray (k := k) (cx i) (cy i) (b i) := by
      change b j ∈ (ρ i).1
      rw [hs]
      exact F.mem_ray_self (hcorner j)
    have hbjc := F.ray_subset_corner (hcorner i) hbj
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (F.mem_span_of_ray_eq G he0 hcorner0
      (hcorner i) hbjc (b.ne_zero j) (hdeg i) (hdeg j) (F.ray_eq_of_mem (hcorner i) hbj))
    by_contra hne
    have hr := congrArg (fun v ↦ b.repr v i) hc
    simp only [Module.Basis.repr_self, map_smul, Finsupp.smul_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one] at hr
    exact b.ne_zero j (by rw [← hc, hr, zero_smul])
  have hsurj : Function.Surjective ρ := by
    rintro ⟨S, x, y, f, hf, hf0, rfl⟩
    obtain ⟨g, d, hgd, hg0, hg⟩ := F.exists_hom_mem_ray G he0 hcorner0 hA hf hf0
    have hgc := F.ray_subset_corner hf hg
    obtain ⟨i, c, hc, rfl, hic⟩ := F.exists_basis_line G he0 hcorner0 hA b
      (fun i ↦ ⟨cx i, cy i, dg i, hcorner i, hdeg i⟩) hgc hgd hg0
    refine ⟨i, Subtype.ext ?_⟩
    show (ρ i).1 = F.ray (k := k) x y f
    rw [hρ i x y hic, ← F.ray_eq_of_mem hf hg]
    refine (F.ray_eq_of_mem hic ⟨c • F.e x, F.e y, F.isCornerUnit_smul_e x hc,
      F.isCornerUnit_e y, ?_⟩).symm
    rw [smul_mul_assoc, F.e_mul_of_mem hic, smul_mul_assoc, F.mul_e_of_mem hic]
  let e := Equiv.ofBijective ρ ⟨hinj, hsurj⟩
  have he : ∀ r, ρ (e.symm r) = r := fun r ↦ e.apply_symm_apply r
  refine ⟨b.reindex e, hnorm.reindex e, ⟨fun r ↦ ?_, fun r x hx ↦ ?_⟩, ?_⟩
  · rw [Module.Basis.reindex_apply]
    have := F.mem_ray_self (hcorner (e.symm r))
    change b (e.symm r) ∈ (ρ (e.symm r)).1 at this
    rwa [he r] at this
  · rw [Module.Basis.reindex_apply]
    set i := e.symm r
    obtain ⟨j, hj⟩ := hid x
    have hx' : F.e x ∈ (ρ i).1 := by rw [he r]; exact hx
    have hxc := F.ray_subset_corner (hcorner i) hx'
    obtain ⟨h1, h2⟩ := F.corner_unique hxc (F.e_mem_corner x) (F.primitive x).2.1
    have hij : ρ i = ρ j := by
      apply Subtype.ext
      rw [hρ j x x (hj ▸ F.e_mem_corner x), hj]
      change F.ray (k := k) (cx i) (cy i) (b i) = _
      rw [← F.ray_eq_of_mem (hcorner i) hx', h1, h2]
    rw [hinj hij, hj]
  · intro r s x y z hr hs hM
    rw [Module.Basis.reindex_apply] at hr hM ⊢
    rw [Module.Basis.reindex_apply] at hs hM ⊢
    exact (F.mul_mem_insertionSpan_iff G he0 hcorner0 (hdeg _) (hdeg _)).1 hM

end PrimitiveIdempotents

end MultiplicativeBasisDeformations
