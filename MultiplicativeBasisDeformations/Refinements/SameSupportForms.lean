module

public import MultiplicativeBasisDeformations.Refinements.MeshNormalForm
public import MultiplicativeBasisDeformations.Foundations.MeshGauge
public import MultiplicativeBasisDeformations.Foundations.PeriodicComponents

/-!
# Lemma 12.6: mesh normal forms with the same support

`deformation-refinements.tex` (`lem:same-support-forms`). Let `C(λ)` be the mesh normal
forms `kQ/(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)` of Proposition 12.2, with the residual paths `p_i`,
each internal to its own periodic component. If `λ_i = 0` exactly when `λ'_i = 0`, then
`C(λ) ≅ C(λ')` by an object-preserving isomorphism.

The proof is the source's. Choose `a_i ∈ kˣ`; prescribe `μ_a = a_i` on the internal arrows of
the `i`th residual component and the row scale `a_i²` on its vertices, scale one on the other
periodic components. The mate map `σ` on arrows has chains and cycles; its cycles lie in the
periodic part (`σ²` translates both endpoints), so the scale equations
`μ_{σa} μ_a = η_v` (`eq:global-mesh-scales`) can be solved successively along every chain, with
no closing condition (`exists_chain_solution`). The diagonal map sends `r_v ↦ η_v r_v` and
`p_i ↦ a_i^{d_i} p_i`, so it changes `λ_i` to `λ_i a_i^{d_i-2}`; take `a_i` a root of
`λ'_i/λ_i`.

Generalizations: any characteristic, any mesh coefficients (the same on both sides), any
finite translation quiver; the residual rows are any rows of length at least three, internal to
pairwise distinct periodic components.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace SameSupport

/-! ### Solving scale equations along chains -/

section Chains

variable {X : Type*} (σ : X → Option X)

/-- Iterates of a partial map. -/
def oiter : ℕ → X → Option X
  | 0, a => some a
  | n + 1, a => (oiter n a).bind σ

theorem oiter_add (m n : ℕ) (a : X) : oiter σ (m + n) a = (oiter σ n a).bind (oiter σ m) := by
  induction m with
  | zero => simp [oiter]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, oiter, ih, Option.bind_assoc]
    rfl

theorem oiter_one (a : X) : oiter σ 1 a = σ a := by simp [oiter]

variable [Fintype X]

open Classical in
/-- The strict backward orbit of `b`. -/
def back (b : X) : Finset X := Finset.univ.filter fun a ↦ ∃ n, 1 ≤ n ∧ oiter σ n a = some b

theorem back_eq [DecidableEq X] (hinj : ∀ a b c, σ a = some c → σ b = some c → a = b) {a b : X}
    (hab : σ a = some b) (hcyc : ∀ n, 1 ≤ n → oiter σ n a ≠ some a) :
    back σ b = insert a (back σ a) ∧ a ∉ back σ a := by
  classical
  refine ⟨?_, ?_⟩
  · ext x
    simp only [back, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨n, hn, hx⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      change (oiter σ m x).bind σ = some b at hx
      cases hy : oiter σ m x with
      | none => rw [hy] at hx; simp at hx
      | some y =>
        rw [hy, Option.bind_some] at hx
        have := hinj _ _ _ hx hab
        subst this
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · left
          simp only [oiter, Option.some.injEq] at hy
          exact hy
        · right; exact ⟨m, hm, hy⟩
    · rintro (rfl | ⟨n, hn, hx⟩)
      · exact ⟨1, le_rfl, by rw [oiter_one, hab]⟩
      · refine ⟨n + 1, by omega, ?_⟩
        change (oiter σ n x).bind σ = some b
        rw [hx, Option.bind_some, hab]
  · simp only [back, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    exact hcyc

/-- The alternating products along a chain. -/
def chainF {M : Type*} [CommGroup M] (pred : X → Option X) (e : X → M) : ℕ → X → M
  | 0, _ => 1
  | n + 1, b => match pred b with
    | none => 1
    | some a => e a / chainF pred e n a

/-- **Solving `μ(σ a) μ(a) = e(a)` along chains**: on a finite set, a partial injective map `σ`
without cycles outside a `σ`-closed set `P` allows any solution on `P` to be extended. -/
theorem exists_chain_solution {M : Type*} [CommGroup M]
    (hinj : ∀ a b c, σ a = some c → σ b = some c → a = b)
    (P : X → Prop) (hP : ∀ a b, σ a = some b → (P a ↔ P b))
    (hcyc : ∀ a, ¬ P a → ∀ n, 1 ≤ n → oiter σ n a ≠ some a)
    (e μ₀ : X → M) (h₀ : ∀ a b, σ a = some b → P a → μ₀ b * μ₀ a = e a) :
    ∃ μ : X → M, (∀ a, P a → μ a = μ₀ a) ∧ ∀ a b, σ a = some b → μ b * μ a = e a := by
  classical
  let pred : X → Option X := fun b ↦ if h : ∃ a, σ a = some b then some h.choose else none
  have hpred : ∀ a b, σ a = some b → pred b = some a := by
    intro a b hab
    have h : ∃ a, σ a = some b := ⟨a, hab⟩
    simp only [pred, dif_pos h]
    exact congrArg some (hinj _ _ _ h.choose_spec hab)
  refine ⟨fun b ↦ if P b then μ₀ b else chainF pred e (back σ b).card b, fun a ha ↦ if_pos ha,
    fun a b hab ↦ ?_⟩
  by_cases ha : P a
  · have hb := (hP a b hab).1 ha
    simp only [if_pos ha, if_pos hb]
    exact h₀ a b hab ha
  · have hb : ¬ P b := fun hb ↦ ha ((hP a b hab).2 hb)
    simp only [if_neg ha, if_neg hb]
    obtain ⟨hback, hnot⟩ := back_eq σ hinj hab (hcyc a ha)
    rw [hback, Finset.card_insert_of_notMem hnot]
    simp only [chainF, hpred a b hab]
    exact div_mul_cancel _ _

end Chains

/-! ### The mate map on arrows -/

section Mate

variable {V : Type} [Quiver.{0} V] (Q : TranslationQuiver V)

/-- The arrows of the quiver. -/
abbrev Arr (V : Type) [Quiver.{0} V] := Σ u v : V, u ⟶ v

open Classical in
/-- **The mate map** `σ`: `a : u → v` with `v` nonprojective goes to `σ a : τ v → u`. -/
def mateMap (a : Arr V) : Option (Arr V) :=
  if h : a.2.1 ∈ Q.nonprojective then
    some ⟨(Q.tau ⟨a.2.1, h⟩).1, a.1, Q.mate ⟨a.2.1, h⟩ a.1 a.2.2⟩
  else none

theorem mateMap_of_mem {u v : V} (α : u ⟶ v) (h : v ∈ Q.nonprojective) :
    mateMap Q ⟨u, v, α⟩ = some ⟨(Q.tau ⟨v, h⟩).1, u, Q.mate ⟨v, h⟩ u α⟩ := by
  simp [mateMap, h]

theorem mateMap_eq_some {a b : Arr V} (h : mateMap Q a = some b) :
    ∃ h : a.2.1 ∈ Q.nonprojective, b = ⟨(Q.tau ⟨a.2.1, h⟩).1, a.1, Q.mate ⟨a.2.1, h⟩ a.1 a.2.2⟩ := by
  unfold mateMap at h
  split_ifs at h with h'
  exact ⟨h', (Option.some.inj h).symm⟩

theorem mateMap_inj (a b c : Arr V) (ha : mateMap Q a = some c) (hb : mateMap Q b = some c) :
    a = b := by
  obtain ⟨u, v, α⟩ := a
  obtain ⟨u', v', α'⟩ := b
  obtain ⟨h, rfl⟩ := mateMap_eq_some Q ha
  obtain ⟨h', e⟩ := mateMap_eq_some Q hb
  simp only [Sigma.mk.inj_iff] at e
  obtain ⟨e1, e2⟩ := e
  have hv : v = v' := congrArg Subtype.val (Q.tau.injective (Subtype.ext e1))
  subst hv
  obtain ⟨hu, hα⟩ := Sigma.mk.inj_iff.1 (eq_of_heq e2)
  subst hu
  have := (Q.mate ⟨v, h⟩ u).injective (eq_of_heq hα)
  subst this
  rfl

/-- The arrows with both endpoints periodic. -/
def PerArr (a : Arr V) : Prop := a.1 ∈ Q.periodic ∧ a.2.1 ∈ Q.periodic

theorem mem_periodic_tau_iff {v : V} (h : v ∈ Q.nonprojective) :
    (Q.tau ⟨v, h⟩).1 ∈ Q.periodic ↔ v ∈ Q.periodic := by
  change Q.IsTauPeriodic _ ↔ Q.IsTauPeriodic v
  rw [TranslationQuiver.isTauPeriodic_iff v]
  exact ⟨fun h' ↦ ⟨h, h'⟩, fun ⟨_, h'⟩ ↦ h'⟩

theorem perArr_iff {a b : Arr V} (h : mateMap Q a = some b) : PerArr Q a ↔ PerArr Q b := by
  obtain ⟨h, rfl⟩ := mateMap_eq_some Q h
  simp only [PerArr, mem_periodic_tau_iff]
  exact and_comm

/-- `σ²` translates the target: if `2m` iterates are defined, `τ^j` of the target is defined
for `j < m`. -/
theorem tauChain_of_oiter : ∀ (m : ℕ) (a : Arr V), oiter (mateMap Q) (2 * m) a ≠ none →
    Q.TauChain a.2.1 m := by
  intro m
  induction m with
  | zero => intro _ _; trivial
  | succ m ih =>
    intro a ha
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, oiter_add] at ha
    obtain ⟨u, v, α⟩ := a
    by_cases hv : v ∈ Q.nonprojective
    · have h1 := mateMap_of_mem Q α hv
      have e2 : oiter (mateMap Q) 2 ⟨u, v, α⟩ = mateMap Q ⟨(Q.tau ⟨v, hv⟩).1, u,
          Q.mate ⟨v, hv⟩ u α⟩ := by
        change ((some _).bind (mateMap Q)).bind (mateMap Q) = _
        rw [Option.bind_some, h1, Option.bind_some]
      rw [e2] at ha
      by_cases hu : u ∈ Q.nonprojective
      · rw [mateMap_of_mem Q _ hu, Option.bind_some] at ha
        exact ⟨hv, ih _ ha⟩
      · exfalso; apply ha; simp [mateMap, hu]
    · exfalso; apply ha
      change ((((some _).bind (mateMap Q)).bind (mateMap Q))).bind _ = none
      simp [mateMap, hv]

theorem perArr_of_oiter {a : Arr V} (ha : ∀ m, oiter (mateMap Q) m a ≠ none) : PerArr Q a := by
  have htgt : ∀ b : Arr V, (∀ m, oiter (mateMap Q) m b ≠ none) → b.2.1 ∈ Q.periodic :=
    fun b hb m ↦ tauChain_of_oiter Q m b (hb _)
  refine ⟨?_, htgt a ha⟩
  obtain ⟨u, v, α⟩ := a
  have h1 := ha 1
  rw [oiter_one] at h1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨hv, rfl⟩ := mateMap_eq_some Q hb
  refine htgt ⟨_, u, Q.mate ⟨v, hv⟩ u α⟩ fun m ↦ ?_
  have := ha (m + 1)
  rwa [oiter_add, oiter_one, hb, Option.bind_some] at this

/-- **The cycles of the mate map lie in the periodic part.** -/
theorem perArr_of_cycle {a : Arr V} {n : ℕ} (hn : 1 ≤ n) (ha : oiter (mateMap Q) n a = some a) :
    PerArr Q a := by
  have hj : ∀ j, oiter (mateMap Q) (j * n) a = some a := by
    intro j
    induction j with
    | zero => simp [oiter]
    | succ j ih => rw [Nat.succ_mul, add_comm, oiter_add, ih, Option.bind_some, ha]
  refine perArr_of_oiter Q fun m hm ↦ ?_
  have := hj m
  rw [(Nat.sub_add_cancel (Nat.le_mul_of_pos_right m hn)).symm, oiter_add, hm] at this
  simp at this

end Mate

/-! ### Scales on periodic components -/

section Scales

variable {V : Type} [Quiver.{0} V] [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]
  (Q : TranslationQuiver V) {M : Type*} [CommGroup M] {I : Type*} (v₀ : I → V)

open Classical in
/-- The component scale: `s_i` on the `i`th component, one elsewhere. -/
def compScale (s : I → M) (v : V) : M :=
  if h : ∃ i, v ∈ Q.component (v₀ i) then s h.choose else 1

variable {Q v₀}
variable (hper : ∀ i, v₀ i ∈ Q.periodic) (hdisj : ∀ i j, v₀ j ∈ Q.component (v₀ i) → i = j)

include hper hdisj in
theorem compScale_of_mem (s : I → M) {v : V} {i : I} (hv : v ∈ Q.component (v₀ i)) :
    compScale Q v₀ s v = s i := by
  have h : ∃ i, v ∈ Q.component (v₀ i) := ⟨i, hv⟩
  rw [compScale, dif_pos h]
  have hj := h.choose_spec
  have hmem : v₀ h.choose ∈ Q.component (v₀ i) :=
    ⟨hper _, Relation.EqvGen.trans _ _ _ hv.2 (Relation.EqvGen.symm _ _ hj.2)⟩
  rw [hdisj _ _ hmem]

theorem mem_component_iff_of_arrow {u v : V} (α : u ⟶ v) (hu : u ∈ Q.periodic)
    (hv : v ∈ Q.periodic) (x : V) : u ∈ Q.component x ↔ v ∈ Q.component x := by
  have hadj : Q.PeriodicAdj u v := ⟨hu, hv, Or.inl ⟨α⟩⟩
  constructor
  · rintro ⟨-, h⟩; exact ⟨hv, Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hadj)⟩
  · rintro ⟨-, h⟩
    exact ⟨hu, Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hadj))⟩

include hper hdisj in
theorem compScale_eq_of_arrow (s : I → M) {u v : V} (α : u ⟶ v) (hu : u ∈ Q.periodic)
    (hv : v ∈ Q.periodic) : compScale Q v₀ s u = compScale Q v₀ s v := by
  by_cases h : ∃ i, v ∈ Q.component (v₀ i)
  · obtain ⟨i, hi⟩ := h
    rw [compScale_of_mem hper hdisj s hi,
      compScale_of_mem hper hdisj s ((mem_component_iff_of_arrow α hu hv _).2 hi)]
  · have h' : ¬ ∃ i, u ∈ Q.component (v₀ i) := fun ⟨i, hi⟩ ↦
      h ⟨i, (mem_component_iff_of_arrow α hu hv _).1 hi⟩
    rw [compScale, compScale, dif_neg h, dif_neg h']

include hper hdisj in
/-- **The global mesh scales** (`eq:global-mesh-scales`, with all `c_{v,a} = 1`): arrow scales
`μ` with `μ_{σa} μ_a = η_v`, where `η_v = s_i²` on the `i`th component and `η_v = 1` on the
other periodic vertices, and `μ_a = s_i` on the internal arrows of the `i`th component. -/
theorem exists_scales (s : I → M) :
    ∃ μ : Arr V → M, (∀ (x : Q.nonprojective) (y : V) (α : y ⟶ x.1),
        μ ⟨_, y, Q.mate x y α⟩ * μ ⟨y, x.1, α⟩ = compScale Q v₀ s x.1 ^ 2) ∧
      ∀ i {u v : V} (α : u ⟶ v), u ∈ Q.component (v₀ i) → v ∈ Q.component (v₀ i) →
        μ ⟨u, v, α⟩ = s i := by
  classical
  obtain ⟨μ, hμP, hμ⟩ := exists_chain_solution (mateMap Q) (mateMap_inj Q) (PerArr Q)
    (fun _ _ h ↦ perArr_iff Q h) (fun _ ha _ hn hc ↦ ha (perArr_of_cycle Q hn hc))
    (fun a ↦ compScale Q v₀ s a.2.1 ^ 2) (fun a ↦ compScale Q v₀ s a.2.1) (by
      intro a b hab ha
      obtain ⟨u, v, α⟩ := a
      obtain ⟨h, rfl⟩ := mateMap_eq_some Q hab
      change compScale Q v₀ s u * compScale Q v₀ s v = compScale Q v₀ s v ^ 2
      rw [compScale_eq_of_arrow hper hdisj s α ha.1 ha.2, sq])
  refine ⟨μ, fun x y α ↦ hμ ⟨y, x.1, α⟩ _ (mateMap_of_mem Q α x.2), fun i u v α hu hv ↦ ?_⟩
  rw [hμP _ ⟨hu.1, hv.1⟩]
  exact compScale_of_mem hper hdisj s hv

end Scales

/-! ### Weights of internal paths -/

section Paths

variable {V : Type} [Quiver.{0} V]

/-- A path all of whose arrows have both endpoints in `C`. -/
def PathIn (C : Set V) {x : V} : ∀ {y : V}, Quiver.Path x y → Prop
  | _, Quiver.Path.nil => True
  | _, @Quiver.Path.cons _ _ _ y _ p _ => PathIn C p ∧ y ∈ C

/-- The last vertex of a nonempty path in `C` lies in `C`. -/
theorem pathWt_of_pathIn {k : Type*} [CommRing k] (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (C : Set V)
    (t : kˣ) (hμ : ∀ {u v : V} (α : u ⟶ v), u ∈ C → v ∈ C → μ α = t) {x : V} (hx : x ∈ C) :
    ∀ {y : V} (p : Quiver.Path x y), PathIn C p → y ∈ C → pathWt μ p = t ^ p.length
  | _, Quiver.Path.nil, _, _ => by simp [pathWt]
  | _, @Quiver.Path.cons _ _ _ y _ p a, h, hz => by
    have h' : PathIn C p ∧ y ∈ C := h
    rw [pathWt, pathWt_of_pathIn μ C t hμ hx p h'.1 h'.2, hμ a h'.2 hz, Quiver.Path.length_cons,
      pow_succ]

theorem pathWt_inv {k : Type*} [CommRing k] (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) {x : V} :
    ∀ {y : V} (p : Quiver.Path x y), pathWt (fun α ↦ (μ α)⁻¹) p = (pathWt μ p)⁻¹
  | _, Quiver.Path.nil => by simp [pathWt]
  | _, Quiver.Path.cons p a => by rw [pathWt, pathWt, pathWt_inv μ p, mul_inv]

theorem gaugeMap_inv {k : Type*} [CommRing k] (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (x y : V)
    (g : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :
    gaugeMap (fun α ↦ (μ α)⁻¹) x y (gaugeMap μ x y g) = g := by
  induction g using LinearPaths.induction_on with
  | h0 => simp
  | hadd a b ha hb => rw [map_add, map_add, ha, hb]
  | hsingle p c =>
    rw [map_smul, map_smul, gaugeMap_path, map_smul, gaugeMap_path, pathWt_inv, smul_smul,
      smul_smul, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end Paths

/-! ### Diagonal maps of the perturbed presentations -/

section Gauge

open FlatPert

variable {k : Type*} [CommRing k] {V : Type} [Quiver.{0} V] [DecidableEq V]
  [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {Q : TranslationQuiver V}
  (c : MeshCoefficients k Q) {I : Type*} [Fintype I]
  (tup : I → ∀ x : Q.nonprojective, Hm k (Q.tau x).1 x.1) (htup : ∀ i x, tup i x ∈ geSpan k 3 _ _)

/-- The perturbation `Σ_i λ_i (p_i)_v` of the mesh relations by tuples. -/
def tpert (lam : I → k) : ∀ x (t : (meshPres c).T x), Hm k ((meshPres c).src x t) x :=
  fun x t ↦ ∑ i, lam i • tup i ⟨x, t.2⟩

include htup in
theorem tpert_mem (lam : I → k) :
    ∀ x t, tpert c tup lam x t ∈ geSpan k ((meshPres c).deg x t + 1) ((meshPres c).src x t) x :=
  fun x t ↦ Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (htup i ⟨x, t.2⟩)

/-- The ideal `(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)` of `C(λ)`. -/
abbrev idealT (lam : I → k) (N : ℕ) : IdealFam k V :=
  idealB (meshPres c) (tpert c tup lam) (tpert_mem c tup htup lam) N

/-- **A diagonal map** with `μ_{σa} μ_a = η_v` and `p_i ↦ η_v κ_i p_i` maps the ideal of `C(λ)`
into that of `C(λκ)`. -/
theorem gauge_le (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (E : V → kˣ) (κ : I → kˣ)
    (hscale : ∀ (x : Q.nonprojective) (y : V) (α : y ⟶ x.1), μ (Q.mate x y α) * μ α = E x.1)
    (hg : ∀ i x, gaugeMap μ _ _ (tup i x) = ((E x.1 * κ i : kˣ) : k) • tup i x)
    (lam : I → k) (N : ℕ) (w y : V) :
    (idealT c tup htup lam N).I w y ≤
      ((idealT c tup htup (fun i ↦ lam i * κ i) N).I w y).comap (gaugeMap μ w y) := by
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, t, u, v, rfl⟩
    have hr : gaugeMap μ _ _ ((meshPres c).r x t) = ((E x : kˣ) : k) • (meshPres c).r x t := by
      have := gaugeMap_meshRelation μ (fun z ↦ (E z.1)⁻¹) c c (fun z y α ↦ by
        rw [mul_assoc _ (μ _), hscale, mul_comm (E z.1)⁻¹, inv_mul_cancel_right]) ⟨x, t.2⟩
      rw [inv_inv, Units.smul_def] at this
      exact this
    have hrf : gaugeMap μ _ _ (rf (meshPres c) (tpert c tup lam) x t) =
        ((E x : kˣ) : k) • rf (meshPres c) (tpert c tup (fun i ↦ lam i * κ i)) x t := by
      simp only [rf, tpert]
      rw [map_sub, map_sum, hr, smul_sub, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, hg, smul_smul, smul_smul, Units.val_mul]
      congr 1
      ring
    rw [SetLike.mem_coe, Submodule.mem_comap, gaugeMap_comp, gaugeMap_comp, gaugeMap_path,
      gaugeMap_path, hrf]
    simp only [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, t, u, v, rfl⟩))))
  · rintro _ ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, gaugeMap_path]
    exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, hq, rfl⟩))

end Gauge

/-! ### Lemma 12.6 -/

section Rows

open FlatPert

variable {k : Type*} [CommRing k] {V : Type} [Quiver.{0} V] [DecidableEq V]
  [∀ x y : V, DecidableEq (x ⟶ y)] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {Q : TranslationQuiver V}
  {I : Type*} (v₀ : I → Q.nonprojective) (p : ∀ i, Quiver.Path (Q.tau (v₀ i)).1 (v₀ i).1)

open Classical in
/-- The tuple of a row: the path `p_i` at the row `v_i`, zero at all other rows. -/
def rowTup (i : I) (x : Q.nonprojective) : Hm k (Q.tau x).1 x.1 :=
  if h : v₀ i = x then (by subst h; exact LinearPaths.path (p i)) else 0

theorem rowTup_mem (hlen : ∀ i, 3 ≤ (p i).length) (i : I) (x : Q.nonprojective) :
    rowTup (k := k) v₀ p i x ∈ geSpan k 3 _ _ := by
  by_cases h : v₀ i = x
  · subst h
    simp only [rowTup, dif_pos rfl]
    exact Submodule.subset_span ⟨p i, hlen i, rfl⟩
  · simp only [rowTup, dif_neg h]; exact zero_mem _

theorem tau_mem_component {v : Q.nonprojective} (hv : v.1 ∈ Q.periodic) :
    (Q.tau v).1 ∈ Q.component v.1 := by
  have hτ : (Q.tau v).1 ∈ Q.periodic := (mem_periodic_tau_iff Q v.2).2 hv
  exact ⟨hτ, Relation.EqvGen.rel _ _ ⟨hv, hτ, Or.inr ⟨v.2, rfl⟩⟩⟩

theorem gauge_rowTup (hper : ∀ i, (v₀ i).1 ∈ Q.periodic)
    (hint : ∀ i, PathIn (Q.component (v₀ i).1) (p i)) (hlen : ∀ i, 3 ≤ (p i).length)
    (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (E : V → kˣ) (κ : I → kˣ) (t : I → kˣ)
    (hμ : ∀ i {u v : V} (α : u ⟶ v), u ∈ Q.component (v₀ i).1 → v ∈ Q.component (v₀ i).1 →
      μ α = t i)
    (hE : ∀ i, E (v₀ i).1 = t i ^ 2) (hκ : ∀ i, κ i = t i ^ ((p i).length - 2))
    (i : I) (x : Q.nonprojective) :
    gaugeMap μ _ _ (rowTup (k := k) v₀ p i x) = ((E x.1 * κ i : kˣ) : k) • rowTup v₀ p i x := by
  by_cases h : v₀ i = x
  · subst h
    have e : rowTup (k := k) v₀ p i (v₀ i) = LinearPaths.path (p i) := by simp [rowTup]
    rw [e, gaugeMap_path, pathWt_of_pathIn μ _ (t i) (hμ i) (tau_mem_component (hper i)) (p i)
      (hint i) (TranslationQuiver.mem_component_self (hper i)), hE, hκ, ← pow_add,
      show 2 + ((p i).length - 2) = (p i).length by have := hlen i; omega]
  · simp only [rowTup, dif_neg h, map_zero, smul_zero]

variable [Fintype I]

/-- **Lemma 12.6** (`lem:same-support-forms`): let `C(λ) = kQ/(𝔪^{N+1}, r_v − Σ_i λ_i (p_i)_v)`
with rows `p_i : τ v_i → v_i` of length at least three, internal to pairwise distinct periodic
components. If `λ_i = 0` exactly when `λ'_i = 0`, a diagonal automorphism `a ↦ μ_a a` of `kQ`
(object-preserving, with inverse `a ↦ μ_a⁻¹ a`) maps the ideal of `C(λ)` onto that of `C(λ')`,
so `C(λ) ≅ C(λ')`. -/
theorem sameSupport {k : Type*} [Field k] [IsAlgClosed k] [Fintype V] [∀ x y : V, Fintype (x ⟶ y)]
    (c : MeshCoefficients k Q) (hper : ∀ i, (v₀ i).1 ∈ Q.periodic)
    (hdisj : ∀ i j, (v₀ j).1 ∈ Q.component (v₀ i).1 → i = j)
    (hint : ∀ i, PathIn (Q.component (v₀ i).1) (p i)) (hlen : ∀ i, 3 ≤ (p i).length)
    (N : ℕ) (lam lam' : I → k) (hsupp : ∀ i, lam i = 0 ↔ lam' i = 0) :
    ∃ μ : ∀ {x y : V}, (x ⟶ y) → kˣ,
      (∀ x y (g : Hm k x y), gaugeMap (fun α ↦ (μ α)⁻¹) x y (gaugeMap μ x y g) = g) ∧
      (∀ x y (g : Hm k x y), gaugeMap μ x y (gaugeMap (fun α ↦ (μ α)⁻¹) x y g) = g) ∧
      ∀ x y, Submodule.map (gaugeMap μ x y)
          ((idealT c (rowTup v₀ p) (rowTup_mem v₀ p hlen) lam N).I x y) =
        (idealT c (rowTup v₀ p) (rowTup_mem v₀ p hlen) lam' N).I x y := by
  classical
  -- the component scales `a_i`, with `λ_i a_i^{d_i - 2} = λ'_i`
  have hroot : ∀ i, ∃ a : kˣ, lam i * ((a ^ ((p i).length - 2) : kˣ) : k) = lam' i := by
    intro i
    by_cases h0 : lam i = 0
    · exact ⟨1, by rw [h0, zero_mul, (hsupp i).1 h0]⟩
    · have h0' : lam' i ≠ 0 := fun h ↦ h0 ((hsupp i).2 h)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (lam' i / lam i)
        (by have := hlen i; omega : 0 < (p i).length - 2)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow (by have := hlen i; omega)] at hz
        exact div_ne_zero h0' h0 hz.symm
      refine ⟨Units.mk0 z hz0, ?_⟩
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]
      field_simp
  choose a ha using hroot
  -- the global mesh scales
  obtain ⟨μA, hscale, hμA⟩ := exists_scales (Q := Q) (v₀ := fun i ↦ (v₀ i).1) hper hdisj a
  let μ : ∀ {x y : V}, (x ⟶ y) → kˣ := fun {x y} α ↦ μA ⟨x, y, α⟩
  let E : V → kˣ := fun v ↦ compScale Q (fun i ↦ (v₀ i).1) a v ^ 2
  let κ : I → kˣ := fun i ↦ a i ^ ((p i).length - 2)
  have hE : ∀ i, E (v₀ i).1 = a i ^ 2 := fun i ↦ by
    simp only [E]
    rw [compScale_of_mem (v₀ := fun i ↦ (v₀ i).1) hper hdisj a
      (TranslationQuiver.mem_component_self (hper i))]
  have hle := gauge_le c (rowTup v₀ p) (rowTup_mem v₀ p hlen) μ E κ (fun x y α ↦ hscale x y α)
    (gauge_rowTup v₀ p hper hint hlen μ E κ a (fun i _ _ α hu hv ↦ hμA i α hu hv) hE
      (fun _ ↦ rfl)) lam N
  have hle' := gauge_le c (rowTup v₀ p) (rowTup_mem v₀ p hlen) (fun α ↦ (μ α)⁻¹)
    (fun v ↦ (E v)⁻¹) (fun i ↦ (κ i)⁻¹)
    (fun x y α ↦ by rw [← mul_inv, hscale])
    (gauge_rowTup v₀ p hper hint hlen (fun α ↦ (μ α)⁻¹) (fun v ↦ (E v)⁻¹) (fun i ↦ (κ i)⁻¹)
      (fun i ↦ (a i)⁻¹)
      (fun i _ _ α hu hv ↦ by simp only [μ]; rw [hμA i α hu hv])
      (fun i ↦ by rw [hE, inv_pow]) (fun i ↦ by simp only [κ]; rw [inv_pow])) lam' N
  have hlk : (fun i ↦ lam i * ((κ i : kˣ) : k)) = lam' := funext ha
  have hlk' : (fun i ↦ lam' i * (((κ i)⁻¹ : kˣ) : k)) = lam := by
    funext i
    rw [← ha i]
    simp only [κ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [hlk] at hle
  rw [hlk'] at hle'
  have hinv : ∀ x y (g : Hm k x y), gaugeMap μ x y (gaugeMap (fun α ↦ (μ α)⁻¹) x y g) = g := by
    intro x y g
    have := gaugeMap_inv (fun α ↦ (μ α)⁻¹) x y g
    simp only [inv_inv] at this
    exact this
  refine ⟨μ, fun x y g ↦ gaugeMap_inv μ x y g, hinv, fun x y ↦ le_antisymm ?_ ?_⟩
  · exact Submodule.map_le_iff_le_comap.2 (hle x y)
  · intro g hg
    exact ⟨_, hle' x y hg, hinv x y g⟩

end Rows

end SameSupport

end MultiplicativeBasisDeformations
