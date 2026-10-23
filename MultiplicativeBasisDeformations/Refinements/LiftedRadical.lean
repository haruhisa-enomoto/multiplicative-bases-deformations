module

public import MultiplicativeBasisDeformations.Refinements.SplitDeformation

/-!
# Proposition 6.5(3): the radical filtration of the lifted category

`positive-deformations.tex`: "Let `E` be the full category on the lifted modules. The
map-degree filtration has nilpotent positive part, and its degree-zero part is a product of
copies of `k`, one for each lifted module. Its first term is therefore the categorical radical.
Since the original graded Hom category is generated in degree one, descending induction
through the finite filtration identifies its `q`th term with the `q`th radical power."

Formalization. For a family of filtered lifts `A i` of graded modules `M i`, a morphism of `E`
is a `B`-linear map (`IsBLin`), the categorical radical is `IsRad` (`1 − hg` invertible for all
`h`), and its powers are `radPow` (spans of composites). Under the hypotheses of (3) the radical
is the filtration order `≥ 1` (`isRad_iff`), and the `q`th radical power is the filtration order
`≥ q` (`mem_radPow_iff`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N X : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup X] [Module R X] {MM : GMod GΛ M} {NN : GMod GΛ N} {XX : GMod GΛ X}

theorem OrderGe.comp {r s : ℤ} {g : M →ₗ[R] N} {h : N →ₗ[R] X} (hg : OrderGe MM NN r g)
    (hh : OrderGe NN XX s h) : OrderGe MM XX (r + s) (h ∘ₗ g) := by
  intro p m hm e he
  rw [LinearMap.comp_apply, NN.gr.sum (g m), map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  by_cases hd : d < p + r
  · rw [hg p m hm d hd, map_zero, map_zero]
  · exact hh d _ (NN.gr.isHom_proj d (g m)) e (by omega)

theorem OrderGe.add {r : ℤ} {g g' : M →ₗ[R] N} (hg : OrderGe MM NN r g)
    (hg' : OrderGe MM NN r g') : OrderGe MM NN r (g + g') := by
  intro p m hm d hd
  rw [LinearMap.add_apply, map_add, hg p m hm d hd, hg' p m hm d hd, add_zero]

theorem OrderGe.smul {r : ℤ} (c : R) {g : M →ₗ[R] N} (hg : OrderGe MM NN r g) :
    OrderGe MM NN r (c • g) := by
  intro p m hm d hd
  rw [LinearMap.smul_apply, map_smul, hg p m hm d hd, smul_zero]

theorem OrderGe.zero (r : ℤ) : OrderGe MM NN r (0 : M →ₗ[R] N) := by
  intro p m hm d hd
  rw [LinearMap.zero_apply, map_zero]

theorem OrderGe.mono {r r' : ℤ} {g : M →ₗ[R] N} (hg : OrderGe MM NN r g) (h : r' ≤ r) :
    OrderGe MM NN r' g := fun p m hm d hd ↦ hg p m hm d (by omega)

/-- **The leading term of a composite is the composite of the leading terms.** -/
theorem comp_comp_lead {r s : ℤ} {g : M →ₗ[R] N} {h : N →ₗ[R] X} (hg : OrderGe MM NN r g)
    (hh : OrderGe NN XX s h) :
    ZGr.comp MM.gr XX.gr (r + s) (h ∘ₗ g) =
      ZGr.comp NN.gr XX.gr s h ∘ₗ ZGr.comp MM.gr NN.gr r g := by
  classical
  refine MM.gr.ext_of_hom fun p m hm ↦ ?_
  rw [ZGr.comp_hom MM.gr XX.gr _ hm, LinearMap.comp_apply, LinearMap.comp_apply,
    ZGr.comp_hom MM.gr NN.gr _ hm, ZGr.comp_hom NN.gr XX.gr _ (NN.gr.isHom_proj _ _)]
  conv_lhs => rw [NN.gr.sum (g m), map_sum, map_sum]
  by_cases hmem : p + r ∈ NN.gr.supp
  · rw [Finset.sum_eq_single (p + r)]
    · rw [show p + (r + s) = p + r + s by ring]
    · intro d _ hd
      by_cases hlt : d < p + r
      · rw [hg p m hm d hlt, map_zero, map_zero]
      · exact hh d _ (NN.gr.isHom_proj d (g m)) _ (by omega)
    · intro h; exact absurd hmem h
  · rw [NN.gr.proj_out (p + r) hmem, LinearMap.zero_apply, map_zero, map_zero]
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    by_cases hlt : d < p + r
    · rw [hg p m hm d hlt, map_zero, map_zero]
    · have hne : d ≠ p + r := fun h ↦ hmem (h ▸ hd)
      exact hh d _ (NN.gr.isHom_proj d (g m)) _ (by omega)

theorem OrderGe.raisesBy {r : ℤ} {g : M →ₗ[R] M} (hg : OrderGe MM MM r g) : RaisesBy MM r g := hg

end GExt

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

namespace PosFiltration

universe u v w

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] {P : PosFiltration G B} {h1 : G.IsHom 0 (1 : Λ)}
  {ι : Type} [DecidableEq ι] {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module k (Ms i)]
  {MM : ∀ i, GExt.GMod (GExt.GAlg.ofLen G h1) (Ms i)} (A : ∀ i, FLift P h1 (MM i))

/-- A morphism of the lifted category: a `B`-linear map. -/
def IsBLin (i j : ι) (g : Ms i →ₗ[k] Ms j) : Prop := ∀ m x, g ((A i).act m x) = (A j).act (g m) x

theorem isBLin_comp {i j l : ι} {g : Ms i →ₗ[k] Ms l} {h : Ms l →ₗ[k] Ms j} (hg : IsBLin A i l g)
    (hh : IsBLin A l j h) : IsBLin A i j (h ∘ₗ g) := fun m x ↦ by
  rw [LinearMap.comp_apply, hg, hh]; rfl

theorem isBLin_id (i : ι) : IsBLin A i i LinearMap.id := fun _ _ ↦ rfl

/-- **The categorical radical** of the lifted category: `1 − hg` is invertible for all `h`. -/
def IsRad (i j : ι) (g : Ms i →ₗ[k] Ms j) : Prop :=
  IsBLin A i j g ∧ ∀ h : Ms j →ₗ[k] Ms i, IsBLin A j i h →
    Function.Bijective ((LinearMap.id : Ms i →ₗ[k] Ms i) - h ∘ₗ g)

/-- The `B`-linear maps, as a subspace. -/
def bLin (i j : ι) : Submodule k (Ms i →ₗ[k] Ms j) where
  carrier := {g | IsBLin A i j g}
  add_mem' {g g'} hg hg' m x := by simp only [LinearMap.add_apply, map_add, hg m x, hg' m x]
  zero_mem' m x := by simp
  smul_mem' c g hg m x := by simp only [LinearMap.smul_apply, map_smul, hg m x]

/-- **The powers of the radical**: `rad⁰ = Hom`, `rad^{q+1} = rad · rad^q`. -/
def radPow : ℕ → ∀ i j : ι, Submodule k (Ms i →ₗ[k] Ms j)
  | 0, i, j => bLin A i j
  | q + 1, i, j => Submodule.span k {f | ∃ (l : ι) (g : Ms i →ₗ[k] Ms l) (h : Ms l →ₗ[k] Ms j),
      g ∈ radPow q i l ∧ IsRad A l j h ∧ f = h ∘ₗ g}

/-- A homogeneous `Λ`-linear map of degree `r`. -/
def IsGrHom (i j : ι) (r : ℤ) (f : Ms i →ₗ[k] Ms j) : Prop :=
  (∀ m a, f ((MM i).act m a) = (MM j).act (f m) a) ∧
    ∀ p m, (MM i).gr.IsHom p m → (MM j).gr.IsHom (p + r) (f m)

/-- The homogeneous `Λ`-linear maps of degree `r`, as a subspace. -/
def grHom (i j : ι) (r : ℤ) : Submodule k (Ms i →ₗ[k] Ms j) where
  carrier := {f | IsGrHom (MM := MM) i j r f}
  add_mem' {f f'} hf hf' := ⟨fun m a ↦ by simp [hf.1, hf'.1],
    fun p m hm ↦ (MM j).gr.isHom_add (hf.2 p m hm) (hf'.2 p m hm)⟩
  zero_mem' := ⟨fun m a ↦ by simp, fun p m hm ↦ (MM j).gr.isHom_zero _⟩
  smul_mem' c f hf := ⟨fun m a ↦ by simp [hf.1], fun p m hm ↦ (MM j).gr.isHom_smul c (hf.2 p m hm)⟩

/-- **The graded Hom category generated in degree one**: `grPow n` is spanned by composites of
`n + 1` homogeneous maps of degree one. -/
def grPow : ℕ → ∀ i j : ι, Submodule k (Ms i →ₗ[k] Ms j)
  | 0, i, j => grHom (MM := MM) i j 1
  | n + 1, i, j => Submodule.span k {f | ∃ (l : ι) (g : Ms i →ₗ[k] Ms l) (h : Ms l →ₗ[k] Ms j),
      g ∈ grPow n i l ∧ h ∈ grHom (MM := MM) l j 1 ∧ f = h ∘ₗ g}

variable (MM) in
/-- **The hypotheses of Proposition 6.5(3)**, with the `Ext¹` vanishing of (2). -/
structure LiftHyp : Prop where
  neg : ∀ i j (r : ℤ), r < 0 → ∀ f, IsGrHom (MM := MM) i j r f → f = 0
  off : ∀ i j, i ≠ j → ∀ f, IsGrHom (MM := MM) i j 0 f → f = 0
  diag : ∀ i f, IsGrHom (MM := MM) i i 0 f → ∃ c : k, f = c • LinearMap.id
  ext : ∀ i j (r t : ℕ), 0 < t → GExt.ExtVanish (MM i) (MM j) 0 (r + t)
  nontriv : ∀ i, Nontrivial (Ms i)

section Comp

variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {gM : GExt.ZGr (R := k) M} {gN : GExt.ZGr (R := k) N}

theorem comp_sub (r : ℤ) (u v : M →ₗ[k] N) :
    GExt.ZGr.comp gM gN r (u - v) = GExt.ZGr.comp gM gN r u - GExt.ZGr.comp gM gN r v := by
  simp only [GExt.ZGr.comp, LinearMap.comp_sub, LinearMap.sub_comp, Finset.sum_sub_distrib]

theorem comp_smul (r : ℤ) (c : k) (u : M →ₗ[k] N) :
    GExt.ZGr.comp gM gN r (c • u) = c • GExt.ZGr.comp gM gN r u := by
  simp only [GExt.ZGr.comp, LinearMap.comp_smul, LinearMap.smul_comp, Finset.smul_sum]

theorem comp_zero_id : GExt.ZGr.comp gM gM 0 (LinearMap.id : M →ₗ[k] M) = LinearMap.id := by
  refine gM.ext_of_hom fun p m hm ↦ ?_
  rw [GExt.ZGr.comp_hom gM gM _ hm, add_zero, LinearMap.id_apply, hm]

end Comp

variable (hS : Nonempty (Split P))

include hS in
theorem orderGe_zero_of_bLin (H : LiftHyp MM) {i j : ι} {g : Ms i →ₗ[k] Ms j}
    (hg : IsBLin A i j g) : GExt.OrderGe (MM i) (MM j) 0 g :=
  fLift_orderGe_zero_of_split hS (A i) (A j) (fun r hr f h1 h2 ↦ H.neg i j r hr f ⟨h1, h2⟩) g hg

include hS in
theorem leading_isGrHom (H : LiftHyp MM) {i j : ι} {g : Ms i →ₗ[k] Ms j} {r : ℤ}
    (hg : IsBLin A i j g) (hord : GExt.OrderGe (MM i) (MM j) r g) :
    IsGrHom (MM := MM) i j r (GExt.ZGr.comp (MM i).gr (MM j).gr r g) :=
  ⟨fun m a ↦ fLift_leading_of_split hS (A i) (A j) g hg hord m a,
    fun p m hm ↦ GExt.ZGr.comp_isHom (MM i).gr (MM j).gr g hm⟩

include hS in
/-- **The radical of the lifted category is the filtration order `≥ 1`.** -/
theorem isRad_iff (H : LiftHyp MM) (i j : ι) (g : Ms i →ₗ[k] Ms j) :
    IsRad A i j g ↔ IsBLin A i j g ∧ GExt.OrderGe (MM i) (MM j) 1 g := by
  constructor
  · rintro ⟨hg, hrad⟩
    have hord0 := orderGe_zero_of_bLin A hS H hg
    have hgr := leading_isGrHom A hS H hg hord0
    refine ⟨hg, ?_⟩
    have key : GExt.ZGr.comp (MM i).gr (MM j).gr 0 g = 0 → GExt.OrderGe (MM i) (MM j) 1 g :=
      fun h0 ↦ by simpa using orderGe_succ hord0 h0
    by_cases hij : i = j
    · subst hij
      obtain ⟨c, hc⟩ := H.diag i _ hgr
      by_cases hc0 : c = 0
      · exact key (by rw [hc, hc0, zero_smul])
      · exfalso
        set h : Ms i →ₗ[k] Ms i := c⁻¹ • LinearMap.id
        have hh : IsBLin A i i h := fun m x ↦ by
          simp only [h, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_smul₂]
        have hbij := hrad h hh
        set Nm : Ms i →ₗ[k] Ms i := LinearMap.id - h ∘ₗ g
        have hNb : IsBLin A i i Nm := fun m x ↦ by
          simp only [Nm, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hg m x]
          rw [hh, map_sub, LinearMap.sub_apply]
        have hN0 := orderGe_zero_of_bLin A hS H hNb
        have hlead : GExt.ZGr.comp (MM i).gr (MM i).gr 0 Nm = 0 := by
          simp only [Nm, h, comp_sub, LinearMap.smul_comp, LinearMap.id_comp, comp_smul, hc,
            comp_zero_id, smul_smul, inv_mul_cancel₀ hc0, one_smul, sub_self]
        have hN1 : GExt.RaisesBy (MM i) 1 Nm :=
          GExt.OrderGe.raisesBy (by simpa using orderGe_succ hN0 hlead)
        obtain ⟨n, hn⟩ := hN1.isNilpotent
        have := H.nontriv i
        have hpow : Function.Bijective (Nm ^ n) := by
          rw [← Module.End.isUnit_iff] at hbij ⊢
          exact hbij.pow n
        rw [hn] at hpow
        obtain ⟨x, hx⟩ := exists_ne (0 : Ms i)
        exact hx (hpow.1 (by simp))
    · exact key (H.off i j hij _ hgr)
  · rintro ⟨hg, hord⟩
    refine ⟨hg, fun h hh ↦ ?_⟩
    have h0 := orderGe_zero_of_bLin A hS H hh
    have hc : GExt.RaisesBy (MM i) 1 (h ∘ₗ g) :=
      GExt.OrderGe.raisesBy (by simpa using hord.comp h0)
    have hnil : IsNilpotent (-(h ∘ₗ g) : Module.End k (Ms i)) := hc.isNilpotent.neg
    rw [← Module.End.isUnit_iff]
    have := hnil.isUnit_one_add
    rwa [← sub_eq_add_neg] at this

theorem radPow_le_bLin : ∀ q i j, radPow A q i j ≤ bLin A i j
  | 0, _, _ => le_rfl
  | q + 1, i, j => by
    rw [radPow, Submodule.span_le]
    rintro _ ⟨l, g, h, hg, hh, rfl⟩
    exact isBLin_comp A (radPow_le_bLin q i l hg) hh.1

theorem radPow_succ_le : ∀ q i j, radPow A (q + 1) i j ≤ radPow A q i j
  | 0, i, j => radPow_le_bLin A 1 i j
  | q + 1, i, j => by
    rw [radPow, radPow]
    refine Submodule.span_mono ?_
    rintro _ ⟨l, g, h, hg, hh, rfl⟩
    exact ⟨l, g, h, radPow_succ_le q i l hg, hh, rfl⟩

theorem comp_add' {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {gM : GExt.ZGr (R := k) M} {gN : GExt.ZGr (R := k) N} (r : ℤ) (u v : M →ₗ[k] N) :
    GExt.ZGr.comp gM gN r (u + v) = GExt.ZGr.comp gM gN r u + GExt.ZGr.comp gM gN r v := by
  simp only [GExt.ZGr.comp, LinearMap.comp_add, LinearMap.add_comp, Finset.sum_add_distrib]

theorem comp_zero' {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {gM : GExt.ZGr (R := k) M} {gN : GExt.ZGr (R := k) N} (r : ℤ) :
    GExt.ZGr.comp gM gN r (0 : M →ₗ[k] N) = 0 := by
  simp only [GExt.ZGr.comp, LinearMap.comp_zero, LinearMap.zero_comp, Finset.sum_const_zero]

include hS in
theorem orderGe_of_mem_radPow (H : LiftHyp MM) :
    ∀ q i j g, g ∈ radPow A q i j → GExt.OrderGe (MM i) (MM j) q g
  | 0, i, j, g, hg => by simpa using orderGe_zero_of_bLin A hS H hg
  | q + 1, i, j, g, hg => by
    rw [radPow] at hg
    induction hg using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨l, g, h, hg, hh, rfl⟩ := hf
      have h1 := orderGe_of_mem_radPow H q i l g hg
      have h2 := ((isRad_iff A hS H l j h).1 hh).2
      have := h1.comp h2
      push_cast
      exact this
    | zero => exact GExt.OrderGe.zero _
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c

include hS in
/-- Homogeneous maps generated in degree one lift into the radical powers. -/
theorem lift_grPow (H : LiftHyp MM) :
    ∀ n i j f, f ∈ grPow (MM := MM) n i j → ∃ F : Ms i →ₗ[k] Ms j, F ∈ radPow A (n + 1) i j ∧
      IsBLin A i j F ∧ GExt.OrderGe (MM i) (MM j) (n + 1 : ℕ) F ∧
        GExt.ZGr.comp (MM i).gr (MM j).gr (n + 1 : ℕ) F = f
  | 0, i, j, f, hf => by
    obtain ⟨Φ, hΦ, hord, hlead⟩ := fLift_map_of_split hS (A i) (A j) 1 f hf.1 (by simpa using hf.2)
      (H.ext i j 1)
    have hrad : IsRad A i j Φ := (isRad_iff A hS H i j Φ).2 ⟨hΦ, by simpa using hord⟩
    refine ⟨Φ, Submodule.subset_span ⟨i, LinearMap.id, Φ, isBLin_id A i, hrad, rfl⟩, hΦ,
      by simpa using hord, by simpa using hlead⟩
  | n + 1, i, j, f, hf => by
    rw [grPow] at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨l, g, h, hg, hh, rfl⟩ := hf
      obtain ⟨G', hG, hGb, hGo, hGl⟩ := lift_grPow H n i l g hg
      obtain ⟨Hm, hHb, hHo, hHl⟩ := fLift_map_of_split hS (A l) (A j) 1 h hh.1 (by simpa using hh.2)
        (H.ext l j 1)
      have hHr : IsRad A l j Hm := (isRad_iff A hS H l j Hm).2 ⟨hHb, by simpa using hHo⟩
      refine ⟨Hm ∘ₗ G', Submodule.subset_span ⟨l, G', Hm, hG, hHr, rfl⟩,
        isBLin_comp A hGb hHb, ?_, ?_⟩
      · have := hGo.comp hHo
        push_cast at this ⊢
        exact this
      · have := GExt.comp_comp_lead hGo hHo
        push_cast at this hGl ⊢
        rw [this, hGl]
        simp only [Nat.cast_one] at hHl
        rw [hHl]
    | zero =>
      exact ⟨0, Submodule.zero_mem _, (bLin A i j).zero_mem, GExt.OrderGe.zero _, comp_zero' _⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, hF, hFb, hFo, hFl⟩ := hx
      obtain ⟨F', hF', hFb', hFo', hFl'⟩ := hy
      exact ⟨F + F', Submodule.add_mem _ hF hF', (bLin A i j).add_mem hFb hFb', hFo.add hFo',
        by rw [comp_add', hFl, hFl']⟩
    | smul c x _ hx =>
      obtain ⟨F, hF, hFb, hFo, hFl⟩ := hx
      exact ⟨c • F, Submodule.smul_mem _ c hF, (bLin A i j).smul_mem c hFb, hFo.smul c,
        by rw [comp_smul, hFl]⟩

theorem OrderGe.eq_zero' {i j : ι} {q : ℕ} {g : Ms i →ₗ[k] Ms j}
    (hg : GExt.OrderGe (MM i) (MM j) q g)
    (hq : GExt.degBound (MM i).gr + GExt.degBound (MM j).gr < q) : g = 0 := by
  refine (MM i).gr.ext_of_hom fun p m hm ↦ ?_
  by_cases hp : p ∈ (MM i).gr.supp
  · rw [(MM j).gr.sum (g m), LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun d hd ↦ hg p m hm d ?_
    have h1 := GExt.le_degBound hp
    have h2 := GExt.le_degBound hd
    rw [abs_le] at h1 h2
    omega
  · rw [(MM i).gr.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

include hS in
/-- **Proposition 6.5(3), the radical filtration**: if the graded Hom category is generated in
degree one, the `q`th power of the radical of the lifted category consists of the `B`-linear
maps of filtration order `≥ q`. -/
theorem mem_radPow_iff (H : LiftHyp MM)
    (hgen : ∀ n i j f, IsGrHom (MM := MM) i j (n + 1 : ℕ) f → f ∈ grPow (MM := MM) n i j)
    (q : ℕ) (i j : ι) (g : Ms i →ₗ[k] Ms j) :
    g ∈ radPow A q i j ↔ IsBLin A i j g ∧ GExt.OrderGe (MM i) (MM j) q g := by
  refine ⟨fun hg ↦ ⟨radPow_le_bLin A q i j hg, orderGe_of_mem_radPow A hS H q i j g hg⟩, ?_⟩
  rintro ⟨hgb, hgo⟩
  set Bd := GExt.degBound (MM i).gr + GExt.degBound (MM j).gr
  have key : ∀ t q, Bd < q + t → ∀ g : Ms i →ₗ[k] Ms j, IsBLin A i j g →
      GExt.OrderGe (MM i) (MM j) q g → g ∈ radPow A q i j := by
    intro t
    induction t with
    | zero =>
      intro q hq g _ hgo
      rw [OrderGe.eq_zero' hgo (by omega)]
      exact Submodule.zero_mem _
    | succ t ih =>
      intro q hq g hgb hgo
      rcases q with _ | n
      · exact hgb
      · have hgr := leading_isGrHom A hS H hgb hgo
        obtain ⟨F, hF, hFb, hFo, hFl⟩ := lift_grPow A hS H n i j _ (hgen n i j _ hgr)
        have hdb : IsBLin A i j (g - F) := (bLin A i j).sub_mem hgb hFb
        have hdo : GExt.OrderGe (MM i) (MM j) (n + 1 : ℕ) (g - F) := by
          have := hgo.add (hFo.smul (-1))
          simpa [sub_eq_add_neg] using this
        have hdl : GExt.ZGr.comp (MM i).gr (MM j).gr (n + 1 : ℕ) (g - F) = 0 := by
          rw [comp_sub, hFl, sub_self]
        have hdo' : GExt.OrderGe (MM i) (MM j) ((n + 1 + 1 : ℕ)) (g - F) := by
          have := orderGe_succ hdo hdl
          push_cast at this ⊢
          exact this
        have hmem := ih (n + 1 + 1) (by omega) _ hdb hdo'
        have := Submodule.add_mem _ (radPow_succ_le A (n + 1) i j hmem) hF
        rwa [sub_add_cancel] at this
  exact key (Bd + 1) q (by omega) g hgb hgo

end PosFiltration

end MultiplicativeBasisDeformations
