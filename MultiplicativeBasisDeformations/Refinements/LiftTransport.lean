import MultiplicativeBasisDeformations.Refinements.FilteredMaps

/-!
# Products and transports of filtered lifts (toward Corollary 12.1)

Filtered lifts in the sense of Proposition 6.5 (`FLift`) are stable under finite products with
shifted gradings (`FLift.pi`), and a `B`-stable subspace which is the image of an injective
filtered map with injective `Λ`-linear leading term carries a transported filtered lift
(`FLift.transport`): the leading-term arguments of `deformation-refinements.tex:50–62`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] {GΛ : GAlg (R := k) Λ}
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {MM : GMod GΛ M} {NN : GMod GΛ N}

/-- **Reflecting filtration levels** along a filtered map with injective leading term. -/
theorem geAt_of_lead {r : ℤ} {g : M →ₗ[k] N} (hg : OrderGe MM NN r g)
    (hinj : Function.Injective (ZGr.comp MM.gr NN.gr r g)) {t : ℤ} {m : M}
    (h : NN.gr.GeAt (t + r) (g m)) : MM.gr.GeAt t m := by
  have key : ∀ K : ℕ, MM.gr.GeAt (min t (-(degBound MM.gr : ℤ) + K)) m := by
    intro K
    induction K with
    | zero => exact (MM.gr.geAt_bot m).mono (by simp)
    | succ K ih =>
      set e : ℤ := -(degBound MM.gr : ℤ) + K
      by_cases het : t ≤ e
      · exact ih.mono (by push_cast; omega)
      · have ih' : MM.gr.GeAt e m := ih.mono (by omega)
        have h0 : MM.gr.proj e m = 0 := by
          apply hinj
          rw [map_zero, ZGr.comp_hom _ _ _ (MM.gr.isHom_proj e m)]
          have h1 := hg.geAt ih'.sub_proj (e + r) (by omega)
          have h2 := h (e + r) (by omega)
          have e1 : g (MM.gr.proj e m) = g m - g (m - MM.gr.proj e m) := by rw [map_sub]; abel
          rw [e1, map_sub, h2, h1, sub_zero]
        intro d hd
        rcases lt_or_eq_of_le (show d ≤ e by push_cast at hd; omega) with h' | rfl
        · exact ih' d h'
        · exact h0
  intro d hd
  exact key (Int.toNat (t + degBound MM.gr) + 1) d (by omega)

end GExt

namespace PosFiltration

open GExt

variable {k : Type*} [Field k] {Λ : Type*} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type*} [Ring B] [Algebra k B] {P : PosFiltration G B} {h1 : G.IsHom 0 (1 : Λ)}
  {M U : Type*} [AddCommGroup M] [Module k M] [AddCommGroup U] [Module k U]
  {MM : GMod (GAlg.ofLen G h1) M} {UU : GMod (GAlg.ofLen G h1) U}

/-- The action of `F^d B` raises filtration levels by `d`. -/
theorem FLift.geAt_act (A : FLift P h1 UU) {t : ℤ} {u : U} (hu : UU.gr.GeAt t u) {d : ℕ}
    {x : B} (hx : x ∈ P.F d) : UU.gr.GeAt (t + d) (A.act u x) := by
  intro e he
  rw [UU.gr.sum u, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  by_cases hp : p < t
  · rw [hu p hp, map_zero, LinearMap.zero_apply, map_zero]
  · exact A.filt d p _ x hx (UU.gr.isHom_proj p u) e (by omega)

/-- **The product of filtered lifts**, with shifted gradings. -/
def FLift.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ms : ι → Type*}
    [∀ a, AddCommGroup (Ms a)] [∀ a, Module k (Ms a)] {MMs : ∀ a, GMod (GAlg.ofLen G h1) (Ms a)}
    (A : ∀ a, FLift P h1 (MMs a)) (s : ι → ℤ) : FLift P h1 (GMod.pi MMs s) where
  act := LinearMap.mk₂ k (fun m x a ↦ (A a).act (m a) x)
    (fun m m' x ↦ by funext a; simp) (fun c m x ↦ by funext a; simp)
    (fun m x x' ↦ by funext a; simp) (fun c m x ↦ by funext a; simp)
  mul m x y := by funext a; exact (A a).mul _ _ _
  one m := by funext a; exact (A a).one _
  filt d p m x hx hm e he := by
    funext a
    have hm' := (ZGr.piShift_isHom _ _ _ _).1 hm a
    exact (A a).filt d (p - s a) (m a) x hx hm' (e - s a) (by omega)
  lead d p m x hx hm := by
    funext a
    have hm' := (ZGr.piShift_isHom _ _ _ _).1 hm a
    have := (A a).lead d (p - s a) (m a) x hx hm'
    change (MMs a).gr.proj (p + d - s a) ((A a).act (m a) x) = (MMs a).act (m a) (P.σ d x)
    rwa [show p + d - s a = p - s a + d by ring]

theorem σ_isHom (d : ℕ) (x : B) : (GAlg.ofLen G h1).gr.IsHom (d : ℤ) (P.σ d x) :=
  (ZGr.ofLen_isHom G d _).2 (P.σ_hom d x)

variable (A : FLift P h1 UU) (ι : M →ₗ[k] U) (hι : Function.Injective ι)
  (hstab : ∀ m x, A.act (ι m) x ∈ LinearMap.range ι)

/-- The transported action. -/
def transAct (m : M) (x : B) : M :=
  (LinearEquiv.ofInjective ι hι).symm ⟨A.act (ι m) x, hstab m x⟩

theorem ι_transAct (m : M) (x : B) : ι (transAct A ι hι hstab m x) = A.act (ι m) x := by
  have := (LinearEquiv.ofInjective ι hι).apply_symm_apply ⟨A.act (ι m) x, hstab m x⟩
  exact congrArg Subtype.val this

variable {r : ℤ} (hord : OrderGe MM UU r ι)
  (hlin : ∀ m a, ZGr.comp MM.gr UU.gr r ι (MM.act m a) = UU.act (ZGr.comp MM.gr UU.gr r ι m) a)
  (hinj : Function.Injective (ZGr.comp MM.gr UU.gr r ι))

include hord hlin hinj in
/-- **The transported filtered lift** on a `B`-stable image of an injective filtered map with
injective `Λ`-linear leading term. -/
def FLift.transport : FLift P h1 MM where
  act := LinearMap.mk₂ k (transAct A ι hι hstab)
    (fun m m' x ↦ hι (by simp only [map_add, ι_transAct, LinearMap.add_apply]))
    (fun c m x ↦ hι (by simp only [map_smul, ι_transAct, LinearMap.smul_apply]))
    (fun m x x' ↦ hι (by simp only [map_add, ι_transAct]))
    (fun c m x ↦ hι (by simp only [map_smul, ι_transAct]))
  mul m x y := hι (by simp only [LinearMap.mk₂_apply, ι_transAct, A.mul])
  one m := hι (by simp only [LinearMap.mk₂_apply, ι_transAct, A.one])
  filt d p m x hx hm e he := by
    simp only [LinearMap.mk₂_apply]
    set c := ZGr.comp MM.gr UU.gr r ι
    have hc : UU.gr.IsHom (p + r) (c m) := ZGr.comp_isHom _ _ _ hm
    have hι' : UU.gr.GeAt (p + r + d) (ι (transAct A ι hι hstab m x)) := by
      rw [ι_transAct, show ι m = c m + (ι m - c m) by abel, map_add, LinearMap.add_apply]
      refine (A.geAt_act (UU.gr.geAt_of_isHom hc le_rfl) hx).add ?_
      exact (A.geAt_act (hord.sub_comp_geAt hm) hx).mono (by omega)
    exact geAt_of_lead hord hinj (t := p + d) (hι'.mono (by omega)) e he
  lead d p m x hx hm := by
    simp only [LinearMap.mk₂_apply]
    set c := ZGr.comp MM.gr UU.gr r ι
    set m' := transAct A ι hι hstab m x
    have hc : UU.gr.IsHom (p + r) (c m) := ZGr.comp_isHom _ _ _ hm
    -- the image of `m'` is `c m · σ_d x` modulo higher terms
    have hι' : UU.gr.GeAt (p + r + d + 1) (ι m' - UU.act (c m) (P.σ d x)) := by
      rw [ι_transAct, show ι m = c m + (ι m - c m) by abel, map_add, LinearMap.add_apply]
      have h1 : UU.gr.GeAt (p + r + d + 1) (A.act (c m) x - UU.act (c m) (P.σ d x)) := by
        intro e he
        rw [map_sub]
        rcases lt_or_eq_of_le (show e ≤ p + r + d by omega) with h | rfl
        · rw [A.filt d (p + r) (c m) x hx hc e h,
            UU.gr.proj_of_isHom (UU.act_hom _ _ _ _ hc (σ_isHom (h1 := h1) d x)), if_neg (by omega),
            sub_zero]
        · rw [A.lead d (p + r) (c m) x hx hc,
            UU.gr.proj_of_isHom (UU.act_hom _ _ _ _ hc (σ_isHom (h1 := h1) d x)), if_pos (by ring),
            sub_self]
      have h2 := A.geAt_act (hord.sub_comp_geAt hm) hx
      have := h1.add (h2.mono (by omega))
      convert this using 1; abel
    have hm'ge : MM.gr.GeAt (p + d) m' := by
      refine geAt_of_lead hord hinj ?_
      have h3 : UU.gr.GeAt (p + r + d) (UU.act (c m) (P.σ d x)) :=
        UU.gr.geAt_of_isHom (UU.act_hom _ _ _ _ hc (σ_isHom (h1 := h1) d x)) (by omega)
      have := (hι'.mono (by omega)).add h3
      rw [sub_add_cancel] at this
      exact this.mono (by omega)
    -- compare the degree-`p + d + r` components
    set y := MM.gr.proj (p + d) m'
    have hy : UU.gr.GeAt (p + d + r + 1) (ι m' - c y) := by
      have e1 : ι m' - c y = (ι y - c y) + ι (m' - y) := by rw [map_sub]; abel
      rw [e1]
      exact (hord.sub_comp_geAt (MM.gr.isHom_proj (p + d) m')).add
        ((hord.geAt hm'ge.sub_proj).mono (by omega))
    apply hinj
    have hcy : UU.gr.IsHom (p + d + r) (c y) := ZGr.comp_isHom _ _ _ (MM.gr.isHom_proj _ _)
    have hca : UU.gr.IsHom (p + d + r) (c (MM.act m (P.σ d x))) :=
      ZGr.comp_isHom _ _ _ (MM.act_hom _ _ _ _ hm (σ_isHom (h1 := h1) d x))
    have e2 : UU.gr.proj (p + d + r) (ι m') = c y := by
      have := hy (p + d + r) (by omega)
      rw [map_sub, sub_eq_zero, hcy] at this
      exact this
    have hact : UU.gr.IsHom (p + r + d) (UU.act (c m) (P.σ d x)) :=
      UU.act_hom _ _ _ _ hc (σ_isHom (h1 := h1) d x)
    have e3 : UU.gr.proj (p + d + r) (ι m') = c (MM.act m (P.σ d x)) := by
      have := hι' (p + d + r) (by omega)
      rw [map_sub, sub_eq_zero] at this
      rw [this, UU.gr.proj_of_isHom hact, if_pos (by ring), ← hlin]
    exact e2.symm.trans e3

theorem FLift.transport_act (m : M) (x : B) :
    ι ((FLift.transport A ι hι hstab hord hlin hinj).act m x) = A.act (ι m) x :=
  ι_transAct A ι hι hstab m x

end PosFiltration

end MultiplicativeBasisDeformations
