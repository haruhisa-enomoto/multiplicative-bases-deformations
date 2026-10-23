module

public import MultiplicativeBasisDeformations.Refinements.SplitDeformation

/-!
# Proposition 6.5(1) for arbitrary filtered lifts

`prop:positive-module-lifting`(1): "Each `M_i` has a filtered lift `M_i^B` with `gr M_i^B = M_i`,
unique up to an isomorphism with prescribed leading identity."

`FLift` is a `B`-action on the graded space `M` itself. Here a filtered lift is any right
`B`-module `N` with a finite decreasing filtration `F^p N`, compatible with the filtration of `B`,
and an identification `gr N = M` of graded `Λ`-modules: symbols `ι_p : F^p N → M_p`, onto, with
kernel `F^{p+1} N`, and `ι_{p+d}(n x) = ι_p(n) σ_d(x)` (`GenLift`). As in the source, choosing
linear sections of the `ι_p` identifies `N` with `M` as filtered spaces and carries the action to
an `FLift` (`GenLift.exists_model`). Hence a lift exists (`exists_genLift`) and two filtered lifts
are isomorphic by a `B`-linear isomorphism preserving the filtrations with leading term the
identity (`genLift_unique`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

namespace PosFiltration

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] (P : PosFiltration G B)
  {M : Type*} [AddCommGroup M] [Module k M] (h1 : G.IsHom 0 (1 : Λ))
  (MM : GExt.GMod (GExt.GAlg.ofLen G h1) M)

/-- **A filtered lift of `M` to `B`**: a right `B`-module `N` with a finite decreasing filtration
compatible with that of `B` and an identification `gr N = M` of graded `Λ`-modules, given by
symbols `ι_p : F^p N → M_p`, onto, with kernel `F^{p+1} N`, and multiplicative. -/
structure GenLift (N : Type*) [AddCommGroup N] [Module k N] where
  act : N →ₗ[k] B →ₗ[k] N
  mul : ∀ n x y, act (act n x) y = act n (x * y)
  one : ∀ n, act n 1 = n
  F : ℤ → Submodule k N
  anti : ∀ p, F (p + 1) ≤ F p
  top : ∃ p₀, F p₀ = ⊤
  bot : ∃ p₁, F p₁ = ⊥
  act_mem : ∀ (d : ℕ) p n x, x ∈ P.F d → n ∈ F p → act n x ∈ F (p + d)
  ι : ℤ → N →ₗ[k] M
  ι_hom : ∀ p n, n ∈ F p → MM.gr.IsHom p (ι p n)
  ι_ker : ∀ p n, n ∈ F p → (ι p n = 0 ↔ n ∈ F (p + 1))
  ι_surj : ∀ p m, MM.gr.IsHom p m → ∃ n ∈ F p, ι p n = m
  ι_act : ∀ (d : ℕ) p n x, x ∈ P.F d → n ∈ F p →
    ι (p + d) (act n x) = MM.act (ι p n) (P.σ d x)

variable {P h1 MM}

namespace GenLift

variable {N : Type*} [AddCommGroup N] [Module k N] (L : GenLift P h1 MM N)

theorem F_anti {p q : ℤ} (h : p ≤ q) : L.F q ≤ L.F p := by
  obtain ⟨j, rfl⟩ := Int.le.dest h
  clear h
  induction j with
  | zero => simp
  | succ j ih =>
      have e : p + ((j + 1 : ℕ) : ℤ) = (p + j) + 1 := by push_cast; ring
      rw [e]
      exact (L.anti _).trans ih

/-- The homogeneous part `M_p`. -/
abbrev Mp (p : ℤ) : Submodule k M := LinearMap.range (MM.gr.proj p)

/-- The symbol on `F^p N`, onto `M_p`. -/
def ιr (p : ℤ) : L.F p →ₗ[k] Mp (MM := MM) p :=
  LinearMap.codRestrict _ (L.ι p ∘ₗ (L.F p).subtype) fun n ↦ ⟨L.ι p n, L.ι_hom p n n.2⟩

theorem ιr_surjective (p : ℤ) : LinearMap.range (L.ιr p) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨m, m', rfl⟩ -
  obtain ⟨n, hn, hι⟩ := L.ι_surj p _ (MM.gr.isHom_proj p m')
  exact ⟨⟨n, hn⟩, Subtype.ext hι⟩

/-- A linear section of `ι_p` on the degree-`p` part. -/
def sec (p : ℤ) : M →ₗ[k] N :=
  (L.F p).subtype ∘ₗ (Classical.choose (LinearMap.exists_rightInverse_of_surjective _
    (L.ιr_surjective p))) ∘ₗ (MM.gr.proj p).rangeRestrict

theorem sec_mem (p : ℤ) (m : M) : L.sec p m ∈ L.F p := by
  simp only [sec, LinearMap.comp_apply, Submodule.subtype_apply]
  exact Subtype.property _

theorem ι_sec (p : ℤ) (m : M) : L.ι p (L.sec p m) = MM.gr.proj p m := by
  have h := Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective _
    (L.ιr_surjective p))
  have h2 := congrArg Subtype.val (LinearMap.congr_fun h ((MM.gr.proj p).rangeRestrict m))
  exact h2

theorem sec_eq_zero (p : ℤ) {m : M} (hm : MM.gr.proj p m = 0) : L.sec p m = 0 := by
  have : (MM.gr.proj p).rangeRestrict m = 0 := Subtype.ext hm
  simp only [sec, LinearMap.comp_apply, this, map_zero]

/-- **The identification** `M ≅ N` assembled from the sections. -/
def ψ : M →ₗ[k] N := ∑ p ∈ MM.gr.supp, L.sec p

/-- `M_{≥ p}`: the elements with no components below `p`. -/
def Ge (p : ℤ) (m : M) : Prop := ∀ e, e < p → MM.gr.proj e m = 0

theorem ψ_mem_ι {p : ℤ} {m : M} (hm : Ge (MM := MM) p m) :
    L.ψ m ∈ L.F p ∧ L.ι p (L.ψ m) = MM.gr.proj p m := by
  have hterm : ∀ q, L.sec q m ∈ L.F p ∧ L.ι p (L.sec q m) = if q = p then MM.gr.proj p m else 0 := by
    intro q
    rcases lt_trichotomy q p with h | rfl | h
    · rw [L.sec_eq_zero q (hm q h), if_neg h.ne]; exact ⟨zero_mem _, map_zero _⟩
    · rw [if_pos rfl]; exact ⟨L.sec_mem q m, L.ι_sec q m⟩
    · have h' : L.sec q m ∈ L.F (p + 1) := L.F_anti (by omega) (L.sec_mem q m)
      rw [if_neg h.ne']
      exact ⟨L.anti p h', (L.ι_ker p _ (L.anti p h')).2 h'⟩
  simp only [ψ, LinearMap.sum_apply]
  refine ⟨Submodule.sum_mem _ fun q _ ↦ (hterm q).1, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun q _ ↦ (hterm q).2, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MM.gr.proj_out p h]; rfl

theorem ge_of_le {p q : ℤ} {m : M} (h : p ≤ q) (hm : Ge (MM := MM) q m) : Ge (MM := MM) p m :=
  fun e he ↦ hm e (by omega)

/-- An element with a nonzero component has a lowest one. -/
theorem exists_lowest {m : M} (hm : m ≠ 0) :
    ∃ e, MM.gr.proj e m ≠ 0 ∧ Ge (MM := MM) e m := by
  classical
  have hne : (MM.gr.supp.filter fun e ↦ MM.gr.proj e m ≠ 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hm
    rw [MM.gr.sum m]
    exact Finset.sum_eq_zero fun e he ↦ not_not.1 (h he)
  set e := (MM.gr.supp.filter fun e ↦ MM.gr.proj e m ≠ 0).min' hne
  have he := Finset.min'_mem _ hne
  refine ⟨e, (Finset.mem_filter.1 he).2, fun e' he' ↦ ?_⟩
  by_contra h
  by_cases hs : e' ∈ MM.gr.supp
  · have := Finset.min'_le _ e'
      ((Finset.mem_filter (p := fun e ↦ MM.gr.proj e m ≠ 0)).2 ⟨hs, h⟩)
    omega
  · exact h (by rw [MM.gr.proj_out e' hs]; rfl)

theorem ge_of_ψ_mem {p : ℤ} {m : M} (h : L.ψ m ∈ L.F p) : Ge (MM := MM) p m := by
  by_contra hne
  have hm : m ≠ 0 := by
    rintro rfl; exact hne fun e _ ↦ map_zero _
  obtain ⟨e, he, hge⟩ := exists_lowest (MM := MM) hm
  have hep : e < p := by
    by_contra hle
    exact hne (ge_of_le (MM := MM) (not_lt.1 hle) hge)
  obtain ⟨-, hι⟩ := L.ψ_mem_ι hge
  have h' : L.ψ m ∈ L.F (e + 1) := L.F_anti (by omega) h
  rw [(L.ι_ker e _ (L.anti e h')).2 h'] at hι
  exact he hι.symm

theorem ψ_injective : Function.Injective L.ψ := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  by_contra hne
  obtain ⟨e, he, hge⟩ := exists_lowest (MM := MM) hne
  obtain ⟨-, hι⟩ := L.ψ_mem_ι hge
  rw [hm, map_zero] at hι
  exact he hι.symm

theorem ψ_surjective : Function.Surjective L.ψ := by
  obtain ⟨p₀, hp₀⟩ := L.top
  obtain ⟨p₁, hp₁⟩ := L.bot
  have key : ∀ j : ℕ, ∀ n ∈ L.F (p₁ - j), n ∈ LinearMap.range L.ψ := by
    intro j
    induction j with
    | zero =>
        intro n hn
        simp only [CharP.cast_eq_zero, sub_zero, hp₁, Submodule.mem_bot] at hn
        rw [hn]; exact zero_mem _
    | succ j ih =>
        intro n hn
        set p := p₁ - ((j + 1 : ℕ) : ℤ)
        have hm : Ge (MM := MM) p (MM.gr.proj p (L.ι p n)) := fun e he ↦ by
          rw [MM.gr.proj_proj, if_neg (by omega)]
        obtain ⟨h1', h2'⟩ := L.ψ_mem_ι hm
        have hd : n - L.ψ (MM.gr.proj p (L.ι p n)) ∈ L.F (p + 1) := by
          rw [← L.ι_ker p _ (sub_mem hn h1'), map_sub, h2', MM.gr.proj_proj, if_pos rfl,
            L.ι_hom p n hn, sub_self]
        have hd' : p + 1 = p₁ - j := by simp only [p]; push_cast; ring
        rw [hd'] at hd
        obtain ⟨m, hm'⟩ := ih _ hd
        exact ⟨m + MM.gr.proj p (L.ι p n), by rw [map_add, hm', sub_add_cancel]⟩
  intro n
  rcases le_or_gt p₁ p₀ with h | h
  · have hn : n ∈ L.F p₁ := by
      have := L.F_anti h; rw [hp₀] at this; exact this trivial
    rw [hp₁, Submodule.mem_bot] at hn
    exact ⟨0, by rw [hn, map_zero]⟩
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, p₁ - j ≤ p₀ := ⟨(p₁ - p₀).toNat, by omega⟩
    have hn : n ∈ L.F (p₁ - j) := by
      have := L.F_anti hj; rw [hp₀] at this; exact this trivial
    exact key j n hn

/-- `ψ` as a linear isomorphism. -/
def ψe : M ≃ₗ[k] N := LinearEquiv.ofBijective L.ψ ⟨L.ψ_injective, L.ψ_surjective⟩

/-- **The model of a filtered lift on `M`** (`exists_model`). -/
def model : FLift P h1 MM where
  act :=
    { toFun := fun m ↦ L.ψe.symm.toLinearMap ∘ₗ L.act (L.ψe m)
      map_add' := fun m m' ↦ by rw [map_add, map_add, LinearMap.comp_add]
      map_smul' := fun c m ↦ by rw [map_smul, map_smul, LinearMap.comp_smul]; rfl }
  mul m x y := by
    change L.ψe.symm (L.act (L.ψe (L.ψe.symm (L.act (L.ψe m) x))) y) =
      L.ψe.symm (L.act (L.ψe m) (x * y))
    rw [LinearEquiv.apply_symm_apply, L.mul]
  one m := by
    change L.ψe.symm (L.act (L.ψe m) 1) = m
    rw [L.one, LinearEquiv.symm_apply_apply]
  filt d p m x hx hm e he := by
    change MM.gr.proj e (L.ψe.symm (L.act (L.ψ m) x)) = 0
    have hn : L.ψ m ∈ L.F p := (L.ψ_mem_ι (fun e he ↦ by
      rw [MM.gr.proj_of_isHom hm, if_neg (by omega)])).1
    have h := L.act_mem d p _ x hx hn
    rw [← L.ψe.apply_symm_apply (L.act (L.ψ m) x)] at h
    exact L.ge_of_ψ_mem h e he
  lead d p m x hx hm := by
    change MM.gr.proj (p + d) (L.ψe.symm (L.act (L.ψ m) x)) = _
    have hge : Ge (MM := MM) p m := fun e he ↦ by rw [MM.gr.proj_of_isHom hm, if_neg (by omega)]
    obtain ⟨hn, hι⟩ := L.ψ_mem_ι hge
    rw [MM.gr.proj_of_isHom hm, if_pos rfl] at hι
    set m' := L.ψe.symm (L.act (L.ψ m) x)
    have hm' : L.ψ m' = L.act (L.ψ m) x := L.ψe.apply_symm_apply _
    have hge' : Ge (MM := MM) (p + d) m' := L.ge_of_ψ_mem (by rw [hm']; exact L.act_mem d p _ x hx hn)
    obtain ⟨-, hι'⟩ := L.ψ_mem_ι hge'
    rw [← hι', hm', L.ι_act d p _ x hx hn, hι]

theorem model_act (m : M) (x : B) : L.ψ (L.model.act m x) = L.act (L.ψ m) x :=
  L.ψe.apply_symm_apply _

end GenLift

namespace FLift

/-- **A lift on `M` is a filtered lift**, with the degree filtration. -/
def toGenLift (A : FLift P h1 MM) : GenLift P h1 MM M where
  act := A.act
  mul := A.mul
  one := A.one
  F p :=
    { carrier := {m | GenLift.Ge (MM := MM) p m}
      add_mem' := fun ha hb e he ↦ by rw [map_add, ha e he, hb e he, add_zero]
      zero_mem' := fun e _ ↦ map_zero _
      smul_mem' := fun c m hm e he ↦ by rw [map_smul, hm e he, smul_zero] }
  anti p m hm e he := hm e (by omega)
  top := by
    refine ⟨-((MM.gr.supp.sup Int.natAbs : ℕ) : ℤ) - 1, eq_top_iff.2 fun m _ e he ↦ ?_⟩
    by_cases hs : e ∈ MM.gr.supp
    · have := Finset.le_sup (f := Int.natAbs) hs
      omega
    · rw [MM.gr.proj_out e hs]; rfl
  bot := by
    refine ⟨((MM.gr.supp.sup Int.natAbs : ℕ) : ℤ) + 1, eq_bot_iff.2 fun m hm ↦ ?_⟩
    rw [Submodule.mem_bot, MM.gr.sum m]
    refine Finset.sum_eq_zero fun e he ↦ hm e ?_
    have := Finset.le_sup (f := Int.natAbs) he
    omega
  act_mem d p m x hx hm e he := by
    change GenLift.Ge (MM := MM) p m at hm
    rw [MM.gr.sum m, map_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    by_cases hq : q < p
    · rw [hm q hq, map_zero, LinearMap.zero_apply, map_zero]
    · exact A.filt d q _ x hx (MM.gr.isHom_proj q m) e (by omega)
  ι p := MM.gr.proj p
  ι_hom p m _ := MM.gr.isHom_proj p m
  ι_ker p m hm := by
    constructor
    · intro h e he
      rcases lt_or_eq_of_le (Int.lt_add_one_iff.1 he) with h' | rfl
      · exact hm e h'
      · exact h
    · intro h; exact h p (by omega)
  ι_surj p m hm := ⟨m, fun e he ↦ by rw [MM.gr.proj_of_isHom hm, if_neg (by omega)], hm⟩
  ι_act d p m x hx hm := by
    change GenLift.Ge (MM := MM) p m at hm
    conv_lhs => rw [MM.gr.sum m]
    rw [map_sum, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single p]
    · rw [A.lead d p _ x hx (MM.gr.isHom_proj p m)]
    · intro q _ hqp
      rcases lt_or_gt_of_ne hqp with h | h
      · rw [hm q h, map_zero, LinearMap.zero_apply, map_zero]
      · exact A.filt d q _ x hx (MM.gr.isHom_proj q m) _ (by omega)
    · intro hp
      rw [MM.gr.proj_out p hp, LinearMap.zero_apply, map_zero, LinearMap.zero_apply, map_zero]

end FLift

section Statements

variable (hS : Nonempty (Split P))

include hS in
/-- **Proposition 6.5(1), existence**: under `Ext²_Λ(M, M)_t = 0` for `t > 0`, `M` has a filtered
lift (on `M` itself, with the degree filtration). -/
theorem exists_genLift (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 1 t) :
    Nonempty (GenLift P h1 MM M) := by
  obtain ⟨A⟩ := exists_fLift_of_split hS hExt
  exact ⟨A.toGenLift⟩

include hS in
/-- **Proposition 6.5(1), uniqueness** for arbitrary filtered lifts: under `Ext¹_Λ(M, M)_t = 0`
for `t > 0`, two filtered lifts `N`, `N'` of `M` are isomorphic by a `B`-linear isomorphism
preserving the filtrations with leading term the identity: `ι'_p(Ψ n) = ι_p(n)` on `F^p N`. -/
theorem genLift_unique (hExt : ∀ t : ℕ, 0 < t → GExt.ExtVanish MM MM 0 t)
    {N N' : Type*} [AddCommGroup N] [Module k N] [AddCommGroup N'] [Module k N']
    (L : GenLift P h1 MM N) (L' : GenLift P h1 MM N') :
    ∃ Ψ : N ≃ₗ[k] N', (∀ n x, Ψ (L.act n x) = L'.act (Ψ n) x) ∧
      ∀ p n, n ∈ L.F p → Ψ n ∈ L'.F p ∧ L'.ι p (Ψ n) = L.ι p n := by
  obtain ⟨Φ, hΦ, hlead⟩ := fLift_unique_of_split hS hExt L.model L'.model
  refine ⟨L.ψe.symm.trans (Φ.trans L'.ψe), fun n x ↦ ?_, fun p n hn ↦ ?_⟩
  · simp only [LinearEquiv.trans_apply]
    obtain ⟨m, rfl⟩ := L.ψe.surjective n
    rw [LinearEquiv.symm_apply_apply]
    change L'.ψ (Φ (L.ψe.symm (L.act (L.ψ m) x))) = L'.act (L'.ψ (Φ m)) x
    rw [← L.model_act, ← L'.model_act, ← hΦ]
    congr 2
    exact L.ψe.symm_apply_apply _
  · obtain ⟨m, rfl⟩ := L.ψe.surjective n
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have hge : GenLift.Ge (MM := MM) p m := L.ge_of_ψ_mem hn
    -- `Φ` preserves `M_{≥ p}` with leading term the identity
    have hcomp : ∀ e, e ≤ p → MM.gr.proj e (Φ m) = MM.gr.proj e m := by
      intro e he
      have hsum : Φ m = ∑ q ∈ MM.gr.supp, Φ (MM.gr.proj q m) := by
        conv_lhs => rw [MM.gr.sum m]
        rw [map_sum]
      have hterm : ∀ q ∈ MM.gr.supp, MM.gr.proj e (Φ (MM.gr.proj q m)) =
          if q = e then MM.gr.proj q m else 0 := by
        intro q _
        by_cases hq : q < p
        · rw [hge q hq, map_zero, map_zero]
          split_ifs <;> simp [hge q hq]
        · rw [hlead q _ (MM.gr.isHom_proj q m) e (by omega)]
          by_cases hqe : q = e
          · rw [if_pos hqe.symm, if_pos hqe]
          · rw [if_neg (Ne.symm hqe), if_neg hqe]
      rw [hsum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      split_ifs with hs
      · rfl
      · rw [MM.gr.proj_out e hs]; rfl
    have hΦge : GenLift.Ge (MM := MM) p (Φ m) ∧ MM.gr.proj p (Φ m) = MM.gr.proj p m :=
      ⟨fun e he ↦ by rw [hcomp e he.le, hge e he], hcomp p le_rfl⟩
    obtain ⟨h1', h2'⟩ := L'.ψ_mem_ι hΦge.1
    obtain ⟨-, h3'⟩ := L.ψ_mem_ι hge
    refine ⟨h1', ?_⟩
    change L'.ι p (L'.ψ (Φ m)) = L.ι p (L.ψ m)
    rw [h2', hΦge.2, ← h3']

end Statements

end PosFiltration

end MultiplicativeBasisDeformations
