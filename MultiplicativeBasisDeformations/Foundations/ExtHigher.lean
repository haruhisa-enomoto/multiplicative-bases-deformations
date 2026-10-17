import MultiplicativeBasisDeformations.Foundations.GradedDecomp

/-!
# Higher `Ext` between normalized modules (Lemma 6.3(2))

`positive-deformations.tex`: "In a minimal graded projective cover of a
nonprojective `M_i`, every summand `P⟨a⟩` has `a ≥ 1` […] A nonzero component of a
kernel inclusion `Z⟨b⟩ → P⟨a⟩` is also radical. […] Hence `b − a ≥ 1` and `b ≥ 2`.
[…] Dimension shifting gives `Ext^n(M_i, M_j)_t = Ext^1(Ω^{n−1}M_i, M_j)_t = 0`
(`t > −2n`) […] Projective summands contribute zero."

Here the cover is `P = ⊕_ℓ M_{x_ℓ}⟨d_ℓ⟩ → M_i`, `ℓ` running over homogeneous bases of
the spaces `C_d(P_x, X_i)` (`cπ`, with graded `k`-section `cs`).

Deviation: this cover need not be minimal. Minimality is used in the paper only to
see that kernel summands `Z⟨b⟩` have `b ≥ 2`. Here the bound is proved for the
nonprojective summands directly (`two_le_shift`): every component
`Z → M_{x_ℓ}` has degree `b − d_ℓ`, and it vanishes when `b − d_ℓ ≤ 0`, by
`eq:normalized-hom-degrees`, since `Z ≠ P_{x_ℓ}`. Projective summands contribute
zero whatever their shift.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-! ### The cover -/

section Cover

variable (i : V)

/-- A homogeneous basis of `C_d(P_x, X_i)`. -/
def cbasis (x : D.PV) (d : ℕ) :
    Module.Basis (Fin (Module.finrank k (degreePart c d x.1 i))) k (degreePart c d x.1 i) :=
  haveI := hfin x.1 i
  Module.finBasis k _

/-- The index set of the cover: `(x, d, basis index)`. -/
abbrev CIdx := Σ x : D.PV, Σ d : Fin (Nb hfin), Fin (Module.finrank k (degreePart c d x.1 i))

/-- The basis morphism `h_ℓ : P_x → X_i` of degree `d`. -/
def ch (ℓ : CIdx D hfin i) : obj c ℓ.1.1 ⟶ obj c i :=
  (cbasis D hfin i ℓ.1 ℓ.2.1 ℓ.2.2 : obj c ℓ.1.1 ⟶ obj c i)

theorem ch_mem (ℓ : CIdx D hfin i) : ch D hfin i ℓ ∈ degreePart c ℓ.2.1 ℓ.1.1 i :=
  (cbasis D hfin i ℓ.1 ℓ.2.1 ℓ.2.2).2

/-- The cover `P = ⊕_ℓ M_{x_ℓ}`. -/
abbrev CP := ∀ ℓ : CIdx D hfin i, Rep D.F0 (meshFam Q c ℓ.1.1)

/-- `P = ⊕_ℓ M_{x_ℓ}⟨d_ℓ⟩` as a graded module. -/
def gCP : GExt.GMod (galgA0 D hfin) (CP D hfin i) :=
  GExt.GMod.pi (fun ℓ : CIdx D hfin i ↦ gmodEv D hfin ℓ.1.1) (fun ℓ ↦ ((ℓ.2.1 : ℕ) : ℤ))

/-- The cover map `Σ_ℓ h_ℓ`. -/
def cπ : CP D hfin i →ₗ[k] Rep D.F0 (meshFam Q c i) :=
  ∑ ℓ : CIdx D hfin i, (repMap (F := D.F0) (ch D hfin i ℓ)).restrictScalars k ∘ₗ LinearMap.proj ℓ

theorem cπ_apply (y : CP D hfin i) :
    cπ D hfin i y = ∑ ℓ, repMap (F := D.F0) (ch D hfin i ℓ) (y ℓ) := by
  simp [cπ, LinearMap.sum_apply]

theorem cπ_act (y : CP D hfin i) (a : (Alg D.F0)ᵐᵒᵖ) :
    cπ D hfin i ((gCP D hfin i).act y a) = evAct D i (cπ D hfin i y) a := by
  rw [cπ_apply, cπ_apply]
  change _ = a.unop • ∑ ℓ : CIdx D hfin i, repMap (F := D.F0) (ch D hfin i ℓ) (y ℓ)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
  exact (repMap (F := D.F0) (ch D hfin i ℓ)).map_smul a.unop (y ℓ)

theorem cπ_deg (p : ℤ) (y : CP D hfin i) (hy : (gCP D hfin i).gr.IsHom p y) :
    (zgrEv D hfin i).IsHom (p + 0) (cπ D hfin i y) := by
  have hy' := (GExt.ZGr.piShift_isHom _ _ _ _).1 hy
  rw [cπ_apply, add_zero]
  refine GExt.ZGr.isHom_sum _ _ _ fun ℓ _ ↦ ?_
  have := repMap_isHom (D := D) hfin (ch_mem D hfin i ℓ) (hy' ℓ)
  rwa [sub_add_cancel] at this

/-- Evaluation at a projective label. -/
def evalAt (y : D.PV) : Rep D.F0 (meshFam Q c i) →ₗ[k] (obj c y.1 ⟶ obj c i) where
  toFun m := m y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coefficient of `h_ℓ` in the degree-`d_ℓ` part of `m_{x_ℓ}`. -/
def ccoef (ℓ : CIdx D hfin i) : Rep D.F0 (meshFam Q c i) →ₗ[k] k :=
  (Finsupp.lapply ℓ.2.2) ∘ₗ (cbasis D hfin i ℓ.1 ℓ.2.1).repr.toLinearMap ∘ₗ
    (degProj c ℓ.2.1 ℓ.1.1 i).codRestrict _ (fun f ↦ degProj_mem c _ f) ∘ₗ evalAt D i ℓ.1

theorem ccoef_apply (ℓ : CIdx D hfin i) (m : Rep D.F0 (meshFam Q c i)) :
    ccoef D hfin i ℓ m = (cbasis D hfin i ℓ.1 ℓ.2.1).repr
      ⟨degProj c ℓ.2.1 ℓ.1.1 i (m ℓ.1), degProj_mem c _ _⟩ ℓ.2.2 := rfl

/-- The graded `k`-section `m ↦ Σ_ℓ c_ℓ(m) 1_{x_ℓ}`. -/
def cs : Rep D.F0 (meshFam Q c i) →ₗ[k] CP D hfin i :=
  LinearMap.pi fun ℓ ↦ (ccoef D hfin i ℓ).smulRight (unit (F := D.F0) ℓ.1)

theorem cs_apply_apply (ℓ : CIdx D hfin i) (m : Rep D.F0 (meshFam Q c i)) (y : D.PV) :
    (repMap (F := D.F0) (ch D hfin i ℓ) (cs D hfin i m ℓ)) y =
      if ℓ.1 = y then ccoef D hfin i ℓ m • (idTo (F := D.F0) y ℓ.1 ≫ ch D hfin i ℓ) else 0 := by
  change (ccoef D hfin i ℓ m • unit (F := D.F0) ℓ.1) y ≫ ch D hfin i ℓ = _
  rw [Rep.smul_apply', Linear.smul_comp]
  split_ifs with h
  · rfl
  · change ccoef D hfin i ℓ m • (idTo (F := D.F0) y ℓ.1 ≫ ch D hfin i ℓ) = 0
    rw [idTo_ne (Ne.symm h), Limits.zero_comp, smul_zero]

theorem cπ_cs : cπ D hfin i ∘ₗ cs D hfin i = LinearMap.id := by
  refine LinearMap.ext fun m ↦ funext fun y ↦ ?_
  rw [LinearMap.comp_apply, cπ_apply, Rep.sum_apply, LinearMap.id_apply]
  simp only [cs_apply_apply]
  rw [Fintype.sum_sigma, Finset.sum_eq_single y (fun x _ hx ↦ Finset.sum_eq_zero fun ℓ _ ↦ by
      rw [if_neg hx]) (by simp)]
  simp only [if_true, idTo_self, Category.id_comp]
  rw [Fintype.sum_sigma]
  conv_rhs => rw [eq_sum_degProj c (Nb_spec hfin) (m y), ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hrepr : ∑ b, (cbasis D hfin i y d).repr ⟨degProj c d y.1 i (m y), degProj_mem c _ _⟩ b •
      (cbasis D hfin i y d b : obj c y.1 ⟶ obj c i) = degProj c d y.1 i (m y) := by
    have := congrArg Subtype.val ((cbasis D hfin i y d).sum_repr
      ⟨degProj c d y.1 i (m y), degProj_mem c _ _⟩)
    rw [Submodule.coe_sum] at this
    simpa using this
  rw [← hrepr]
  rfl

theorem cs_deg (p : ℤ) (m : Rep D.F0 (meshFam Q c i)) (hm : (zgrEv D hfin i).IsHom p m) :
    (gCP D hfin i).gr.IsHom (p + 0) (cs D hfin i m) := by
  rw [add_zero]
  refine (GExt.ZGr.piShift_isHom _ _ _ _).2 fun ℓ ↦ ?_
  rcases lt_or_ge p 0 with hp | hp
  · rw [(zgrEv_isHom_neg D hfin i hp m).1 hm, map_zero]
    exact GExt.ZGr.isHom_zero _ _
  obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [zgrEv_isHom] at hm
  change (zgrEv D hfin ℓ.1.1).IsHom _ (ccoef D hfin i ℓ m • unit (F := D.F0) ℓ.1)
  by_cases hd : (ℓ.2.1 : ℕ) = p'
  · rw [← hd, sub_self]
    refine (zgrEv D hfin ℓ.1.1).isHom_smul _ ?_
    change (zgrEv D hfin ℓ.1.1).IsHom ((0 : ℕ) : ℤ) _
    rw [zgrEv_isHom]
    intro y
    exact idTo_mem_degreePart D y ℓ.1
  · have h0 : ccoef D hfin i ℓ m = 0 := by
      have hz : (⟨degProj c ℓ.2.1 ℓ.1.1 i (m ℓ.1), degProj_mem c _ _⟩ :
          degreePart c ℓ.2.1 ℓ.1.1 i) = 0 :=
        Subtype.ext ((degProj_of_mem c (hm ℓ.1)).trans (if_neg (Ne.symm hd)))
      rw [ccoef_apply, hz, map_zero, Finsupp.zero_apply]
    rw [h0, zero_smul]
    exact GExt.ZGr.isHom_zero _ _

end Cover

/-! ### The kernel and its summands -/

section Kernel

variable (i : V)

/-- The kernel `Ω M_i` of the cover. -/
def KK : GExt.GMod (galgA0 D hfin) (LinearMap.ker (cπ D hfin i)) :=
  GExt.GMod.ker (gCP D hfin i) (gmodEv D hfin i) (cπ_act D hfin i) (cπ_deg D hfin i)

/-- At a nonprojective label every cover summand has positive shift. -/
theorem one_le_shift (hi : ¬ D.proj i) (ℓ : CIdx D hfin i) : 1 ≤ (ℓ.2.1 : ℕ) := by
  by_contra h0
  have hd : (ℓ.2.1 : ℕ) = 0 := by omega
  have hne : ℓ.1.1 ≠ i := fun h ↦ hi (h ▸ ℓ.1.2)
  have hmem := ch_mem D hfin i ℓ
  rw [hd] at hmem
  apply (cbasis D hfin i ℓ.1 ℓ.2.1).ne_zero ℓ.2.2
  exact Subtype.ext (degreePart_zero_ne hne hmem)

theorem KK_isHom (p : ℤ) (x : LinearMap.ker (cπ D hfin i)) :
    (KK D hfin i).gr.IsHom p x ↔ (gCP D hfin i).gr.IsHom p (x : CP D hfin i) :=
  GExt.ZGr.ker_isHom (gCP D hfin i) (gmodEv D hfin i) (cπ_deg D hfin i) p x

include hfd in
/-- A graded map of degree `s ≤ 0` between evaluated modules at distinct labels vanishes. -/
theorem eq_zero_of_deg_nonpos {Y Z : V} (hYZ : Y ≠ Z) {s : ℤ} (hs : s ≤ 0)
    (u : Rep D.F0 (meshFam Q c Y) →ₗ[k] Rep D.F0 (meshFam Q c Z))
    (hu : ∀ m x, u (evAct D Y m x) = evAct D Z (u m) x)
    (hdeg : ∀ p m, (zgrEv D hfin Y).IsHom p m → (zgrEv D hfin Z).IsHom (p + s) (u m)) : u = 0 := by
  rw [← GExt.ZGr.comp_eq_self_of_hom (zgrEv D hfin Y) (zgrEv D hfin Z) hdeg]
  rcases hs.lt_or_eq with hneg | h0
  · exact hom_comp_neg D hfin u hu hneg
  · rw [h0]
    exact hom_comp_zero_ne D hfin hYZ u hu

include hfd in
/-- **Nonprojective kernel summands have shift at least two.** -/
theorem two_le_shift (hi : ¬ D.proj i) (d : GDecomp D hfin (KK D hfin i) LinearMap.id) (a : d.μ)
    (ha : d.inc a ≠ 0) (hz : ¬ D.proj (d.W a)) : 2 ≤ d.s a := by
  by_contra hlt
  apply ha
  refine LinearMap.ext fun m ↦ Subtype.ext (funext fun ℓ ↦ ?_)
  have hℓ := one_le_shift D hfin i hi ℓ
  have hzero := eq_zero_of_deg_nonpos D hfin (Y := d.W a) (Z := ℓ.1.1)
    (fun h ↦ hz (by rw [h]; exact ℓ.1.2))
    (s := d.s a - ((ℓ.2.1 : ℕ) : ℤ)) (by omega)
    (LinearMap.proj (R := k) (φ := fun ℓ : CIdx D hfin i ↦ Rep D.F0 (meshFam Q c ℓ.1.1)) ℓ ∘ₗ
      (LinearMap.ker (cπ D hfin i)).subtype ∘ₗ d.inc a)
    (fun m x ↦ by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply]
      rw [d.inc_act]
      rfl)
    (fun p m hm ↦ by
      have h1 := (KK_isHom D hfin i _ _).1 (d.inc_deg a p m hm)
      have h2 := (GExt.ZGr.piShift_isHom _ _ _ _).1 h1 ℓ
      rwa [show p + d.s a - ((ℓ.2.1 : ℕ) : ℤ) = p + (d.s a - (ℓ.2.1 : ℕ)) by ring] at h2)
  exact LinearMap.congr_fun hzero m

end Kernel

/-! ### The vanishing -/

include hfd in
/-- **Lemma 6.3(2)**: `Ext^{n+1}_{A₀}(M_i, M_j)_t = 0` for `t > -2(n+1)`, and for all `t`
when `M_i` is projective. -/
theorem extVanish_ev (J : InjData D) (h1 : DegOne D) (n : ℕ) :
    ∀ i j : V, ∀ t : ℤ, (D.proj i ∨ -2 * ((n : ℤ) + 1) < t) →
      GExt.ExtVanish (gmodEv D hfin i) (gmodEv D hfin j) n t := by
  induction n with
  | zero =>
    intro i j t h
    by_cases hi : D.proj i
    · exact extVanish_proj D hfin ⟨i, hi⟩ _ 0 t
    · exact extOne_vanish hfin J h1 i j (by have := h.resolve_left hi; push_cast at this; omega)
  | succ n ih =>
    intro i j t h
    by_cases hi : D.proj i
    · exact extVanish_proj D hfin ⟨i, hi⟩ _ _ t
    have ht := h.resolve_left hi
    push_cast at ht
    obtain ⟨d⟩ := exists_gdecomp D hfin (KK D hfin i) J
    let ρ : CP D hfin i →ₗ[k] LinearMap.ker (cπ D hfin i) :=
      (LinearMap.id - cs D hfin i ∘ₗ cπ D hfin i).codRestrict _ fun x ↦ by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
          ← LinearMap.comp_apply (cπ D hfin i), ← LinearMap.comp_assoc, cπ_cs,
          LinearMap.id_comp, sub_self]
    have hπι : cπ D hfin i ∘ₗ (LinearMap.ker (cπ D hfin i)).subtype = 0 :=
      LinearMap.ext fun x ↦ x.2
    refine GExt.extVanish_shift (KK := KK D hfin i) (PP := gCP D hfin i)
      (LinearMap.ker (cπ D hfin i)).subtype (cπ D hfin i) (cs D hfin i) ρ
      (fun _ _ ↦ rfl) (cπ_act D hfin i)
      (fun p x hx ↦ by rw [add_zero]; exact (KK_isHom D hfin i _ _).1 hx)
      (cπ_deg D hfin i) (cs_deg D hfin i)
      (fun p x hx ↦ by
        rw [add_zero, KK_isHom]
        change (gCP D hfin i).gr.IsHom p (x - cs D hfin i (cπ D hfin i x))
        have h2 := cs_deg D hfin i _ _ (cπ_deg D hfin i p x hx)
        simp only [add_zero] at h2
        rw [sub_eq_add_neg]
        exact (gCP D hfin i).gr.isHom_add hx ((gCP D hfin i).gr.isHom_neg h2))
      (cπ_cs D hfin i)
      (LinearMap.ext fun x ↦ Subtype.ext (by
        change (x : CP D hfin i) - cs D hfin i (cπ D hfin i x) = x
        rw [LinearMap.mem_ker.1 x.2, map_zero, sub_zero]))
      (LinearMap.ext fun x ↦ by
        change (x - cs D hfin i (cπ D hfin i x)) + cs D hfin i (cπ D hfin i x) = x
        rw [sub_add_cancel])
      hπι
      (GExt.extVanish_pi _ _ _ _ fun ℓ ↦ extVanish_proj D hfin ℓ.1 _ _ _)
      (GExt.extVanish_of_decomp (MM := KK D hfin i) (fun a ↦ gmodEv D hfin (d.W a)) d.s d.inc
        d.pr d.inc_act d.pr_act d.inc_deg d.pr_deg
        (fun m ↦ by
          have := LinearMap.congr_fun d.sum m
          simpa [LinearMap.sum_apply] using this)
        n t fun a ha ↦ ih (d.W a) j (t + d.s a) (by
          by_cases hz : D.proj (d.W a)
          · exact Or.inl hz
          · right
            have := two_le_shift D hfin i hi d a ha hz
            push_cast
            omega))

end MeshWalk

end MultiplicativeBasisDeformations
