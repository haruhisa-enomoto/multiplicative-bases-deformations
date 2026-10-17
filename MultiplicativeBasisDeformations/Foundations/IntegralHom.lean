import MultiplicativeBasisDeformations.Foundations.IntegralLifts

/-!
# Proposition 10.1(1): the Hom modules of `E₄` are free, and `E₄/2E₄ = C⁽²⁾`

`integral-deformations.tex:46–90` (`prop:fixed-integral-companion`(1)): "Its Hom modules are
free over `𝒪`, and `E₄/2E₄ = C⁽²⁾`." Here `E₄` is the graded Hom category of the lifts
`M̃_i` of the modules `M_i` of `C⁽²⁾` (`ModLift`).

For lifts `M̃ → M`, `Ñ → N` (`IsLift`) and a degree `d`, let `H̃_d` be the graded `Λ̃`-module
maps `M̃ → Ñ` of degree `d` and `H_d` the graded `Λ`-module maps `M → N` of degree `d`.
Reduction `H̃_d → H_d` (`redHom`) is surjective when `Ext¹_d(M, N) = 0` (`exists_liftHom`),
its kernel is `2H̃_d` (`ker_redHom`), and `2f = 0` forces `red f = 0` (`redHom_of_two`). A
finite `ℤ/4`-module with such a reduction onto an `𝔽₂`-space is free on lifts of a basis
(`free_of_red`). So `H̃_d` is free with `H̃_d/2H̃_d = H_d` (`homFree`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace WLift

open GExt

/-! ### Free `ℤ/4`-modules from reductions -/

theorem red_eq_zero_iff (a : ZMod 4) : Z4.red a = 0 ↔ a = 0 ∨ a = 2 := by
  revert a; decide

/-- **A finite `ℤ/4`-module reducing onto an `𝔽₂`-space with kernel `2H` and `2x = 0 ⟹ red x
= 0` is free on lifts of a basis.** -/
theorem free_of_red {H' H : Type*} [AddCommGroup H'] [Module (ZMod 4) H'] [AddCommGroup H]
    [Module 𝔽₂ H] {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝔽₂ H) (r : H' →+ H)
    (hrs : ∀ (a : ZMod 4) x, r (a • x) = Z4.red a • r x) (hsurj : Function.Surjective r)
    (hker : ∀ x, r x = 0 → ∃ y, x = (2 : ZMod 4) • y)
    (hann : ∀ x, (2 : ZMod 4) • x = 0 → r x = 0) :
    ∃ b' : Module.Basis ι (ZMod 4) H', ∀ i, r (b' i) = b i := by
  classical
  choose e he using fun i ↦ hsurj (b i)
  have hr_sum : ∀ a : ι → ZMod 4, r (∑ i, a i • e i) = ∑ i, Z4.red (a i) • b i := by
    intro a
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hrs, he]
  -- the lift of a combination of the basis
  have hlift : ∀ x : H', ∃ a : ι → ZMod 4, r (x - ∑ i, a i • e i) = 0 := by
    intro x
    refine ⟨fun i ↦ Z4.lift (b.repr (r x) i), ?_⟩
    rw [map_sub, hr_sum]
    simp only [Z4.red_lift]
    rw [b.sum_repr, sub_self]
  have hli : LinearIndependent (ZMod 4) e := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h1 : ∀ j, Z4.red (a j) = 0 := by
      have := congrArg r ha
      rw [hr_sum, map_zero] at this
      exact fun j ↦ (Fintype.linearIndependent_iff.1 b.linearIndependent) _ this j
    have hhalf : ∀ j, ∃ c : ZMod 4, a j = 2 * c := fun j ↦ by
      rcases (red_eq_zero_iff _).1 (h1 j) with h | h
      · exact ⟨0, by rw [h]; rfl⟩
      · exact ⟨1, by rw [h]; rfl⟩
    choose c hc using hhalf
    have h2 : (2 : ZMod 4) • ∑ j, c j • e j = 0 := by
      rw [Finset.smul_sum]
      simp only [smul_smul]
      rw [← ha]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hc j]
    have h3 := hann _ h2
    rw [hr_sum] at h3
    have h4 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h3 i
    rw [hc i]
    rcases (red_eq_zero_iff _).1 h4 with h | h
    · rw [h, mul_zero]
    · rw [h]; rfl
  have hsp : ⊤ ≤ Submodule.span (ZMod 4) (Set.range e) := by
    intro x _
    obtain ⟨a, ha⟩ := hlift x
    obtain ⟨y, hy⟩ := hker _ ha
    obtain ⟨a', ha'⟩ := hlift y
    obtain ⟨z, hz⟩ := hker _ ha'
    have hx : x = ∑ i, a i • e i + (2 : ZMod 4) • (∑ i, a' i • e i + (2 : ZMod 4) • z) := by
      rw [← hz, add_sub_cancel, ← hy, add_sub_cancel]
    rw [hx, smul_add, smul_smul, show (2 : ZMod 4) * 2 = 0 from rfl, zero_smul, add_zero]
    refine add_mem (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨i, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)))
  exact ⟨Module.Basis.mk hli hsp, fun i ↦ by rw [Module.Basis.mk_apply, he]⟩

/-! ### Reduction of module maps -/

variable {Λ : Type*} [Ring Λ] [Algebra 𝔽₂ Λ] {GΛ : GAlg (R := 𝔽₂) Λ}
  {Λ' : Type*} [Ring Λ'] [Algebra (ZMod 4) Λ'] {GΛ' : GAlg (R := ZMod 4) Λ'} {π : Λ' →+* Λ}

section Hom

variable {M : Type*} [AddCommGroup M] [Module 𝔽₂ M] {M' : Type*} [AddCommGroup M']
  [Module (ZMod 4) M'] {MM' : GMod GΛ' M'} {MM : GMod GΛ M} {ρM : M' →+ M}
  {N : Type*} [AddCommGroup N] [Module 𝔽₂ N] {N' : Type*} [AddCommGroup N']
  [Module (ZMod 4) N'] {NN' : GMod GΛ' N'} {NN : GMod GΛ N} {ρN : N' →+ N}
  (hπ : IsRed GΛ' GΛ π) (HM : IsLift MM' MM π ρM) (HN : IsLift NN' NN π ρN)

variable (MM' NN') in
/-- **`H̃_d`**: the graded `Λ̃`-module maps `M̃ → Ñ` of degree `d`. -/
def homD' (d : ℤ) : Submodule (ZMod 4) (M' →ₗ[ZMod 4] N') where
  carrier := {f | (∀ m b, f (MM'.act m b) = NN'.act (f m) b) ∧
    ∀ p m, MM'.gr.IsHom p m → NN'.gr.IsHom (p + d) (f m)}
  add_mem' {f g} hf hg := ⟨fun m b ↦ by simp [hf.1 m b, hg.1 m b],
    fun p m hm ↦ NN'.gr.isHom_add (hf.2 p m hm) (hg.2 p m hm)⟩
  zero_mem' := ⟨fun m b ↦ by simp, fun p m _ ↦ by simpa using NN'.gr.isHom_zero (p + d)⟩
  smul_mem' a f hf := ⟨fun m b ↦ by simp [hf.1 m b], fun p m hm ↦ by
    simpa using NN'.gr.isHom_smul a (hf.2 p m hm)⟩

variable (MM NN) in
/-- **`H_d`**: the graded `Λ`-module maps `M → N` of degree `d`. -/
def homD (d : ℤ) : Submodule 𝔽₂ (M →ₗ[𝔽₂] N) where
  carrier := {f | (∀ m b, f (MM.act m b) = NN.act (f m) b) ∧
    ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + d) (f m)}
  add_mem' {f g} hf hg := ⟨fun m b ↦ by simp [hf.1 m b, hg.1 m b],
    fun p m hm ↦ NN.gr.isHom_add (hf.2 p m hm) (hg.2 p m hm)⟩
  zero_mem' := ⟨fun m b ↦ by simp, fun p m _ ↦ by simpa using NN.gr.isHom_zero (p + d)⟩
  smul_mem' a f hf := ⟨fun m b ↦ by simp [hf.1 m b], fun p m hm ↦ by
    simpa using NN.gr.isHom_smul a (hf.2 p m hm)⟩

include HM HN in
theorem redL_indep (f : M' →ₗ[ZMod 4] N') {m₁ m₂ : M'} (h : ρM m₁ = ρM m₂) :
    ρN (f m₁) = ρN (f m₂) := by
  obtain ⟨x, hx⟩ := HM.ker (m₁ - m₂) (by rw [map_sub, h, sub_self])
  have : f m₁ = f m₂ + (2 : ZMod 4) • f x := by
    rw [← map_smul, ← hx, ← map_add, add_sub_cancel]
  rw [this, map_add, HN.ρ_two_smul, add_zero]

/-- **The reduction of an `𝒪`-linear map** `M̃ → Ñ`, as an `𝔽₂`-linear map `M → N`. -/
def redL (f : M' →ₗ[ZMod 4] N') : M →ₗ[𝔽₂] N where
  toFun m := ρN (f (Classical.choose (HM.ρ_surj m)))
  map_add' m n := by
    rw [← map_add, ← map_add]
    exact redL_indep HM HN f (by rw [map_add, Classical.choose_spec (HM.ρ_surj _),
      Classical.choose_spec (HM.ρ_surj _), Classical.choose_spec (HM.ρ_surj _)])
  map_smul' c m := by
    rw [RingHom.id_apply, ← Z4.red_lift c, ← HN.smul, ← map_smul]
    exact redL_indep HM HN f (by rw [HM.smul, Classical.choose_spec (HM.ρ_surj _),
      Classical.choose_spec (HM.ρ_surj _), Z4.red_lift])

theorem redL_spec (f : M' →ₗ[ZMod 4] N') (m : M') : redL HM HN f (ρM m) = ρN (f m) :=
  redL_indep HM HN f (Classical.choose_spec (HM.ρ_surj _))

include hπ in
theorem redL_mem {d : ℤ} {f : M' →ₗ[ZMod 4] N'} (hf : f ∈ homD' MM' NN' d) :
    redL HM HN f ∈ homD MM NN d := by
  refine ⟨fun m b ↦ ?_, fun p m hm ↦ ?_⟩
  · obtain ⟨m', rfl⟩ := HM.ρ_surj m
    obtain ⟨b', rfl⟩ := hπ.surj b
    rw [← HM.act, redL_spec, redL_spec, hf.1, HN.act]
  · obtain ⟨m', hm', rfl⟩ := HM.lift p m hm
    rw [redL_spec]
    exact HN.deg _ _ (hf.2 p m' hm')

/-- **The reduction `H̃_d → H_d`.** -/
def redHom (d : ℤ) : homD' MM' NN' d →+ homD MM NN d where
  toFun f := ⟨redL HM HN f, redL_mem hπ HM HN f.2⟩
  map_zero' := by
    apply Subtype.ext; ext m
    obtain ⟨m', rfl⟩ := HM.ρ_surj m
    simp [redL_spec]
  map_add' f g := by
    apply Subtype.ext; ext m
    obtain ⟨m', rfl⟩ := HM.ρ_surj m
    simp [redL_spec]

theorem redHom_apply (d : ℤ) (f : homD' MM' NN' d) (m : M') :
    (redHom hπ HM HN d f : M →ₗ[𝔽₂] N) (ρM m) = ρN ((f : M' →ₗ[ZMod 4] N') m) :=
  redL_spec HM HN _ m

theorem redHom_smul (d : ℤ) (a : ZMod 4) (f : homD' MM' NN' d) :
    redHom hπ HM HN d (a • f) = Z4.red a • redHom hπ HM HN d f := by
  apply Subtype.ext; ext m
  obtain ⟨m', rfl⟩ := HM.ρ_surj m
  change (redHom hπ HM HN d (a • f) : M →ₗ[𝔽₂] N) (ρM m') = _
  rw [redHom_apply]
  change ρN (a • (f : M' →ₗ[ZMod 4] N') m') = Z4.red a • (redHom hπ HM HN d f : M →ₗ[𝔽₂] N) (ρM m')
  rw [redHom_apply, HN.smul]

/-- **`2f = 0` forces `red f = 0`.** -/
theorem redHom_of_two (d : ℤ) (f : homD' MM' NN' d) (h : (2 : ZMod 4) • f = 0) :
    redHom hπ HM HN d f = 0 := by
  apply Subtype.ext; ext m
  obtain ⟨m', rfl⟩ := HM.ρ_surj m
  change (redHom hπ HM HN d f : M →ₗ[𝔽₂] N) (ρM m') = 0
  rw [redHom_apply]
  apply HN.ann
  have := congrArg (fun g : homD' MM' NN' d ↦ (g : M' →ₗ[ZMod 4] N') m') h
  simpa using this

/-- **Surjectivity of the reduction** in a degree where maps lift. -/
theorem redHom_surjective {d : ℤ}
    (hlift : ∀ f ∈ homD MM NN d, ∃ f' ∈ homD' MM' NN' d, ∀ m, ρN (f' m) = f (ρM m)) :
    Function.Surjective (redHom hπ HM HN d) := by
  intro f
  obtain ⟨f', hf', hρ⟩ := hlift f f.2
  refine ⟨⟨f', hf'⟩, Subtype.ext ?_⟩
  ext m
  obtain ⟨m', rfl⟩ := HM.ρ_surj m
  change (redHom hπ HM HN d ⟨f', hf'⟩ : M →ₗ[𝔽₂] N) (ρM m') = _
  rw [redHom_apply]
  exact hρ m'

/-- **The kernel of the reduction is `2H̃_d`.** -/
theorem ker_redHom {d : ℤ}
    (hlift : ∀ f ∈ homD MM NN d, ∃ f' ∈ homD' MM' NN' d, ∀ m, ρN (f' m) = f (ρM m))
    (f : homD' MM' NN' d) (h : redHom hπ HM HN d f = 0) :
    ∃ g, f = (2 : ZMod 4) • g := by
  set F : M' →ₗ[ZMod 4] N' := (f : M' →ₗ[ZMod 4] N') with hFdef
  have hF0 : ∀ m, ρN (F m) = 0 := fun m ↦ by
    have := congrArg (fun g : homD MM NN d ↦ (g : M →ₗ[𝔽₂] N) (ρM m)) h
    change (redHom hπ HM HN d f : M →ₗ[𝔽₂] N) (ρM m) = (0 : homD MM NN d).1 (ρM m) at this
    rw [redHom_apply] at this
    exact this
  -- `φ = half ∘ F`, well defined on `M`
  have hind : ∀ {m₁ m₂ : M'}, ρM m₁ = ρM m₂ → HN.half (F m₁) = HN.half (F m₂) := by
    intro m₁ m₂ hm
    obtain ⟨x, hx⟩ := HM.ker (m₁ - m₂) (by rw [map_sub, hm, sub_self])
    have : F m₁ = F m₂ + (2 : ZMod 4) • F x := by
      rw [← map_smul, ← hx, ← map_add, add_sub_cancel]
    rw [this, HN.half_add (hF0 _) (HN.ρ_two_smul _), HN.half_two_smul, hF0, add_zero]
  let φ : M →ₗ[𝔽₂] N :=
    { toFun := fun m ↦ HN.half (F (Classical.choose (HM.ρ_surj m)))
      map_add' := fun m n ↦ by
        rw [← HN.half_add (hF0 _) (hF0 _), ← map_add]
        exact hind (by rw [map_add, Classical.choose_spec (HM.ρ_surj _),
          Classical.choose_spec (HM.ρ_surj _), Classical.choose_spec (HM.ρ_surj _)])
      map_smul' := fun c m ↦ by
        rw [RingHom.id_apply, ← Z4.red_lift c, ← HN.half_smul _ (hF0 _), ← map_smul]
        exact hind (by rw [HM.smul, Classical.choose_spec (HM.ρ_surj _),
          Classical.choose_spec (HM.ρ_surj _), Z4.red_lift]) }
  have hφ : ∀ m, φ (ρM m) = HN.half (F m) := fun m ↦ hind (Classical.choose_spec (HM.ρ_surj _))
  have hφmem : φ ∈ homD MM NN d := by
    refine ⟨fun m b ↦ ?_, fun p m hm ↦ ?_⟩
    · obtain ⟨m', rfl⟩ := HM.ρ_surj m
      obtain ⟨b', rfl⟩ := hπ.surj b
      rw [← HM.act, hφ, hφ, f.2.1, HN.half_act (hF0 _)]
    · obtain ⟨m', hm', rfl⟩ := HM.lift p m hm
      rw [hφ]
      exact HN.half_deg (f.2.2 p m' hm') (hF0 _)
  obtain ⟨g, hg, hgρ⟩ := hlift φ hφmem
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  ext m
  change F m = (2 : ZMod 4) • g m
  rw [← HN.tw_half (hF0 m), ← hφ, ← hgρ, HN.tw_ρ]

/-- **Proposition 10.1(1)** for one pair of lifts and one degree: if maps of degree `d` lift,
then `H̃_d` is free over `ℤ/4` on lifts of a basis of `H_d`, and the reduction `H̃_d → H_d` is
surjective with kernel `2H̃_d` (so `H̃_d/2H̃_d = H_d`). -/
theorem homFree {d : ℤ} [FiniteDimensional 𝔽₂ (homD MM NN d)]
    (hlift : ∀ f ∈ homD MM NN d, ∃ f' ∈ homD' MM' NN' d, ∀ m, ρN (f' m) = f (ρM m)) :
    (∃ b : Module.Basis (Fin (Module.finrank 𝔽₂ (homD MM NN d))) (ZMod 4) (homD' MM' NN' d),
      ∀ i, redHom hπ HM HN d (b i) = Module.finBasis 𝔽₂ (homD MM NN d) i) ∧
    Function.Surjective (redHom hπ HM HN d) ∧
    ∀ f, redHom hπ HM HN d f = 0 ↔ ∃ g, f = (2 : ZMod 4) • g := by
  refine ⟨free_of_red _ (redHom hπ HM HN d) (redHom_smul hπ HM HN d) (redHom_surjective hπ HM HN hlift)
    (ker_redHom hπ HM HN hlift) (redHom_of_two hπ HM HN d), redHom_surjective hπ HM HN hlift,
    fun f ↦ ⟨ker_redHom hπ HM HN hlift f, ?_⟩⟩
  rintro ⟨g, rfl⟩
  rw [redHom_smul, show Z4.red 2 = 0 by decide, zero_smul]

end Hom

end WLift

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]
  {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} (T : TabIso D P)

/-- **Maps of degree `d > −2` between the evaluated modules lift** to the lifts (`Ext¹`
vanishing, eq. prime-field-ext-vanishing). -/
theorem homD_lift (J : InjData D) (h1 : DegOne D) (N : ∀ X, ModLift T X) (X Y : V) {d : ℤ}
    (hd : -2 < d) :
    ∀ f ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d,
      ∃ f' ∈ homD' (N X).MM (N Y).MM d, ∀ m, ρF (N Y).β (f' m) = f (ρF (N X).β m) := by
  intro f hf
  have hExt : ExtVanish (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) 0 d :=
    extVanish_ev D (hfin2 (c := c)) J h1 0 X Y d (Or.inr (by push_cast; omega))
  obtain ⟨f', hact, hred, hdeg⟩ := exists_liftHom (isRed_πO T) (N X).lift (N Y).lift f hf.1 hExt
    (linLift (N X).β (N Y).β f) (ρF_linLift _ _ _) fun p m hm ↦ by
      rw [(N X).gr] at hm
      rw [(N Y).gr]
      exact linLift_isHom (MM := gmodEv D (hfin2 (c := c)) X) (NN := gmodEv D (hfin2 (c := c)) Y)
        (N X).β (N Y).β (N X).dβ (N Y).dβ (N X).hβ (N Y).hβ f hf.2 hm
  exact ⟨f', ⟨hact, hdeg⟩, hred⟩

/-- **Proposition 10.1(1)** (`prop:fixed-integral-companion`(1)): the graded Hom modules of
`E₄` (the lifts `M̃_X` of the modules of `C⁽²⁾`) are free over `𝒪 = ℤ/4` in every degree
`d > −2`, and reduction identifies `E₄/2E₄` with the graded Hom spaces of the modules of
`C⁽²⁾`, which are those of `C⁽²⁾` by the evaluation of Proposition 2.10. -/
theorem integralHomFree (J : InjData D) (h1 : DegOne D) (N : ∀ X, ModLift T X) (X Y : V) {d : ℤ}
    (hd : -2 < d) :
    (∃ b : Module.Basis (Fin (Module.finrank 𝔽₂ (homD (gmodEv D (hfin2 (c := c)) X)
        (gmodEv D (hfin2 (c := c)) Y) d))) (ZMod 4) (homD' (N X).MM (N Y).MM d),
      ∀ i, redHom (isRed_πO T) (N X).lift (N Y).lift d (b i) = Module.finBasis 𝔽₂ _ i) ∧
    Function.Surjective (redHom (isRed_πO T) (N X).lift (N Y).lift d) ∧
    ∀ f, redHom (isRed_πO T) (N X).lift (N Y).lift d f = 0 ↔ ∃ g, f = (2 : ZMod 4) • g :=
  homFree (isRed_πO T) (N X).lift (N Y).lift (homD_lift T J h1 N X Y hd)

end MeshWalk

end MultiplicativeBasisDeformations
