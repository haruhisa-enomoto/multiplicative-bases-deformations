import MultiplicativeBasisDeformations.Foundations.IntegralPsi
import MultiplicativeBasisDeformations.Foundations.IntegralHom
import MultiplicativeBasisDeformations.Foundations.ProjectiveEvaluation

/-!
# Proposition 10.1(1) in all degrees and 10.1(3): the presentation of `E₄`

`prop:fixed-integral-companion` (`integral-deformations.tex:46–60`): (1) the Hom modules of
`E₄` are free over `𝒪` and `E₄/2E₄ = C⁽²⁾`; "the same two reductions exclude negative-degree Hom
spaces"; (3) "`E₄` has a quadratic scalar mesh presentation with unit coefficients reducing to
the all-one presentation of `C⁽²⁾`".

* Evaluation over `𝔽₂` is full (`rs_surj`, from Proposition 2.10's `evMap_surjective`) and faithful
  (`rs_inj`); a graded map of degree `d` is the evaluation of a morphism of degree `d`, and there
  are none in negative degrees (`exists_rs_of_homD`, `homD_eq_bot_of_neg`).
* The graded Hom modules of the lifts vanish in negative degrees (`homD'_eq_bot_of_neg`), so
  (1) holds in every degree (`integralHomFree_all`).
* Path evaluation `𝒪Q → E₄` along the lifted arrows (`evO`) is onto the graded maps of every
  degree, by length-homogeneous path combinations (`evO_surj`), and its kernel is exactly the
  ideal of the unit mesh relations (`evO_eq_zero_iff`): this is the presentation (3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt WLift PathEval

attribute [local instance] Classical.decEq

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients 𝔽₂ Q}
  {L : LocalFamily (k := 𝔽₂) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional 𝔽₂ (meshFam Q c x ⟶ meshFam Q c y)]

/-! ### Evaluation over `𝔽₂` is full -/

/-- **Evaluation is full** (Proposition 2.10): every `A⁽²⁾`-linear map between evaluated
modules is the evaluation of a morphism. -/
theorem rs_surj {X Y : V} (g : Rep D.F0 (meshFam Q c X) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c Y))
    (hg : ∀ m b, g ((gmodEv D (hfin2 (c := c)) X).act m b) =
      (gmodEv D (hfin2 (c := c)) Y).act (g m) b) :
    ∃ f : obj c X ⟶ obj c Y, rs D f = g := by
  classical
  let G : D.EZ (fun _ : Unit ↦ X) →ₗ[Alg D.F0] D.EZ (fun _ : Unit ↦ Y) :=
    { toFun := fun m _ ↦ g (m ())
      map_add' := fun m m' ↦ by funext j; exact map_add g (m ()) (m' ())
      map_smul' := fun a m ↦ by funext j; exact hg (m ()) (MulOpposite.op a) }
  obtain ⟨f, hf⟩ := D.evMap_surjective G
  refine ⟨f () (), LinearMap.ext fun x ↦ ?_⟩
  have h := congrFun (LinearMap.congr_fun hf (fun _ ↦ x)) ()
  simpa [MeshData.evMap, G] using h

/-- **Graded maps are evaluations of morphisms of the same degree**: a graded map of degree `d`
is `rs f` with all length components of `f` other than `d` zero. -/
theorem exists_rs_of_homD {X Y : V} {d : ℤ} {g : Rep D.F0 (meshFam Q c X) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c Y)}
    (hg : g ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d) :
    ∃ f : obj c X ⟶ obj c Y, rs D f = g ∧ ∀ s : ℕ, (s : ℤ) ≠ d → degProj c s X Y f = 0 := by
  obtain ⟨f, hf⟩ := rs_surj g hg.1
  obtain ⟨N, hN⟩ := exists_degreePart_eq_bot c (hfin2 (c := c))
  refine ⟨f, hf, fun s hs ↦ ?_⟩
  by_cases hsN : N ≤ s
  · have := degProj_mem c s f
    rw [hN s X Y hsN, Submodule.mem_bot] at this
    exact this
  push Not at hsN
  -- `rs` of the degree-`s` component kills homogeneous elements
  have hhom : ∀ p (m : Rep D.F0 (meshFam Q c X)), (zgrEv D (hfin2 (c := c)) X).IsHom p m →
      rs D (degProj c s X Y f) m = 0 := by
    intro p m hm
    have e1 : (zgrEv D (hfin2 (c := c)) Y).proj (p + s) (g m) = 0 := by
      rw [(zgrEv D (hfin2 (c := c)) Y).proj_of_isHom (hg.2 p m hm), if_neg (by omega)]
    rw [← hf, eq_sum_degProj c hN f, rs_sum, LinearMap.sum_apply, map_sum,
      Finset.sum_eq_single s] at e1
    · rwa [(zgrEv D (hfin2 (c := c)) Y).proj_of_isHom (rs_deg (D := D) (hfin := hfin2 (c := c))
        (degProj_mem c s f) hm), if_pos rfl] at e1
    · intro s' _ hs'
      rw [(zgrEv D (hfin2 (c := c)) Y).proj_of_isHom (rs_deg (D := D) (hfin := hfin2 (c := c))
        (degProj_mem c s' f) hm), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 hsN) h
  have hz : rs D (degProj c s X Y f) = rs D 0 := by
    rw [rs_zero]
    refine LinearMap.ext fun m ↦ ?_
    rw [(zgrEv D (hfin2 (c := c)) X).sum m, map_sum, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun p _ ↦ hhom p _ ((zgrEv D (hfin2 (c := c)) X).isHom_proj p m)
  exact rs_inj hz

/-- **No graded maps of negative degree** between evaluated modules. -/
theorem homD_eq_bot_of_neg {X Y : V} {d : ℤ} (hd : d < 0) :
    homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d = ⊥ := by
  refine eq_bot_iff.2 fun g hg ↦ (Submodule.mem_bot _).2 ?_
  obtain ⟨f, hf, h0⟩ := exists_rs_of_homD hg
  obtain ⟨N, hN⟩ := exists_degreePart_eq_bot c (hfin2 (c := c))
  have : f = 0 := by
    rw [eq_sum_degProj c hN f]
    exact Finset.sum_eq_zero fun s _ ↦ h0 s (by omega)
  rw [← hf, this, rs_zero]

/-- **A graded map of degree `d ≥ 0` is `rs` of a morphism of degree `d`.** -/
theorem exists_rs_degreePart {X Y : V} {d : ℕ}
    {g : Rep D.F0 (meshFam Q c X) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c Y)}
    (hg : g ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d) :
    ∃ f ∈ degreePart c d X Y, rs D f = g := by
  obtain ⟨f, hf, h0⟩ := exists_rs_of_homD hg
  obtain ⟨N, hN⟩ := exists_degreePart_eq_bot c (hfin2 (c := c))
  refine ⟨degProj c d X Y f, degProj_mem c d f, ?_⟩
  rw [← hf]
  congr 1
  conv_rhs => rw [eq_sum_degProj c hN f]
  by_cases hdN : d < N
  · rw [Finset.sum_eq_single d (fun s _ hs ↦ h0 s (by exact_mod_cast hs))
      (fun h ↦ absurd (Finset.mem_range.2 hdN) h)]
  · have := degProj_mem c d f
    rw [hN d X Y (by omega), Submodule.mem_bot] at this
    rw [this]
    exact (Finset.sum_eq_zero fun s hs ↦ h0 s (by
      have := Finset.mem_range.1 hs; omega)).symm

/-- **`C⁽²⁾` is the graded Hom category of its evaluated modules** (Proposition 2.10, graded):
the graded maps of degree `n` are exactly the evaluations of the morphisms of degree `n`, and
evaluation is injective (`rs_inj`). -/
theorem mem_homD_iff {X Y : V} {n : ℕ}
    (g : Rep D.F0 (meshFam Q c X) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c Y)) :
    g ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) n ↔
      ∃ f ∈ degreePart c n X Y, rs D f = g := by
  refine ⟨exists_rs_degreePart, ?_⟩
  rintro ⟨f, hf, rfl⟩
  exact ⟨fun m b ↦ rs_act (hfin := hfin2 (c := c)) f m b,
    fun p m hm ↦ rs_deg (D := D) (hfin := hfin2 (c := c)) hf hm⟩

/-! ### The lifts: negative degrees and the presentation -/

section Lifts

variable {R : Type} [Fintype R] [DecidableEq R] {P : RaySys.Mult D.PV R} (T : TabIso D P)

/-- **The graded Hom modules of the lifts vanish in negative degrees** ("the same two reductions
exclude negative-degree Hom spaces"). -/
theorem homD'_eq_bot_of_neg (N : ∀ X, ModLift T X) {X Y : V} {d : ℤ} (hd : d < 0) :
    homD' (N X).MM (N Y).MM d = ⊥ := by
  have hlift : ∀ f ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d,
      ∃ f' ∈ homD' (N X).MM (N Y).MM d, ∀ m, ρF (N Y).β (f' m) = f (ρF (N X).β m) := by
    intro f hf
    rw [homD_eq_bot_of_neg hd, Submodule.mem_bot] at hf
    exact ⟨0, zero_mem _, fun m ↦ by simp [hf]⟩
  have hred0 : ∀ f, redHom (isRed_πO T) (N X).lift (N Y).lift d f = 0 := fun f ↦ by
    exact Subtype.ext ((Submodule.eq_bot_iff _).1 (homD_eq_bot_of_neg hd) _
      (redHom (isRed_πO T) (N X).lift (N Y).lift d f).2)
  refine eq_bot_iff.2 fun f hf ↦ (Submodule.mem_bot _).2 ?_
  obtain ⟨g, hg⟩ := ker_redHom (isRed_πO T) (N X).lift (N Y).lift hlift ⟨f, hf⟩ (hred0 _)
  obtain ⟨g', hg'⟩ := ker_redHom (isRed_πO T) (N X).lift (N Y).lift hlift g (hred0 _)
  have : (⟨f, hf⟩ : homD' (N X).MM (N Y).MM d) = 0 := by
    rw [hg, hg', smul_smul, Z4.four_eq_zero, zero_smul]
  exact congrArg Subtype.val this

/-- Graded maps lift in every degree: by `Ext¹`-vanishing for `d > −2`, trivially below. -/
theorem homD_lift_all (J : InjData D) (h1 : DegOne D) (N : ∀ X, ModLift T X) (X Y : V) (d : ℤ) :
    ∀ f ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) d,
      ∃ f' ∈ homD' (N X).MM (N Y).MM d, ∀ m, ρF (N Y).β (f' m) = f (ρF (N X).β m) := by
  by_cases hd : -2 < d
  · exact homD_lift T J h1 N X Y hd
  · intro f hf
    rw [homD_eq_bot_of_neg (by omega), Submodule.mem_bot] at hf
    exact ⟨0, zero_mem _, fun m ↦ by simp [hf]⟩

/-- **Proposition 10.1(1) in every degree**: the graded Hom modules of `E₄` are free over `𝒪` on
lifts of a basis of the graded Hom spaces over `𝔽₂`, and reduction is onto with kernel `2·`
(both sides vanish in negative degrees). -/
theorem integralHomFree_all (J : InjData D) (h1 : DegOne D) (N : ∀ X, ModLift T X) (X Y : V)
    (d : ℤ) :
    (∃ b : Module.Basis (Fin (Module.finrank 𝔽₂ (homD (gmodEv D (hfin2 (c := c)) X)
        (gmodEv D (hfin2 (c := c)) Y) d))) (ZMod 4) (homD' (N X).MM (N Y).MM d),
      ∀ i, redHom (isRed_πO T) (N X).lift (N Y).lift d (b i) = Module.finBasis 𝔽₂ _ i) ∧
    Function.Surjective (redHom (isRed_πO T) (N X).lift (N Y).lift d) ∧
    ∀ f, redHom (isRed_πO T) (N X).lift (N Y).lift d f = 0 ↔ ∃ g, f = (2 : ZMod 4) • g :=
  homFree (isRed_πO T) (N X).lift (N Y).lift (homD_lift_all T J h1 N X Y d)

variable (W : WData T)

theorem evP_isHom {Y X : V} (p : Quiver.Path Y X) {p₀ : ℤ} {m : NW W Y}
    (hm : (W.N Y).MM.gr.IsHom p₀ m) : (W.N X).MM.gr.IsHom (p₀ + p.length) (evP (NW W) W.φ p m) := by
  induction p with
  | nil => rw [evP_nil, Quiver.Path.length_nil, Nat.cast_zero, add_zero]; exact hm
  | cons p a ih =>
      rw [evP_cons, LinearMap.comp_apply, Quiver.Path.length_cons, Nat.cast_succ, ← add_assoc]
      exact W.φ_deg a _ _ ih

/-- **Path combinations of length `n` evaluate to graded maps of degree `n`.** -/
theorem evO_mem_homD' {Y X : V} {n : ℕ}
    {F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X}
    (hF : F ∈ LinearPaths.degreePart (k := ZMod 4) n Y X) :
    evO W F ∈ homD' (W.N Y).MM (W.N X).MM n := by
  refine ⟨fun m b ↦ evO_act W F m b, ?_⟩
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨p, hp, rfl⟩ := hF
      intro p₀ m hm
      rw [evL_path, ← hp]
      exact evP_isHom T W p hm
  | zero => intro p₀ m _; rw [map_zero, LinearMap.zero_apply]; exact (W.N X).MM.gr.isHom_zero _
  | add F G _ _ hF hG =>
      intro p₀ m hm
      rw [map_add, LinearMap.add_apply]
      exact (W.N X).MM.gr.isHom_add (hF p₀ m hm) (hG p₀ m hm)
  | smul a F _ hF =>
      intro p₀ m hm
      rw [map_smul, LinearMap.smul_apply]
      exact (W.N X).MM.gr.isHom_smul a (hF p₀ m hm)

variable (J : InjData D) (h1 : DegOne D)

include J h1 in
theorem evO_surj_step {Y X : V} {n : ℕ} {f : NW W Y →ₗ[ZMod 4] NW W X}
    (hf : f ∈ homD' (W.N Y).MM (W.N X).MM n) :
    ∃ F ∈ LinearPaths.degreePart (k := ZMod 4) n Y X, ∃ g : homD' (W.N Y).MM (W.N X).MM n,
      f = evO W F + (2 : ZMod 4) • (g : NW W Y →ₗ[ZMod 4] NW W X) := by
  set gb := redHom (isRed_πO T) (W.N Y).lift (W.N X).lift n ⟨f, hf⟩
  obtain ⟨φ, hφ, hφg⟩ := exists_rs_degreePart (d := n) gb.2
  obtain ⟨Ψ, hΨ, rfl⟩ := hφ
  obtain ⟨Φ, hΦ, hΦΨ⟩ := LinearPaths.exists_lift Z4.red_surjective hΨ
  have hmem : f - evO W Φ ∈ homD' (W.N Y).MM (W.N X).MM n := sub_mem hf (evO_mem_homD' T W hΦ)
  have h0 : redHom (isRed_πO T) (W.N Y).lift (W.N X).lift n ⟨f - evO W Φ, hmem⟩ = 0 := by
    apply Subtype.ext
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨m', rfl⟩ := (W.N Y).lift.ρ_surj m
    change (redHom (isRed_πO T) (W.N Y).lift (W.N X).lift n ⟨f - evO W Φ, hmem⟩ :
      Rep D.F0 (meshFam Q c Y) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c X)) (ρF (W.N Y).β m') = 0
    rw [redHom_apply]
    change ρW W X (f m' - evO W Φ m') = 0
    rw [map_sub, ρW_evO, hΦΨ]
    have := redHom_apply (isRed_πO T) (W.N Y).lift (W.N X).lift (n : ℤ) ⟨f, hf⟩ m'
    change (gb : Rep D.F0 (meshFam Q c Y) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c X)) (ρW W Y m') =
      ρW W X (f m') at this
    rw [← this, ← hφg]
    exact sub_self _
  obtain ⟨g, hg⟩ := ker_redHom (isRed_πO T) (W.N Y).lift (W.N X).lift
    (homD_lift T J h1 W.N Y X (by omega)) _ h0
  refine ⟨Φ, hΦ, g, ?_⟩
  have hv : f - evO W Φ = (2 : ZMod 4) • (g : NW W Y →ₗ[ZMod 4] NW W X) := congrArg Subtype.val hg
  rw [← hv, add_sub_cancel]

include J h1 in
/-- **`E₄` is generated by the lifted arrows**: every graded map of degree `n` between the lifts
is the evaluation of a path combination of length `n`. -/
theorem evO_surj {Y X : V} {n : ℕ} {f : NW W Y →ₗ[ZMod 4] NW W X}
    (hf : f ∈ homD' (W.N Y).MM (W.N X).MM n) :
    ∃ F ∈ LinearPaths.degreePart (k := ZMod 4) n Y X, evO W F = f := by
  obtain ⟨F, hF, g, rfl⟩ := evO_surj_step T W J h1 hf
  obtain ⟨F', hF', g', hg'⟩ := evO_surj_step T W J h1 g.2
  refine ⟨F + (2 : ZMod 4) • F', add_mem hF (Submodule.smul_mem _ _ hF'), ?_⟩
  rw [hg', map_add, map_smul, smul_add, smul_smul, Z4.four_eq_zero, zero_smul, add_zero]

variable {u : MeshCoefficients (ZMod 4) Q}
  (hmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
    ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0)
  (hred : ∀ x y a, Z4.red (u x y a : ZMod 4) = (c x y a : 𝔽₂))

include hred in
theorem evO_inj_step {Y X : V} {F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X}
    (hF : ∀ m, ρW W X (evO W F m) = 0) :
    ∃ G ∈ (CategoricalIdeal.HomIdeal.linearSpan (ZMod 4) (meshRelations u)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X), ∃ H, F = G + (2 : ZMod 4) • H := by
  have h1 : rs D (imgk (c := c) (LinearPaths.redP Z4.red F)) = rs D 0 := by
    rw [rs_zero]
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨m', rfl⟩ := (W.N Y).lift.ρ_surj m
    rw [← ρW_evO, hF, LinearMap.zero_apply]
  have h2 : imgk (c := c) (LinearPaths.redP Z4.red F) = 0 := rs_inj h1
  rw [imgk, RelationCategory.functor_map_eq_zero_iff] at h2
  obtain ⟨G, hG, hGF⟩ := exists_lift_ideal hred Z4.red_surjective h2
  obtain ⟨H, hH⟩ := eq_two_smul_of_redP (Φ := F - G) (by rw [map_sub, hGF, sub_self])
  exact ⟨G, hG, H, by rw [← hH, add_sub_cancel]⟩

include hmesh hred in
/-- **The kernel of path evaluation is the ideal of the unit mesh relations**: together with
`evO_surj`, `E₄` is presented by the quadratic mesh relations with coefficients `u`. -/
theorem evO_eq_zero_iff {Y X : V}
    (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X) :
    evO W F = 0 ↔ F ∈ (CategoricalIdeal.HomIdeal.linearSpan (ZMod 4) (meshRelations u)).hom
      (LinearPaths.obj Y) (LinearPaths.obj X) := by
  refine ⟨fun hF0 ↦ ?_, fun hF ↦ evL_ideal hmesh hF⟩
  obtain ⟨G, hG, H, rfl⟩ := evO_inj_step T W hred (F := F) (fun m ↦ by rw [hF0]; simp)
  have hG0 : evO W G = 0 := evL_ideal hmesh hG
  have hH : ∀ m, ρW W X (evO W H m) = 0 := fun m ↦ by
    refine (W.N X).lift.ann _ ?_
    have := LinearMap.congr_fun hF0 m
    rw [map_add, map_smul, hG0, zero_add, LinearMap.smul_apply] at this
    exact this
  obtain ⟨G', hG', H', rfl⟩ := evO_inj_step T W hred hH
  rw [smul_add, smul_smul, Z4.four_eq_zero, zero_smul, add_zero, two_smul]
  exact add_mem hG (add_mem hG' hG')

omit hmesh hred in
/-- **The statement of Proposition 10.1** (`prop:fixed-integral-companion`) for the table `T`:
the modules `M_X⁽²⁾` lift to graded `𝒪P`-modules free over `𝒪` with degree-one arrow lifts
(`WData`), and their graded Hom category `E₄` satisfies
(1) its Hom modules are free over `𝒪` in every degree, with `E₄/2E₄` the graded Homs of the
    modules of `C⁽²⁾`, which are the morphisms of `C⁽²⁾` of the same degree;
(2) at projective labels the lifts are `ẽ_s𝒪P`, through the generator `w_s`;
(3) `E₄` is presented by the quadratic mesh relations with unit coefficients `u` reducing to the
    all-one coefficients `c`: path evaluation is onto every graded Hom module (by paths of the
    same length) and its kernel is the ideal of the `u`-mesh relations. -/
def Prop101Stmt : Prop :=
  ∃ W : WData T,
    (∀ (X Y : V) (d : ℤ),
      (∃ b : Module.Basis (Fin (Module.finrank 𝔽₂ (homD (gmodEv D (hfin2 (c := c)) X)
          (gmodEv D (hfin2 (c := c)) Y) d))) (ZMod 4) (homD' (W.N X).MM (W.N Y).MM d),
        ∀ i, redHom (isRed_πO T) (W.N X).lift (W.N Y).lift d (b i) = Module.finBasis 𝔽₂ _ i) ∧
      Function.Surjective (redHom (isRed_πO T) (W.N X).lift (W.N Y).lift d) ∧
      ∀ f, redHom (isRed_πO T) (W.N X).lift (W.N Y).lift d f = 0 ↔ ∃ g, f = (2 : ZMod 4) • g) ∧
    (∀ (X Y : V) (n : ℕ) (g : Rep D.F0 (meshFam Q c X) →ₗ[𝔽₂] Rep D.F0 (meshFam Q c Y)),
      g ∈ homD (gmodEv D (hfin2 (c := c)) X) (gmodEv D (hfin2 (c := c)) Y) n ↔
        ∃ f ∈ degreePart c n X Y, rs D f = g) ∧
    (∀ (X Y : V) (d : ℤ), d < 0 → homD' (W.N X).MM (W.N Y).MM d = ⊥) ∧
    (∀ s : D.PV, (∀ n : NW W s.1, ∃ b, (W.N s.1).MM.act (wO W s) b = n) ∧
      ∀ b, eO P s * b = b → (W.N s.1).MM.act (wO W s) b = 0 → b = 0) ∧
    ∃ u : MeshCoefficients (ZMod 4) Q, (∀ x y a, Z4.red (u x y a : ZMod 4) = c x y a) ∧
      (∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
        ((u x a.1 a.2 : (ZMod 4)ˣ) : ZMod 4) • (W.φ a.2 ∘ₗ W.φ (Q.mate x a.1 a.2)) = 0) ∧
      (∀ (Y X : V) (n : ℕ) (f : NW W Y →ₗ[ZMod 4] NW W X),
        f ∈ homD' (W.N Y).MM (W.N X).MM n →
          ∃ F ∈ LinearPaths.degreePart (k := ZMod 4) n Y X, evO W F = f) ∧
      ∀ (Y X : V) (F : LinearPaths.obj (k := ZMod 4) Y ⟶ LinearPaths.obj (k := ZMod 4) X),
        evO W F = 0 ↔ F ∈ (CategoricalIdeal.HomIdeal.linearSpan (ZMod 4) (meshRelations u)).hom
          (LinearPaths.obj Y) (LinearPaths.obj X)

omit hmesh hred in
include J h1 in
/-- **Proposition 10.1** (`prop:fixed-integral-companion`), for any ray table of `A⁽²⁾`. -/
theorem prop101 : Prop101Stmt T := by
  obtain ⟨W⟩ := exists_wData (T := T) J h1
  obtain ⟨u, hred, hmesh⟩ := exists_meshUnits W
  refine ⟨W, fun X Y d ↦ integralHomFree_all T J h1 W.N X Y d, fun X Y n g ↦ mem_homD_iff g,
    fun X Y d hd ↦ homD'_eq_bot_of_neg T W.N hd, fun s ↦ ⟨fun n ↦ ?_, fun b hb h0 ↦ ?_⟩,
    u, hred, hmesh, fun Y X n f hf ↦ evO_surj T W J h1 hf,
    fun Y X F ↦ evO_eq_zero_iff T W hmesh hred F⟩
  · exact exists_act_wG (isRed_πO T) (W.N s.1).lift (eO P s) (unit (F := D.F0) s)
      (ψP D (hfin2 (c := c)) s) (hψ1 s) (hψ2 (T := T) s) n
  · exact eq_zero_of_act_wG (isRed_πO T) (W.N s.1).lift (eO P s) (eO_idem s) (unit (F := D.F0) s)
      (ψP D (hfin2 (c := c)) s) (hψ1 s) (hψ2 (T := T) s) hb h0

end Lifts

end MeshWalk

end MultiplicativeBasisDeformations
