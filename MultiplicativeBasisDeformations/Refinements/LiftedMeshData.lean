module

public import MultiplicativeBasisDeformations.Refinements.LiftedCategory

/-!
# Mesh data of the lifted modules (toward Corollary 12.1)

The lifted mesh sequences `0 → M_{τx}^B → ⊕_a M_{y_a}^B → M_x^B → 0` are exact sequences of
right `B`-modules (`LiftedMesh.lean`); applying `Hom_B(M_w^B, −)` and `Hom_B(−, M_w^B)` gives the
exactness required of a `MeshData` on the lifted modules (`meshB`), with the radical of
`localB` (filtration order at least one).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  {hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {B : Type u} [Ring B] [Algebra k B] {P : PosFiltration (lenA0 D hfin) B}
  (Ls : Lifts D hfin P) (J : D.InjData) (h1 : DegOne D) (Vx : LenGrading.Vertices (lenA0 D hfin))

/-- The chosen lifted kernel at a nonprojective label. -/
def kd (x : V) (hx : ¬ D.proj x) : KerData Ls J h1 Vx x hx :=
  (nonempty_kerData Ls J h1 Vx x hx).some

/-- The lifted arrow map as a morphism of right `B`-modules. -/
def pB (x : V) (a : D.Mid x) : FB Ls (D.mid x a) ⟶ FB Ls x :=
  ofLin Ls (pL Ls J h1 Vx x a) (pL_act Ls J h1 Vx x a)

/-- The components of the lifted kernel as morphisms. -/
def qB (x : V) (hx : ¬ D.proj x) (a : D.Mid x) : FB Ls (D.tau x hx) ⟶ FB Ls (D.mid x a) :=
  ofLin Ls (LinearMap.proj a ∘ₗ (kd Ls J h1 Vx x hx).q) fun m b ↦ by
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, (kd Ls J h1 Vx x hx).act]
    rfl

/-- The components of a family of maps into the middle term, as one map. -/
def joinIn {w x : V} (g : ∀ a : D.Mid x, FB Ls w ⟶ FB Ls (D.mid x a)) :
    Rep D.F0 (meshFam Q c w) →ₗ[k] Emid D x :=
  LinearMap.pi fun a ↦ toLin (g a)

theorem πB_joinIn {w x : V} (g : ∀ a : D.Mid x, FB Ls w ⟶ FB Ls (D.mid x a)) :
    πB Ls J h1 Vx x ∘ₗ joinIn Ls g = toLin (∑ a, g a ≫ pB Ls J h1 Vx x a) := by
  refine LinearMap.ext fun m ↦ ?_
  simp [πB, joinIn, toLin_sum, pB]

theorem joinIn_act {w x : V} (g : ∀ a : D.Mid x, FB Ls w ⟶ FB Ls (D.mid x a)) (m) (b : B) :
    joinIn Ls g ((Ls.L w).act m b) = (LE Ls x).act (joinIn Ls g m) b := by
  funext a
  exact toLin_act (g a) m b

/-- A family of maps out of the middle term, as one map. -/
def joinOut {w x : V} (v : ∀ a : D.Mid x, FB Ls (D.mid x a) ⟶ FB Ls w) :
    Emid D x →ₗ[k] Rep D.F0 (meshFam Q c w) :=
  ∑ a, toLin (v a) ∘ₗ LinearMap.proj a

theorem joinOut_act {w x : V} (v : ∀ a : D.Mid x, FB Ls (D.mid x a) ⟶ FB Ls w) (e : Emid D x)
    (b : B) : joinOut Ls v ((LE Ls x).act e b) = (Ls.L w).act (joinOut Ls v e) b := by
  simp only [joinOut, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact toLin_act (v a) (e a) b

variable (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)

include hrad in
/-- **The mesh data of the lifted modules.** -/
def meshB : MeshData (FB Ls) (localB Ls Vx) where
  Mid := D.Mid
  fin := D.fin
  decMid := D.decMid
  mid := D.mid
  p := pB Ls J h1 Vx
  p_rad x a := pL_order Ls J h1 Vx x a
  image x w f hf := by
    obtain ⟨g, hg, hfg⟩ := exists_factor_πB Ls J h1 Vx hrad w x (toLin f) (toLin_act f) hf
    refine ⟨fun a ↦ ofLin Ls (g a) (hg a), toLin_injective ?_⟩
    rw [toLin_sum, hfg]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [toLin_comp]; rfl
  proj := D.proj
  decProj := D.decProj
  tau := D.tau
  q := qB Ls J h1 Vx
  comp_zero x hx := by
    apply toLin_injective
    rw [toLin_sum, toLin_zero]
    have h0 : πB Ls J h1 Vx x ∘ₗ (kd Ls J h1 Vx x hx).q = 0 := by
      refine LinearMap.ext fun m ↦ ?_
      have := (kd Ls J h1 Vx x hx).range ▸ LinearMap.mem_range_self (kd Ls J h1 Vx x hx).q m
      exact this
    rw [← h0]
    refine LinearMap.ext fun m ↦ ?_
    simp [πB, qB, pB]
  cov_exact x hx w g hg := by
    set K := kd Ls J h1 Vx x hx
    have hG : ∀ m, joinIn Ls g m ∈ LinearMap.range K.q := by
      intro m
      rw [K.range, LinearMap.mem_ker, ← LinearMap.comp_apply, πB_joinIn, hg, toLin_zero,
        LinearMap.zero_apply]
    set e := LinearEquiv.ofInjective K.q K.inj
    let z₀ : Rep D.F0 (meshFam Q c w) →ₗ[k] Rep D.F0 (meshFam Q c (D.tau x hx)) :=
      e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range K.q) (joinIn Ls g) hG
    have hz₀ : ∀ m, K.q (z₀ m) = joinIn Ls g m := by
      intro m
      have := e.apply_symm_apply ⟨joinIn Ls g m, hG m⟩
      exact congrArg Subtype.val this
    have hz₀act : ∀ m b, z₀ ((Ls.L w).act m b) = (Ls.L _).act (z₀ m) b := by
      intro m b
      apply K.inj
      rw [hz₀, K.act, hz₀, joinIn_act]
    refine ⟨ofLin Ls z₀ hz₀act, fun a ↦ toLin_injective ?_⟩
    refine LinearMap.ext fun m ↦ ?_
    change toLin (g a) m = (K.q (z₀ m)) a
    rw [hz₀]
    rfl
  cov_mono x hx w z hz := by
    set K := kd Ls J h1 Vx x hx
    apply toLin_injective
    refine LinearMap.ext fun m ↦ ?_
    apply K.inj
    rw [toLin_zero, LinearMap.zero_apply, map_zero]
    funext a
    have := congrArg (fun f ↦ toLin f m) (hz a)
    simpa [qB] using this
  contra_exact x hx w v hv := by
    set K := kd Ls J h1 Vx x hx
    have hVq : joinOut Ls v ∘ₗ K.q = 0 := by
      have := congrArg toLin hv
      rw [toLin_sum, toLin_zero] at this
      refine LinearMap.ext fun m ↦ ?_
      have hm := LinearMap.congr_fun this m
      simpa [joinOut, qB] using hm
    obtain ⟨s, hs⟩ := (πB Ls J h1 Vx x).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (πB_surjective Ls J h1 Vx x hx))
    set u₀ := joinOut Ls v ∘ₗ s
    have hu₀π : u₀ ∘ₗ πB Ls J h1 Vx x = joinOut Ls v := by
      refine LinearMap.ext fun e ↦ ?_
      have hmem : s (πB Ls J h1 Vx x e) - e ∈ LinearMap.ker (πB Ls J h1 Vx x) := by
        rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
      rw [← K.range] at hmem
      obtain ⟨r, hr⟩ := hmem
      have h0 : joinOut Ls v (s (πB Ls J h1 Vx x e) - e) = 0 := by
        rw [← hr, ← LinearMap.comp_apply, hVq, LinearMap.zero_apply]
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hu₀act : ∀ m b, u₀ ((Ls.L x).act m b) = (Ls.L w).act (u₀ m) b := by
      intro m b
      obtain ⟨e, rfl⟩ := πB_surjective Ls J h1 Vx x hx m
      rw [← πB_act, ← LinearMap.comp_apply u₀, hu₀π, joinOut_act, ← LinearMap.comp_apply u₀, hu₀π]
    refine ⟨ofLin Ls u₀ hu₀act, fun a ↦ toLin_injective ?_⟩
    refine LinearMap.ext fun m ↦ ?_
    rw [toLin_comp, toLin_ofLin, LinearMap.comp_apply]
    change toLin (v a) m = u₀ (pL Ls J h1 Vx x a m)
    have := LinearMap.congr_fun hu₀π (Pi.single a m)
    rw [LinearMap.comp_apply] at this
    simp only [πB, joinOut, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at this
    rw [Finset.sum_eq_single a, Finset.sum_eq_single a] at this
    · simpa using this.symm
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · simp
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · simp
  contra_mono x hx w u hu := by
    apply toLin_injective
    refine LinearMap.ext fun m ↦ ?_
    obtain ⟨e, rfl⟩ := πB_surjective Ls J h1 Vx x hx m
    rw [toLin_zero, LinearMap.zero_apply]
    simp only [πB, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    have := congrArg (fun f ↦ toLin f (e a)) (hu a)
    simpa [pB] using this
  proj_mono x hx w g hg a := by
    apply toLin_injective
    have h0 : joinIn Ls g = 0 := by
      refine LinearMap.ext fun m ↦ ?_
      apply πB_injective Ls J h1 Vx x hx
      rw [← LinearMap.comp_apply, πB_joinIn, hg, toLin_zero, LinearMap.zero_apply,
        LinearMap.zero_apply, map_zero]
    refine LinearMap.ext fun m ↦ ?_
    rw [toLin_zero, LinearMap.zero_apply]
    exact congrFun (LinearMap.congr_fun h0 m) a

/-! ### Dimensions of the lifted Hom spaces -/

include Vx in
/-- The leading term of a map of order `r` is a morphism of `C` of degree `r`. -/
theorem exists_lead {X Y : V} (r : ℕ) (f : FB Ls X ⟶ FB Ls Y)
    (hf : OrderGe (gmodEv D hfin X) (gmodEv D hfin Y) r (toLin f)) :
    ∃ φ : obj c X ⟶ obj c Y, φ ∈ degreePart c r X Y ∧
      ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f) = rs D φ := by
  have hℓ : ∀ m a, ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f)
      (evAct D X m a) = evAct D Y (ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r
        (toLin f) m) a :=
    fun m a ↦ fLift_leading Vx (Ls.L X) (Ls.L Y) (toLin f) (toLin_act f) hf m a
  obtain ⟨φ, hφ⟩ := exists_repMap D _ hℓ
  refine ⟨φ, mem_degreePart_of_repMap D hfin fun p m hm ↦ ?_, hφ⟩
  rw [← hφ]
  exact ZGr.comp_isHom _ _ (toLin f) hm

variable (X Y : V)

/-- The filtration of the lifted Hom space by order. -/
def filB (r : ℕ) : Submodule k (FB Ls X ⟶ FB Ls Y) where
  carrier := {f | OrderGe (gmodEv D hfin X) (gmodEv D hfin Y) r (toLin f)}
  add_mem' {f g} hf hg := by
    change OrderGe _ _ _ (toLin (f + g)); rw [toLin_add]; exact hf.add hg
  zero_mem' := by change OrderGe _ _ _ (toLin 0); rw [toLin_zero]; exact OrderGe.zero _
  smul_mem' t f hf := by
    change OrderGe _ _ _ (toLin (t • f)); rw [toLin_smul]; exact hf.smul t

include J h1 Vx in
theorem finrank_filB_step (r : ℕ) :
    Module.finrank k (filB Ls X Y r) =
      Module.finrank k (filB Ls X Y (r + 1)) + Module.finrank k (degreePart c r X Y) := by
  classical
  -- the leading-term map
  set θ : filB Ls X Y r →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y)) :=
    { toFun := fun f ↦ ZGr.comp (gmodEv D hfin X).gr (gmodEv D hfin Y).gr r (toLin f.1)
      map_add' := fun f g ↦ by simp only [Submodule.coe_add, toLin_add, comp_add']
      map_smul' := fun t f ↦ by simp only [Submodule.coe_smul, toLin_smul, comp_smul]; rfl }
  set ρ : degreePart c r X Y →ₗ[k] (Rep D.F0 (meshFam Q c X) →ₗ[k] Rep D.F0 (meshFam Q c Y)) :=
    { toFun := fun φ ↦ rs D φ.1
      map_add' := fun φ ψ ↦ by simp only [Submodule.coe_add, rs_add]
      map_smul' := fun t φ ↦ by simp only [Submodule.coe_smul, rs_smul]; rfl }
  have hρ : Function.Injective ρ := fun φ ψ h ↦ Subtype.ext (rs_inj (D := D) h)
  have hrange : LinearMap.range θ = LinearMap.range ρ := by
    apply le_antisymm
    · rintro _ ⟨f, rfl⟩
      obtain ⟨φ, hφ, he⟩ := exists_lead Ls Vx r f.1 f.2
      exact ⟨⟨φ, hφ⟩, he.symm⟩
    · rintro _ ⟨φ, rfl⟩
      obtain ⟨g, hg, hord, hlead⟩ := fLift_map Vx (Ls.L X) (Ls.L Y) r (rs D φ.1) (rs_act φ.1)
        (fun p m hm ↦ repMap_isHom hfin φ.2 hm)
        (fun t _ ↦ extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))
      exact ⟨⟨ofLin Ls g hg, hord⟩, hlead⟩
  have hker : Module.finrank k (LinearMap.ker θ) = Module.finrank k (filB Ls X Y (r + 1)) := by
    have hle : filB Ls X Y (r + 1) ≤ filB Ls X Y r := fun f hf ↦ by
      change OrderGe _ _ _ _; exact OrderGe.mono hf (by push_cast; omega)
    have heq : LinearMap.ker θ = Submodule.comap (filB Ls X Y r).subtype (filB Ls X Y (r + 1)) := by
      ext f
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker]
      have := (fLift_gr_hom Vx (Ls.L X) (Ls.L Y) r (fun t _ ↦
        extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))).1 (toLin f.1) f.2
      constructor
      · intro hf
        change OrderGe _ _ _ _
        exact_mod_cast this.1 hf
      · intro hf
        change OrderGe _ _ _ _ at hf
        exact this.2 (by exact_mod_cast hf)
    exact ((LinearEquiv.ofEq _ _ heq).trans (Submodule.comapSubtypeEquivOfLe hle)).finrank_eq
  have h1' := LinearMap.finrank_range_add_finrank_ker θ
  rw [hrange, LinearMap.finrank_range_of_inj hρ, hker] at h1'
  omega

include J h1 Vx in
theorem finrank_FB_eq_sum (R : ℕ)
    (hR : (degBound (gmodEv D hfin X).gr : ℤ) + degBound (gmodEv D hfin Y).gr < R) :
    Module.finrank k (FB Ls X ⟶ FB Ls Y) =
      ∑ r ∈ Finset.range R, Module.finrank k (degreePart c r X Y) := by
  have h0 : filB Ls X Y 0 = ⊤ := eq_top_iff.2 fun f _ ↦ order0 Vx f
  have hbot : filB Ls X Y R = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    apply toLin_injective
    rw [toLin_zero]
    exact orderGe_eq_zero_of_large hf hR
  have key : ∀ n, Module.finrank k (filB Ls X Y 0) =
      Module.finrank k (filB Ls X Y n) + ∑ r ∈ Finset.range n, Module.finrank k (degreePart c r X Y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, finrank_filB_step Ls J h1 Vx X Y n, Finset.sum_range_succ]; ring
  rw [← finrank_top k (FB Ls X ⟶ FB Ls Y), ← h0, key R, hbot, finrank_bot, zero_add]

include hfin in
theorem finrank_C_eq_sum (R : ℕ) (hR : Nb hfin ≤ R) :
    Module.finrank k (obj c X ⟶ obj c Y) =
      ∑ r ∈ Finset.range R, Module.finrank k (degreePart c r X Y) := by
  classical
  let e : (obj c X ⟶ obj c Y) ≃ₗ[k] ((r : Fin R) → degreePart c r X Y) :=
    { toFun := fun f r ↦ ⟨degProj c r X Y f, degProj_mem c r f⟩
      map_add' := fun f g ↦ funext fun r ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun t f ↦ funext fun r ↦ Subtype.ext (map_smul _ _ _)
      invFun := fun φ ↦ ∑ r, (φ r : obj c X ⟶ obj c Y)
      left_inv := fun f ↦ by
        simp only
        rw [← Finset.sum_range (fun d ↦ degProj c d X Y f)]
        conv_rhs => rw [eq_sum_degProj c (Nb_spec hfin) f]
        rw [← Finset.sum_range_add_sum_Ico _ hR, Finset.sum_eq_zero (s := Finset.Ico _ _)
          fun d hd ↦ by
            have := degProj_mem c d f
            rwa [Nb_spec hfin d X Y (Finset.mem_Ico.1 hd).1, Submodule.mem_bot] at this,
          add_zero]
      right_inv := fun φ ↦ funext fun r ↦ Subtype.ext (by
        simp only [map_sum]
        rw [Finset.sum_eq_single r]
        · rw [degProj_of_mem c (φ r).2, if_pos rfl]
        · intro s _ hs
          rw [degProj_of_mem c (φ s).2, if_neg (fun h ↦ hs (Fin.ext h))]
        · simp) }
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_range]

include J h1 Vx in
/-- **The lifted Hom spaces have the dimensions of `C`.** -/
theorem finrank_FB : Module.finrank k (FB Ls X ⟶ FB Ls Y) =
    Module.finrank k (meshFam Q c X ⟶ meshFam Q c Y) := by
  set R := max (Nb hfin) (degBound (gmodEv D hfin X).gr + degBound (gmodEv D hfin Y).gr + 1)
  rw [finrank_FB_eq_sum Ls J h1 Vx X Y R (by push_cast; omega)]
  exact (finrank_C_eq_sum (hfin := hfin) X Y R (le_max_left _ _)).symm

end MeshWalk

end MultiplicativeBasisDeformations
