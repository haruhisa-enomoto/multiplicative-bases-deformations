import MultiplicativeBasisDeformations.Refinements.LiftTransport
import MultiplicativeBasisDeformations.Refinements.CocycleLift

/-!
# Lifted mesh sequences over a positive deformation (toward Corollary 12.1)

`deformation-refinements.tex` (`cor:positive-deformation-completeness`). Let `B` be a
positive filtered deformation of `A₀` and `M_X^B` the filtered lifts of the evaluated modules
(Proposition 6.5). Lifting the mesh maps gives, at a nonprojective `x`, a surjection
`π : ⊕_a M_{y_a}^B → M_x^B` whose leading term is the graded mesh map, with kernel the image of
an injective `B`-linear map `M_{τx}^B → ⊕_a M_{y_a}^B` (the kernel is a filtered lift of
`M_{τx}`, by uniqueness of lifts); at a projective `x`, `π` is injective. These are the lifted
almost split sequences of `ind(mod B)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {B : Type u} [Ring B] [Algebra k B] (P : PosFiltration (lenA0 D hfin) B)

/-- **Filtered lifts of all evaluated modules** (Proposition 6.5(1)). -/
structure Lifts where
  L : ∀ X : V, FLift P (one_isHom D hfin) (gmodEv D hfin X)

section Basic

variable (J : D.InjData) (h1 : DegOne D) (Vx : LenGrading.Vertices (lenA0 D hfin))

include hfd J h1 Vx in
theorem nonempty_lifts : Nonempty (Lifts D hfin P) :=
  ⟨⟨fun X ↦ (PosFiltration.exists_fLift Vx fun t _ ↦
    extVanish_ev D hfin J h1 1 X X t (Or.inr (by push_cast; omega))).some⟩⟩

end Basic

variable {D hfin P}
variable (Ls : Lifts D hfin P) (J : D.InjData) (h1 : DegOne D)
  (Vx : LenGrading.Vertices (lenA0 D hfin))

/-! ### The lifted mesh maps -/

theorem rs_act {X Y : V} (f : obj c X ⟶ obj c Y) (m : Rep D.F0 (meshFam Q c X))
    (a : (Alg D.F0)ᵐᵒᵖ) :
    rs D f ((gmodEv D hfin X).act m a) = (gmodEv D hfin Y).act (rs D f m) a :=
  (repMap (F := D.F0) f).map_smul a.unop m

include J h1 Vx in
theorem exists_pLift (x : V) (a : D.Mid x) :
    ∃ g : Rep D.F0 (meshFam Q c (D.mid x a)) →ₗ[k] Rep D.F0 (meshFam Q c x),
      (∀ m b, g ((Ls.L _).act m b) = (Ls.L x).act (g m) b) ∧
      OrderGe (gmodEv D hfin _) (gmodEv D hfin x) 1 g ∧
      ZGr.comp (gmodEv D hfin _).gr (gmodEv D hfin x).gr 1 g = rs D (D.p x a) := by
  obtain ⟨g, hg, hord, hlead⟩ := fLift_map Vx (Ls.L (D.mid x a)) (Ls.L x) 1 (rs D (D.p x a))
    (rs_act (D.p x a)) (fun p m hm ↦ repMap_isHom hfin (h1.p x a) hm)
    (fun t _ ↦ extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))
  exact ⟨g, hg, by exact_mod_cast hord, by exact_mod_cast hlead⟩

/-- **The lifted arrow maps** `p̃_a : M_{y_a}^B → M_x^B`. -/
def pL (x : V) (a : D.Mid x) :
    Rep D.F0 (meshFam Q c (D.mid x a)) →ₗ[k] Rep D.F0 (meshFam Q c x) :=
  (exists_pLift Ls J h1 Vx x a).choose

theorem pL_act (x : V) (a : D.Mid x) (m) (b : B) :
    pL Ls J h1 Vx x a ((Ls.L _).act m b) = (Ls.L x).act (pL Ls J h1 Vx x a m) b :=
  (exists_pLift Ls J h1 Vx x a).choose_spec.1 m b

theorem pL_order (x : V) (a : D.Mid x) :
    OrderGe (gmodEv D hfin _) (gmodEv D hfin x) 1 (pL Ls J h1 Vx x a) :=
  (exists_pLift Ls J h1 Vx x a).choose_spec.2.1

theorem pL_lead (x : V) (a : D.Mid x) :
    ZGr.comp (gmodEv D hfin _).gr (gmodEv D hfin x).gr 1 (pL Ls J h1 Vx x a) = rs D (D.p x a) :=
  (exists_pLift Ls J h1 Vx x a).choose_spec.2.2

/-- The lift on the middle term `⊕_a M_{y_a}⟨1⟩`. -/
def LE (x : V) : FLift P (one_isHom D hfin) (gE D hfin x) :=
  FLift.pi (fun a ↦ Ls.L (D.mid x a)) (fun _ ↦ 1)

/-- **The lifted mesh map** `π = Σ_a p̃_a : ⊕_a M_{y_a}^B → M_x^B`. -/
def πB (x : V) : Emid D x →ₗ[k] Rep D.F0 (meshFam Q c x) :=
  ∑ a, pL Ls J h1 Vx x a ∘ₗ LinearMap.proj a

theorem πB_act (x : V) (m : Emid D x) (b : B) :
    πB Ls J h1 Vx x ((LE Ls x).act m b) = (Ls.L x).act (πB Ls J h1 Vx x m) b := by
  simp only [πB, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  exact pL_act Ls J h1 Vx x a (m a) b

theorem πB_order (x : V) : OrderGe (gE D hfin x) (gmodEv D hfin x) 0 (πB Ls J h1 Vx x) := by
  intro p m hm e he
  have hm' := (ZGr.piShift_isHom _ _ _ _).1 hm
  simp only [πB, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  exact pL_order Ls J h1 Vx x a (p - 1) (m a) (hm' a) e (by omega)

theorem πB_lead (x : V) :
    ZGr.comp (gE D hfin x).gr (gmodEv D hfin x).gr 0 (πB Ls J h1 Vx x) =
      (πE D x).restrictScalars k := by
  refine (gE D hfin x).gr.ext_of_hom fun p m hm ↦ ?_
  have hm' := (ZGr.piShift_isHom _ _ _ _).1 hm
  rw [ZGr.comp_hom _ _ _ hm]
  simp only [πB, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum,
    LinearMap.coe_restrictScalars, πE]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have := congrArg (fun f ↦ f (m a)) (pL_lead Ls J h1 Vx x a)
  simp only [ZGr.comp_hom _ _ _ (hm' a)] at this
  rw [show p - 1 + 1 = p + 0 by ring] at this
  exact this

/-! ### Exactness of the lifted mesh sequences -/

include hfd in
/-- **The graded mesh map is onto** at a nonprojective label. -/
theorem πE_surjective (x : V) (hx : ¬ D.proj x) : Function.Surjective (πE D x) := by
  intro m
  have hrad : ∀ y : D.PV, m y ∈ L.rad y.1 x :=
    fun y ↦ L.mem_of_ne (fun (h : y.1 = x) ↦ hx (h ▸ y.2)) (m y)
  choose g hg using fun y : D.PV ↦ D.image x y.1 (m y) (hrad y)
  refine ⟨fun a ↦ (show Rep D.F0 (meshFam Q c (D.mid x a)) from fun y ↦ g y a), ?_⟩
  ext y
  rw [πE_apply]
  exact (hg y).symm

theorem πB_surjective (x : V) (hx : ¬ D.proj x) : Function.Surjective (πB Ls J h1 Vx x) :=
  surjective_of_lead (πB_order Ls J h1 Vx x)
    (by rw [πB_lead]; exact πE_surjective (D := D) x hx)

theorem πB_injective (x : V) (hx : D.proj x) : Function.Injective (πB Ls J h1 Vx x) :=
  injective_of_lead (πB_order Ls J h1 Vx x)
    (by rw [πB_lead]; exact πE_injective (D := D) x hx)

include hfd in
/-- The graded dimension count `dim M_{τx} + dim M_x = dim ⊕_a M_{y_a}`. -/
theorem finrank_graded (x : V) (hx : ¬ D.proj x) :
    Module.finrank k (Rep D.F0 (meshFam Q c (D.tau x hx))) + Module.finrank k
      (Rep D.F0 (meshFam Q c x)) = Module.finrank k (Emid D x) := by
  set πk := (πE D x).restrictScalars k
  set ιk := (ιτ D x hx).restrictScalars k
  have hrange : LinearMap.range ιk = LinearMap.ker πk := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact πE_ιτ (D := D) x hx m
    · intro m hm
      obtain ⟨r, hr⟩ := exact_E (D := D) x hx hm
      exact ⟨r, hr⟩
  have h1' := LinearMap.finrank_range_of_inj (f := ιk) (ιτ_injective (D := D) x hx)
  have h2 := LinearMap.finrank_range_add_finrank_ker πk
  have hsurj : LinearMap.range πk = ⊤ :=
    LinearMap.range_eq_top.2 (πE_surjective (D := D) x hx)
  rw [hsurj, finrank_top] at h2
  rw [← h1', hrange]
  omega

/-- **The lifted kernel**: `M_{τx}^B` as the kernel of the lifted mesh map. -/
structure KerData (x : V) (hx : ¬ D.proj x) where
  q : Rep D.F0 (meshFam Q c (D.tau x hx)) →ₗ[k] Emid D x
  act : ∀ m b, q ((Ls.L _).act m b) = (LE Ls x).act (q m) b
  inj : Function.Injective q
  range : LinearMap.range q = LinearMap.ker (πB Ls J h1 Vx x)

include hfd in
theorem nonempty_kerData (x : V) (hx : ¬ D.proj x) : Nonempty (KerData Ls J h1 Vx x hx) := by
  classical
  set ι₁ := (ιτ D x hx).restrictScalars k
  obtain ⟨ι, hπι, hord, hlead⟩ := exists_kernel_lift (UU := gE D hfin x) (NN := gmodEv D hfin x)
    (MM := gmodEv D hfin (D.tau x hx)) (r := 0) (r' := 2) (πB_order Ls J h1 Vx x)
    (by rw [πB_lead]; exact πE_surjective (D := D) x hx) (ι₁ := ι₁)
    (fun p m hm ↦ ιτ_isHom (D := D) hfin h1 x hx p m hm)
    (by rw [πB_lead]; ext m : 1; exact πE_ιτ (D := D) x hx m)
  have hinj : Function.Injective (ZGr.comp (gmodEv D hfin (D.tau x hx)).gr (gE D hfin x).gr 2 ι) := by
    rw [hlead]; exact ιτ_injective (D := D) x hx
  have hι := injective_of_lead hord hinj
  have hrange : LinearMap.range ι = LinearMap.ker (πB Ls J h1 Vx x) := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨m, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hπι, LinearMap.zero_apply]
    · have h1' := LinearMap.finrank_range_of_inj hι
      have h2 := LinearMap.finrank_range_add_finrank_ker (πB Ls J h1 Vx x)
      rw [LinearMap.range_eq_top.2 (πB_surjective Ls J h1 Vx x hx), finrank_top] at h2
      have h3 := finrank_graded (D := D) x hx
      rw [h1']
      omega
  have hstab : ∀ m b, (LE Ls x).act (ι m) b ∈ LinearMap.range ι := by
    intro m b
    have h0 : πB Ls J h1 Vx x (ι m) = 0 := by
      rw [← LinearMap.comp_apply, hπι, LinearMap.zero_apply]
    rw [hrange, LinearMap.mem_ker, πB_act, h0, map_zero, LinearMap.zero_apply]
  have hlin : ∀ m a, ZGr.comp (gmodEv D hfin (D.tau x hx)).gr (gE D hfin x).gr 2 ι
      ((gmodEv D hfin (D.tau x hx)).act m a) =
      (gE D hfin x).act (ZGr.comp (gmodEv D hfin (D.tau x hx)).gr (gE D hfin x).gr 2 ι m) a := by
    intro m a
    rw [hlead]
    exact (ιτ D x hx).map_smul a.unop m
  set tr := FLift.transport (LE Ls x) ι hι hstab hord hlin hinj
  obtain ⟨Φ, hΦ, -⟩ := fLift_unique Vx (fun t _ ↦
    extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega))) (Ls.L (D.tau x hx)) tr
  refine ⟨⟨ι ∘ₗ Φ.toLinearMap, fun m b ↦ ?_, hι.comp Φ.injective, ?_⟩⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hΦ]
    exact FLift.transport_act (LE Ls x) ι hι hstab hord hlin hinj (Φ m) b
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, hrange]

/-! ### Radical maps factor through the lifted arrows -/

theorem orderGe_eq_zero_of_large {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k N] {MM : GMod (galgA0 D hfin) M} {NN : GMod (galgA0 D hfin) N} {r : ℤ}
    {g : M →ₗ[k] N} (hg : OrderGe MM NN r g)
    (hr : (degBound MM.gr : ℤ) + degBound NN.gr < r) : g = 0 := by
  refine MM.gr.ext_of_hom fun p m hm ↦ ?_
  by_cases hp : p ∈ MM.gr.supp
  · rw [LinearMap.zero_apply]
    have h1 := le_degBound hp
    rw [abs_le] at h1
    exact NN.gr.eq_zero_of_geAt (fun e he ↦ hg p m hm e he) (by omega)
  · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

include hfin in
theorem degProj_comp_right' {p r : ℕ} {x y z : V} (f : obj c x ⟶ obj c y) {h : obj c y ⟶ obj c z}
    (hh : h ∈ degreePart c p y z) : degProj c (r + p) x z (f ≫ h) = degProj c r x y f ≫ h := by
  classical
  conv_lhs => rw [eq_sum_degProj c (Nb_spec hfin) f, Preadditive.sum_comp, map_sum]
  rw [Finset.sum_eq_single r]
  · rw [degProj_of_mem c (comp_mem_degreePart' c (degProj_mem c r f) hh), if_pos rfl]
  · intro e _ he
    rw [degProj_of_mem c (comp_mem_degreePart' c (degProj_mem c e f) hh), if_neg (by omega)]
  · intro hr
    have := degProj_mem c r f
    rw [Nb_spec hfin r x y (by simpa using hr), Submodule.mem_bot] at this
    rw [this, Limits.zero_comp, map_zero]

variable (hrad : ∀ (x y : V) (d : ℕ), 1 ≤ d → ∀ f ∈ degreePart c d x y, f ∈ L.rad x y)

include hrad in
/-- **Radical maps into a lift factor through the lifted arrows** (the lifted form of
`MeshData.image`, by induction along the finite filtration). -/
theorem exists_factor_πB (w x : V) (f : Rep D.F0 (meshFam Q c w) →ₗ[k] Rep D.F0 (meshFam Q c x))
    (hf : ∀ m b, f ((Ls.L w).act m b) = (Ls.L x).act (f m) b)
    (hord : OrderGe (gmodEv D hfin w) (gmodEv D hfin x) 1 f) :
    ∃ g : ∀ a : D.Mid x, Rep D.F0 (meshFam Q c w) →ₗ[k] Rep D.F0 (meshFam Q c (D.mid x a)),
      (∀ a m b, g a ((Ls.L w).act m b) = (Ls.L _).act (g a m) b) ∧
      f = ∑ a, pL Ls J h1 Vx x a ∘ₗ g a := by
  classical
  set T : ℕ := degBound (gmodEv D hfin w).gr + degBound (gmodEv D hfin x).gr + 1
  have key : ∀ K : ℕ, ∀ r : ℕ, 1 ≤ r → T ≤ r + K →
      ∀ f : Rep D.F0 (meshFam Q c w) →ₗ[k] Rep D.F0 (meshFam Q c x),
      (∀ m b, f ((Ls.L w).act m b) = (Ls.L x).act (f m) b) →
      OrderGe (gmodEv D hfin w) (gmodEv D hfin x) r f →
      ∃ g : ∀ a : D.Mid x, Rep D.F0 (meshFam Q c w) →ₗ[k] Rep D.F0 (meshFam Q c (D.mid x a)),
        (∀ a m b, g a ((Ls.L w).act m b) = (Ls.L _).act (g a m) b) ∧
        f = ∑ a, pL Ls J h1 Vx x a ∘ₗ g a := by
    intro K
    induction K with
    | zero =>
      intro r _ hT f _ hord
      refine ⟨fun _ ↦ 0, fun _ _ _ ↦ by simp, ?_⟩
      rw [orderGe_eq_zero_of_large hord (by push_cast; omega)]
      simp
    | succ K ih =>
      intro r hr hT f hf hord
      by_cases hTr : T ≤ r
      · refine ⟨fun _ ↦ 0, fun _ _ _ ↦ by simp, ?_⟩
        rw [orderGe_eq_zero_of_large hord (by push_cast; omega)]
        simp
      -- the leading term is a morphism of `C` of degree `r`
      set ℓ := ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin x).gr r f
      have hℓ : ∀ m a, ℓ (evAct D w m a) = evAct D x (ℓ m) a :=
        fun m a ↦ fLift_leading Vx (Ls.L w) (Ls.L x) f hf hord m a
      obtain ⟨φ, hφ⟩ := exists_repMap D ℓ hℓ
      have hφdeg : φ ∈ degreePart c r w x := mem_degreePart_of_repMap D hfin fun p m hm ↦ by
        rw [← hφ]; exact ZGr.comp_isHom _ _ _ hm
      obtain ⟨h, hh⟩ := D.image x w φ (hrad w x r hr φ hφdeg)
      set h' : ∀ a : D.Mid x, obj c w ⟶ obj c (D.mid x a) := fun a ↦ degProj c (r - 1) _ _ (h a)
      have hh' : φ = ∑ a, h' a ≫ D.p x a := by
        conv_lhs => rw [← (degProj_of_mem c hφdeg).trans (if_pos rfl), hh, map_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        have := degProj_comp_right' (hfin := hfin) (r := r - 1) (h a) (h1.p x a)
        rwa [show r - 1 + 1 = r by omega] at this
      -- lift the factors
      have hlift : ∀ a : D.Mid x, ∃ g : Rep D.F0 (meshFam Q c w) →ₗ[k]
          Rep D.F0 (meshFam Q c (D.mid x a)),
          (∀ m b, g ((Ls.L w).act m b) = (Ls.L _).act (g m) b) ∧
          OrderGe (gmodEv D hfin w) (gmodEv D hfin _) (r - 1 : ℕ) g ∧
          ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin _).gr (r - 1 : ℕ) g = rs D (h' a) := by
        intro a
        exact fLift_map Vx (Ls.L w) (Ls.L (D.mid x a)) (r - 1) (rs D (h' a)) (rs_act (h' a))
          (fun p m hm ↦ repMap_isHom hfin (degProj_mem c _ _) hm)
          (fun t _ ↦ extVanish_ev D hfin J h1 0 _ _ _ (Or.inr (by push_cast; omega)))
      choose ht hthf htord htlead using hlift
      set f' := f - ∑ a, pL Ls J h1 Vx x a ∘ₗ ht a
      have hcomp : ∀ a, OrderGe (gmodEv D hfin w) (gmodEv D hfin x) r
          (pL Ls J h1 Vx x a ∘ₗ ht a) := by
        intro a
        have := (htord a).comp (pL_order Ls J h1 Vx x a)
        rwa [show ((r - 1 : ℕ) : ℤ) + 1 = r by omega] at this
      have hord' : OrderGe (gmodEv D hfin w) (gmodEv D hfin x) (r + 1 : ℕ) f' := by
        have hsum : OrderGe (gmodEv D hfin w) (gmodEv D hfin x) r
            (∑ a, pL Ls J h1 Vx x a ∘ₗ ht a) :=
          Finset.sum_induction _ _ (fun u v hu hv ↦ hu.add hv) (OrderGe.zero _)
            fun a _ ↦ hcomp a
        have hf'r : OrderGe (gmodEv D hfin w) (gmodEv D hfin x) r f' := by
          have := hord.add (hsum.smul (-1))
          rwa [neg_one_smul, ← sub_eq_add_neg] at this
        have h0 : ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin x).gr r f' = 0 := by
          have hcf : ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin x).gr r f = rs D φ := hφ
          simp only [f', comp_sub]
          rw [hcf, hh', rs_sum, sub_eq_zero]
          rw [show ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin x).gr r
              (∑ a, pL Ls J h1 Vx x a ∘ₗ ht a) =
              ∑ a, ZGr.comp (gmodEv D hfin w).gr (gmodEv D hfin x).gr r
                (pL Ls J h1 Vx x a ∘ₗ ht a) from by
            induction (Finset.univ : Finset (D.Mid x)) using Finset.induction_on with
            | empty => simp [comp_zero']
            | insert a s ha ihs => rw [Finset.sum_insert ha, Finset.sum_insert ha, comp_add', ihs]]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          have := comp_comp_lead (htord a) (pL_order Ls J h1 Vx x a)
          rw [show ((r - 1 : ℕ) : ℤ) + 1 = r by omega] at this
          rw [this, pL_lead, htlead, rs_comp]
        have := orderGe_succ hf'r h0
        exact_mod_cast this
      have hf' : ∀ m b, f' ((Ls.L w).act m b) = (Ls.L x).act (f' m) b := by
        intro m b
        simp only [f', LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.comp_apply, hf, hthf,
          pL_act, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply]
      obtain ⟨g', hg', hfg'⟩ := ih (r + 1) (by omega) (by omega) f' hf' hord'
      refine ⟨fun a ↦ ht a + g' a, fun a m b ↦ by simp [hthf, hg'], ?_⟩
      have : f = f' + ∑ a, pL Ls J h1 Vx x a ∘ₗ ht a := by simp [f']
      rw [this, hfg', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [LinearMap.comp_add]; abel
  exact key T 1 le_rfl (by omega) f hf hord

end MeshWalk

end MultiplicativeBasisDeformations
