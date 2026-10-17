import MultiplicativeBasisDeformations.Foundations.ExtResolutions
import MultiplicativeBasisDeformations.Foundations.SquareZeroModules
import MultiplicativeBasisDeformations.Refinements.GeneralLift

/-!
# Proposition 6.5 and Lemma 6.6 with `Ext` from graded projective resolutions

The `Ext` hypotheses of `prop:positive-module-lifting` and `lem:square-zero-selected-lifts` are
stated in the manuscript with `Ext` in its own sense (`positive-deformations.tex`: degree-`t`
maps from a graded projective resolution). Here the Lean statements are given with exactly these
hypotheses, for a chosen graded projective resolution of the source module, through the
comparison `GRes.extVanish_iff`:

* Lemma 6.6 over any commutative ring `R` with `Λ` and the modules projective over `R`
  (`exists_muMod_res`, `muMod_unique_res`, `muMod_mapLift_res`), and in particular over `ℤ/4`
  with `Λ` and the modules free, as in the lemma (`lemma66_Z4`);
* Proposition 6.5 over a field (`exists_genLift_res`, `genLift_unique_res`, `fLift_map_res`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v w

namespace GExt

/-- The graded pieces of a module projective over `R` are projective (they are direct summands). -/
theorem proj_pieces_of_projective {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
    [Module R X] [Module.Projective R X] (g : ZGr (R := R) X) (q : ℤ) :
    Module.Projective R (LinearMap.range (g.proj q)) :=
  Module.Projective.of_split (LinearMap.range (g.proj q)).subtype (g.proj q).rangeRestrict
    (LinearMap.ext fun x ↦ Subtype.ext (by
      obtain ⟨y, hy⟩ := x.2
      change g.proj q (x : X) = x
      rw [← hy, g.proj_proj, if_pos rfl]))

section SquareZero

variable {R : Type v} [CommRing R] {Λ : Type u} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  [Module.Projective R Λ]
  {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Projective R M] [Module.Projective R N]
  {μ : Λ →ₗ[R] Λ →ₗ[R] Λ} {q : ℤ} {MM : GMod GΛ M} {NN : GMod GΛ N}

theorem res_bar (Rs : GRes MM) (XX : GMod GΛ N) (n : ℕ) (t : ℤ) :
    Rs.ExtVanish XX n t ↔ ExtVanish MM XX n t :=
  GRes.extVanish_iff (fun p ↦ proj_pieces_of_projective GΛ.gr p) XX n Rs
    (fun p ↦ proj_pieces_of_projective MM.gr p) t

theorem res_bar_self (Rs : GRes MM) (n : ℕ) (t : ℤ) :
    Rs.ExtVanish MM n t ↔ ExtVanish MM MM n t :=
  GRes.extVanish_iff (fun p ↦ proj_pieces_of_projective GΛ.gr p) MM n Rs
    (fun p ↦ proj_pieces_of_projective MM.gr p) t

/-- **Lemma 6.6, existence**, with `Ext²_Λ(M, M)_q = 0` computed from a graded projective
resolution of `M`. -/
theorem exists_muMod_res (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) (h11 : μ 1 1 = 0)
    (Rs : GRes MM) (h : Rs.ExtVanish MM 1 q) : Nonempty (MuMod μ q MM (M × M)) :=
  exists_muMod hq hμ h11 ((res_bar_self Rs 1 q).1 h)

/-- **Lemma 6.6, uniqueness**, with `Ext¹_Λ(M, M)_q = 0` computed from a graded projective
resolution of `M`. -/
theorem muMod_unique_res (Rs : GRes MM) (h : Rs.ExtVanish MM 0 q)
    {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (X : MuMod μ q MM L) (Y : MuMod μ q MM L') :
    ∃ Φ : L ≃ₗ[R] L', (∀ l a, Φ (X.act l a) = Y.act (Φ l) a) ∧ (∀ l, Φ (X.ε l) = Y.ε (Φ l)) ∧
      (∀ l, Y.red (Φ l) = X.red l) ∧ ∀ p l, X.gr.IsHom p l → Y.gr.IsHom p (Φ l) :=
  muMod_unique (fun p ↦ proj_pieces_of_projective MM.gr p) ((res_bar_self Rs 0 q).1 h) X Y

/-- **Lemma 6.6, maps lift**, with `Ext¹_Λ(M, N)_{r+q} = 0` computed from a graded projective
resolution of `M`. -/
theorem muMod_mapLift_res {r : ℤ} (Rs : GRes MM) (h : Rs.ExtVanish NN 0 (r + q))
    {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (X : MuMod μ q MM L) (Y : MuMod μ q NN L') (f : M →ₗ[R] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfdeg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) :
    ∃ F : L →ₗ[R] L', (∀ l a, F (X.act l a) = Y.act (F l) a) ∧ (∀ l, F (X.ε l) = Y.ε (F l)) ∧
      (∀ l, Y.red (F l) = f (X.red l)) ∧ ∀ p l, X.gr.IsHom p l → Y.gr.IsHom (p + r) (F l) :=
  muMod_mapLift (fun p ↦ proj_pieces_of_projective MM.gr p)
    (fun p ↦ proj_pieces_of_projective NN.gr p) X Y f hf hfdeg ((res_bar Rs NN 0 (r + q)).1 h)

end SquareZero

/-- **Lemma 6.6 over `ℤ/4`**, as stated: `Λ` a graded `ℤ/4`-algebra free over `ℤ/4`, `M`, `N`
graded modules free over `ℤ/4`, `Ext` computed from graded projective resolutions of `M`. Under
`Ext²(M, M)_q = 0` the lift exists, under `Ext¹(M, M)_q = 0` it is unique up to a graded
isomorphism reducing to the identity, and under `Ext¹(M, N)_{r+q} = 0` maps lift. -/
theorem lemma66_Z4 {Λ : Type u} [Ring Λ] [Algebra (ZMod 4) Λ] {GΛ : GAlg (R := ZMod 4) Λ}
    [Module.Free (ZMod 4) Λ] {M N : Type w} [AddCommGroup M] [Module (ZMod 4) M]
    [AddCommGroup N] [Module (ZMod 4) N] [Module.Free (ZMod 4) M] [Module.Free (ZMod 4) N]
    {μ : Λ →ₗ[ZMod 4] Λ →ₗ[ZMod 4] Λ} {q : ℤ} {MM : GMod GΛ M} {NN : GMod GΛ N}
    (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) (h11 : μ 1 1 = 0) (Rs : GRes MM) :
    (Rs.ExtVanish MM 1 q → Nonempty (MuMod μ q MM (M × M))) ∧
    (Rs.ExtVanish MM 0 q → ∀ {L L' : Type w} [AddCommGroup L] [Module (ZMod 4) L]
      [AddCommGroup L'] [Module (ZMod 4) L'] (X : MuMod μ q MM L) (Y : MuMod μ q MM L'),
      ∃ Φ : L ≃ₗ[ZMod 4] L', (∀ l a, Φ (X.act l a) = Y.act (Φ l) a) ∧
        (∀ l, Φ (X.ε l) = Y.ε (Φ l)) ∧ (∀ l, Y.red (Φ l) = X.red l) ∧
        ∀ p l, X.gr.IsHom p l → Y.gr.IsHom p (Φ l)) ∧
    ∀ {r : ℤ}, Rs.ExtVanish NN 0 (r + q) → ∀ {L L' : Type w} [AddCommGroup L]
      [Module (ZMod 4) L] [AddCommGroup L'] [Module (ZMod 4) L'] (X : MuMod μ q MM L)
      (Y : MuMod μ q NN L') (f : M →ₗ[ZMod 4] N), (∀ m a, f (MM.act m a) = NN.act (f m) a) →
      (∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m)) →
      ∃ F : L →ₗ[ZMod 4] L', (∀ l a, F (X.act l a) = Y.act (F l) a) ∧
        (∀ l, F (X.ε l) = Y.ε (F l)) ∧ (∀ l, Y.red (F l) = f (X.red l)) ∧
        ∀ p l, X.gr.IsHom p l → Y.gr.IsHom (p + r) (F l) :=
  ⟨fun h ↦ exists_muMod_res hq hμ h11 Rs h,
   fun h _ _ _ _ _ _ X Y ↦ muMod_unique_res Rs h X Y,
   fun h _ _ _ _ _ _ X Y f hf hfdeg ↦ muMod_mapLift_res Rs h X Y f hf hfdeg⟩

end GExt

namespace PosFiltration

open LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] {P : PosFiltration G B}
  {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {h1 : G.IsHom 0 (1 : Λ)}
  {MM : GExt.GMod (GExt.GAlg.ofLen G h1) M} {NN : GExt.GMod (GExt.GAlg.ofLen G h1) N}

/-- **Proposition 6.5(1), existence**, with `Ext²_Λ(M, M)_t = 0` (`t > 0`) computed from a graded
projective resolution of `M`. -/
theorem exists_genLift_res (hS : Nonempty (Split P)) (Rs : GExt.GRes MM)
    (hExt : ∀ t : ℕ, 0 < t → Rs.ExtVanish MM 1 t) : Nonempty (GenLift P h1 MM M) :=
  exists_genLift hS fun t ht ↦ (GExt.GRes.extVanish_iff_field MM 1 Rs t).1 (hExt t ht)

/-- **Proposition 6.5(1), uniqueness**, with `Ext¹_Λ(M, M)_t = 0` (`t > 0`) computed from a graded
projective resolution of `M`. -/
theorem genLift_unique_res (hS : Nonempty (Split P)) (Rs : GExt.GRes MM)
    (hExt : ∀ t : ℕ, 0 < t → Rs.ExtVanish MM 0 t)
    {L L' : Type*} [AddCommGroup L] [Module k L] [AddCommGroup L'] [Module k L']
    (X : GenLift P h1 MM L) (Y : GenLift P h1 MM L') :
    ∃ Ψ : L ≃ₗ[k] L', (∀ n x, Ψ (X.act n x) = Y.act (Ψ n) x) ∧
      ∀ p n, n ∈ X.F p → Ψ n ∈ Y.F p ∧ Y.ι p (Ψ n) = X.ι p n :=
  genLift_unique hS (fun t ht ↦ (GExt.GRes.extVanish_iff_field MM 0 Rs t).1 (hExt t ht)) X Y

/-- **Proposition 6.5(2), maps lift**, with `Ext¹_Λ(M, N)_{r+t} = 0` (`t > 0`) computed from a
graded projective resolution of `M`. -/
theorem fLift_map_res (hS : Nonempty (Split P)) (Rs : GExt.GRes MM) (A : FLift P h1 MM)
    (A' : FLift P h1 NN) (r : ℕ) (f : M →ₗ[k] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
    (hExt : ∀ t : ℕ, 0 < t → Rs.ExtVanish NN 0 (r + t)) :
    ∃ Φ : M →ₗ[k] N, (∀ m x, Φ (A.act m x) = A'.act (Φ m) x) ∧ GExt.OrderGe MM NN r Φ ∧
      GExt.ZGr.comp MM.gr NN.gr r Φ = f :=
  fLift_map_of_split hS A A' r f hf hfd fun t ht ↦
    (GExt.GRes.extVanish_iff_field NN 0 Rs _).1 (hExt t ht)

end PosFiltration

end MultiplicativeBasisDeformations
