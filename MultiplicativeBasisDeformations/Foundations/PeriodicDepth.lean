module

public import MultiplicativeBasisDeformations.Foundations.PeriodicModel
public import MultiplicativeBasisDeformations.Foundations.ComponentGlue
public import MultiplicativeBasisDeformations.Foundations.MeshComplex

/-!
# The depth function on periodic components

For the proof of Lemma 4.2 (`lem:mesh-walk-free`, `scalar-normalization.tex`):
"A periodic component containing arrows gives a mapping torus, which retracts
onto its core circle." By Proposition 4.1 a periodic component is covered by
`ℤΔ`, and the deck transformations have the form `(v, t) ↦ (ρ v, t + c₀)` for a
tree automorphism `ρ` (`StarDeck.deck_height_form`). "The automorphism `ρ`
fixes a vertex or an edge midpoint of `Δ`" (lines 82–85): we use the centre of
the path for type `A`, and the trivalent vertex for types `D` and `E`. The
(doubled) distance to this centre is invariant under every deck
transformation, so it descends to the component; each vertex has at most one
neighbour at depth at most its own. This depth function drives the
contraction onto the core circle in `MeshComplex.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace StarDepth

variable {t : ℕ} {L : Fin t → ℕ}

/-- The doubled distance from the centre at "half-depth" `n / 2`. -/
def cdep (n : ℕ) (v : StarV L) : ℕ := (2 * starDepth v - n) + (n - 2 * starDepth v)

theorem starAdj_symm {a b : StarV L} (h : starAdj a b) : starAdj b a := (starGraph L).adj_symm h

theorem depth_eq_zero {v : StarV L} (h : starDepth v = 0) : v = none := by
  rcases v with _ | ⟨i, k⟩
  · rfl
  · simp [starDepth] at h

theorem depth_nb (ht : 0 < t) {v : StarV L} (hv : v ≠ none) :
    starDepth (StarDeck.nb ht v) + 1 = starDepth v := by
  rcases v with _ | ⟨i, k⟩
  · exact absurd rfl hv
  · simp only [StarDeck.nb]
    split_ifs with hk
    · simp [starDepth, hk]
    · simp only [starDepth]; omega

/-- An automorphism fixing the centre preserves depth. -/
theorem depth_pres (ht : 0 < t) (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) (h0 : ρ none = none) :
    ∀ n (v : StarV L), starDepth v = n → starDepth (ρ v) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    rcases n with _ | m
    · rw [depth_eq_zero hv, h0]; rfl
    · have hvn : v ≠ none := by rintro rfl; simp [starDepth] at hv
      obtain ⟨p, hpdef⟩ : ∃ p, p = StarDeck.nb ht v := ⟨_, rfl⟩
      have hp : starDepth p = m := by have := depth_nb ht hvn; rw [← hpdef] at this; omega
      have hpv : starAdj (ρ p) (ρ v) :=
        (hρ p v).1 (starAdj_symm (hpdef ▸ StarDeck.adj_nb ht v))
      have hρp := ih m (by omega) p hp
      rcases starAdj_depth hpv with h | h
      · omega
      · exfalso
        have hpn : p ≠ none := by intro he; rw [he] at hp; simp [starDepth] at hp; omega
        obtain ⟨pp, hppdef⟩ : ∃ pp, pp = StarDeck.nb ht p := ⟨_, rfl⟩
        have hpp : starDepth pp + 1 = m := by have := depth_nb ht hpn; rw [← hppdef] at this; omega
        have hρpp := ih (starDepth pp) (by omega) pp rfl
        have hρpn : ρ p ≠ none := by
          intro he; rw [he] at hρp; simp [starDepth] at hρp; omega
        obtain ⟨⟨i, k⟩, hik⟩ := Option.ne_none_iff_exists'.1 hρpn
        have h1 : starAdj (ρ p) (ρ pp) := (hρ p pp).1 (hppdef ▸ StarDeck.adj_nb ht p)
        rw [hik] at h1 hpv
        have := ρ.injective (nbr_of_some h1 hpv (by omega))
        rw [← this] at hv
        omega

/-- On a path, the distance to the middle is invariant under automorphisms. -/
theorem cdep_aut_path {L : Fin 1 → ℕ} (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) (v : StarV L) :
    cdep (L 0 + 1) (ρ v) = cdep (L 0 + 1) v := by
  have h1 := depth_le v
  have h2 := depth_le (ρ v)
  rcases path_aut ρ hρ with h | h
  · rw [cdep, cdep, h v]
  · have := h v
    simp only [cdep]
    omega

/-- With three arms, the depth is invariant under automorphisms. -/
theorem cdep_aut_three {L : Fin 3 → ℕ} (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) (v : StarV L) :
    cdep 0 (ρ v) = cdep 0 v := by
  rw [cdep, cdep, depth_pres (by norm_num) ρ hρ (fixes_centre_three rfl ρ hρ) _ v rfl]

/-- On a path, a vertex has at most one neighbour not farther from the middle. -/
theorem cdep_uniq_path {L : Fin 1 → ℕ} (n : ℕ) {v w w' : StarV L} (hw : starAdj w v)
    (hw' : starAdj w' v) (h : cdep n w ≤ cdep n v) (h' : cdep n w' ≤ cdep n v) : w = w' := by
  apply depth_injective
  have a := starAdj_depth hw
  have b := starAdj_depth hw'
  simp only [cdep] at h h'
  omega

/-- A vertex has at most one neighbour not farther from the centre. -/
theorem cdep_uniq_zero {v w w' : StarV L} (hw : starAdj w v)
    (hw' : starAdj w' v) (h : cdep 0 w ≤ cdep 0 v) (h' : cdep 0 w' ≤ cdep 0 v) : w = w' := by
  have a := starAdj_depth hw
  have b := starAdj_depth hw'
  simp only [cdep] at h h'
  rcases v with _ | ⟨i, k⟩
  · simp only [starDepth] at a b h h'; omega
  · exact nbr_of_some (starAdj_symm hw) (starAdj_symm hw') (by omega)

end StarDepth

namespace PeriodicDepth

open StarDepth

universe u w

variable {W : Type u} [Quiver.{w} W] [∀ x y : W, Subsingleton (x ⟶ y)] {Q : TranslationQuiver W}
  (hQ : Q.IsStable)

/-- A depth function on a stable translation quiver: invariant under `τ`, and
each vertex has at most one in-neighbour of depth at most its own. -/
def IsDepth (e : W → ℕ) : Prop :=
  (∀ x, e (hQ.tauE x) = e x) ∧
    ∀ (x y y' : W) (_ : y ⟶ x) (_ : y' ⟶ x), e y ≤ e x → e y' ≤ e x → y = y'

/-- **The depth function descends from the tree model.** -/
theorem exists_depth_of_model {t : ℕ} (L : Fin t → ℕ) (π : (starTree L).ZVert ⥤q W)
    (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
    (hsurj : Function.Surjective π.obj) (ht : 0 < t) (f : StarV L → ℕ)
    (hf : ∀ ρ : StarV L ≃ StarV L, (∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) → ∀ v, f (ρ v) = f v)
    (hu : ∀ {v w w' : StarV L}, starAdj w v → starAdj w' v → f w ≤ f v → f w' ≤ f v → w = w') :
    ∃ e : W → ℕ, IsDepth hQ e := by
  classical
  have wd : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y → f X.v = f Y.v := by
    intro X Y h
    obtain ⟨z, hz, rfl⟩ := StarDeck.fibre_transitive L hQ π hπ hτ h
    obtain ⟨ρ, hρ, hF⟩ := StarDeck.deck_height_form L hQ π hπ hτ ht z hz
    rw [(hF X).1, hf ρ hρ]
  let lift : W → (starTree L).ZVert := fun x ↦ Classical.choose (hsurj x)
  have hlift : ∀ x, π.obj (lift x) = x := fun x ↦ Classical.choose_spec (hsurj x)
  refine ⟨fun x ↦ f (lift x).v, fun x ↦ ?_, fun x y y' a a' h h' ↦ ?_⟩
  · have : π.obj ((starTree L).ztau (lift x)) = π.obj (lift (hQ.tauE x)) := by
      rw [hτ, hlift, hlift]
    exact (wd _ _ this).symm
  · set X := lift x
    have hX : π.obj X = x := hlift x
    obtain ⟨⟨Y, b⟩, hb⟩ := (hπ.costar_bijective X).2 ⟨y, show y ⟶ π.obj X from hX ▸ a⟩
    obtain ⟨⟨Y', b'⟩, hb'⟩ := (hπ.costar_bijective X).2 ⟨y', show y' ⟶ π.obj X from hX ▸ a'⟩
    have hY : π.obj Y = y := congrArg Sigma.fst hb
    have hY' : π.obj Y' = y' := congrArg Sigma.fst hb'
    have e1 : f Y.v ≤ f X.v := by
      rw [wd Y (lift y) (by rw [hY, hlift])]; exact h
    have e2 : f Y'.v ≤ f X.v := by
      rw [wd Y' (lift y') (by rw [hY', hlift])]; exact h'
    have hv : Y.v = Y'.v := hu b.down.1 b'.down.1 e1 e2
    have hYY : Y = Y' := by
      apply OrientedTree.ZVert.ext hv
      have := b.down.2; have := b'.down.2; omega
    rw [← hY, ← hY', hYY]

/-- **A connected periodic component has a depth function** (Proposition 4.1 and
the choice of a centre of `Δ`). -/
theorem exists_depth [Fintype W] [DecidableEq W] [∀ x y : W, Fintype (x ⟶ y)]
    [∀ x : W, Fintype (Σ y : W, y ⟶ x)] {k : Type*} [Field k] (c : MeshCoefficients k Q)
    (hfin : ∀ x y : W, FiniteDimensional k
      (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))
    (x₀ : W) (hconn : ∀ v, Relation.EqvGen (TranslationQuiver.SecPath.ConnAdj hQ) x₀ v) :
    ∃ e : W → ℕ, IsDepth hQ e := by
  by_cases harrow : ∃ x y : W, Nonempty (x ⟶ y)
  · obtain ⟨x₁, y₁, ⟨a₀⟩⟩ := harrow
    have hconn₁ : ∀ v, Relation.EqvGen (TranslationQuiver.SecPath.ConnAdj hQ) x₁ v :=
      fun v ↦ Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hconn x₁)) (hconn v)
    obtain ⟨t, L, π, hcl, hπ, hτ, hsurj⟩ := TranslationQuiver.periodic_model hQ c hfin a₀ hconn₁
    rcases hcl with rfl | ⟨rfl, -⟩
    · exact exists_depth_of_model hQ L π hπ hτ hsurj (by norm_num) (cdep (L 0 + 1))
        (fun ρ hρ v ↦ cdep_aut_path ρ hρ v) (fun hw hw' h h' ↦ cdep_uniq_path _ hw hw' h h')
    · exact exists_depth_of_model hQ L π hπ hτ hsurj (by norm_num) (cdep 0)
        (fun ρ hρ v ↦ cdep_aut_three ρ hρ v) (fun hw hw' h h' ↦ cdep_uniq_zero hw hw' h h')
  · push Not at harrow
    exact ⟨fun _ ↦ 0, fun _ ↦ rfl, fun x y _ a _ _ _ ↦ (harrow y x).false a |>.elim⟩

end PeriodicDepth

namespace MeshWalk

open TranslationQuiver PeriodicDepth

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V}

theorem cyclic_step {y x : V} {a : y ⟶ x} (h : Cyclic Q ⟨y, x, a⟩) :
    ∃ hx : x ∈ Q.nonprojective, Cyclic Q ⟨(Q.tau ⟨x, hx⟩).1, y, Q.mate ⟨x, hx⟩ y a⟩ := by
  obtain ⟨hx, -⟩ := h 1
  exact ⟨hx, fun n ↦ by obtain ⟨_, hc⟩ := h (n + 1); exact hc⟩

/-- "A mate cycle forces periodic endpoints because `σ² = τ`." -/
theorem tauChain_of_cyclic : ∀ (n : ℕ) (A : Arr V), Cyclic Q A →
    Q.TauChain A.2.1 n ∧ Q.TauChain A.1 n
  | 0, _, _ => ⟨trivial, trivial⟩
  | n + 1, ⟨y, x, a⟩, h => by
      obtain ⟨hx, h1⟩ := cyclic_step h
      obtain ⟨hy, h2⟩ := cyclic_step h1
      have ih := tauChain_of_cyclic n _ h2
      exact ⟨⟨hx, ih.1⟩, ⟨hy, ih.2⟩⟩

theorem periodic_of_cyclic {A : Arr V} (h : Cyclic Q A) :
    A.2.1 ∈ Q.periodic ∧ A.1 ∈ Q.periodic :=
  ⟨fun n ↦ (tauChain_of_cyclic n A h).1, fun n ↦ (tauChain_of_cyclic n A h).2⟩

theorem component_eq {u v : V} (h : Relation.EqvGen Q.PeriodicAdj u v) :
    Q.component u = Q.component v := by
  ext w
  constructor
  · rintro ⟨hw, huw⟩
    exact ⟨hw, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) huw⟩
  · rintro ⟨hw, hvw⟩
    exact ⟨hw, Relation.EqvGen.trans _ _ _ h hvw⟩

variable [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {k : Type*} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k
    (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

include hfin in
theorem exists_depth_component (x : V) (hx : x ∈ Q.periodic) :
    ∃ f : FullSub (Q.component x) → ℕ, IsDepth (restrict_isStable (Q := Q) x) f := by
  classical
  exact exists_depth (restrict_isStable x) (c.restrict (isTauClosed_component x))
    (finiteDimensional_restrict (isTauClosed_component x) c hfin)
    (FullSub.mk x (mem_component_self hx)) (restrict_conn x hx)

open Classical in
/-- The depth on the vertices of a periodic component `S`, through the chosen
model of `S`. -/
def depthOn (S : Set V) (v : V) : ℕ :=
  if h : ∃ x, x ∈ Q.periodic ∧ Q.component x = S then
    if hv : v ∈ Q.component h.choose then
      Classical.choose (exists_depth_component c hfin h.choose h.choose_spec.1)
        (FullSub.mk v hv)
    else 0
  else 0

/-- The glued depth function. -/
def depth (v : V) : ℕ := depthOn c hfin (Q.component v) v

theorem depth_spec (x : V) (hx : x ∈ Q.periodic) :
    ∃ (x₀ : V) (f : FullSub (Q.component x₀) → ℕ),
      IsDepth (restrict_isStable (Q := Q) x₀) f ∧ Q.component x₀ = Q.component x ∧
      ∀ u (hu : u ∈ Q.component x₀), Q.component u = Q.component x →
        depth c hfin u = f (FullSub.mk u hu) := by
  classical
  have h : ∃ x', x' ∈ Q.periodic ∧ Q.component x' = Q.component x := ⟨x, hx, rfl⟩
  refine ⟨h.choose, Classical.choose (exists_depth_component c hfin h.choose h.choose_spec.1),
    Classical.choose_spec (exists_depth_component c hfin h.choose h.choose_spec.1),
    h.choose_spec.2, fun u hu hcu ↦ ?_⟩
  unfold depth
  rw [hcu]
  unfold depthOn
  rw [dif_pos h, dif_pos hu]

theorem comp_arrow {y x : V} (hy : y ∈ Q.periodic) (hx : x ∈ Q.periodic) (a : y ⟶ x) :
    Q.component y = Q.component x :=
  component_eq (Relation.EqvGen.rel _ _ ⟨hy, hx, Or.inl ⟨a⟩⟩)

theorem comp_tau {x : V} (hx : x ∈ Q.periodic) (hn : x ∈ Q.nonprojective) :
    Q.component (Q.tau ⟨x, hn⟩).1 = Q.component x :=
  (component_eq (Relation.EqvGen.rel _ _ ⟨hx, periodic_tau hx, Or.inr ⟨hn, rfl⟩⟩)).symm

/-- **The depth function of `Γ`**, from the tree models of its periodic
components. -/
def meshDepth : Depth Q where
  e := depth c hfin
  tau_eq t hc := by
    obtain ⟨hxp, -⟩ := periodic_of_cyclic hc
    change t.1.1 ∈ Q.periodic at hxp
    obtain ⟨x₀, f, hf, hc0, hdep⟩ := depth_spec c hfin t.1.1 hxp
    have hcτ := comp_tau hxp t.1.2
    have hux : t.1.1 ∈ Q.component x₀ := hc0 ▸ mem_component_self hxp
    have huτ : (Q.tau t.1).1 ∈ Q.component x₀ :=
      hc0 ▸ hcτ ▸ mem_component_self (periodic_tau hxp)
    rw [hdep _ hux rfl, hdep _ huτ hcτ, ← hf.1 (FullSub.mk t.1.1 hux)]
    rfl
  uniq := by
    rintro ⟨x, y, a⟩ ⟨x', y', a'⟩ hxx hc hc' h h'
    obtain rfl : x = x' := hxx
    obtain ⟨hxp, hyp⟩ := periodic_of_cyclic hc
    obtain ⟨-, hyp'⟩ := periodic_of_cyclic hc'
    change x.1 ∈ Q.periodic at hxp
    change y ∈ Q.periodic at hyp
    change y' ∈ Q.periodic at hyp'
    obtain ⟨x₀, f, hf, hc0, hdep⟩ := depth_spec c hfin x.1 hxp
    have hcy := comp_arrow hyp hxp a
    have hcy' := comp_arrow hyp' hxp a'
    have hux : x.1 ∈ Q.component x₀ := hc0 ▸ mem_component_self hxp
    have huy : y ∈ Q.component x₀ := hc0 ▸ hcy ▸ mem_component_self hyp
    have huy' : y' ∈ Q.component x₀ := hc0 ▸ hcy' ▸ mem_component_self hyp'
    change depth c hfin y ≤ depth c hfin x.1 at h
    change depth c hfin y' ≤ depth c hfin x.1 at h'
    rw [hdep _ hux rfl, hdep _ huy hcy] at h
    rw [hdep _ hux rfl, hdep _ huy' hcy'] at h'
    have := hf.2 (FullSub.mk x.1 hux) (FullSub.mk y huy) (FullSub.mk y' huy') a a' h h'
    obtain rfl : y = y' := congrArg FullSub.val this
    obtain rfl : a = a' := Subsingleton.elim _ _
    rfl

include hfin in
/-- **Lemma 4.2** (`lem:mesh-walk-free`) for a finite translation quiver with at
most one arrow between two vertices and a finite-dimensional scalar mesh
category: every vertex group of the complex `K` is free. -/
theorem isFreeGroup_end (X : V) : IsFreeGroup (End (obK Q X)) :=
  isFreeGroup_end_of_depth (meshDepth c hfin) X

end MeshWalk

end MultiplicativeBasisDeformations
