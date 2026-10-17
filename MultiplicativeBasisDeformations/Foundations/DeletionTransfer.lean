import MultiplicativeBasisDeformations.Foundations.ObjectQuotients
import MultiplicativeBasisDeformations.Foundations.ZDeltaGauge
import MultiplicativeBasisDeformations.Foundations.CoveringMesh

/-!
# Deleting vertices along a covering

Appendix A, `periodic-mesh-calculations.tex:57–66, 616–637`: "Paths lift uniquely
from a chosen start. Contextual mesh relations lift to contextual mesh relations
… The fixed-start lifting of paths and relations preserves nonvanishing", and
"Delete all lifts of the two outer vertices of the long arms … (5.2) identifies
the object quotient with the `D₄` mesh category of the same period."

The object quotient `C(Q)/[D]` is `kQ` modulo the mesh ideal plus the paths
through `D` (`oqFunctor_map_eq_zero_iff`). We add the identities of the deleted
vertices to a relation system (`RelSystem.del`), lift relations along a
covering from a fixed start (`ofStar_liftStar_mem`), rescale to signed
coefficients, and forget heights into `Π(Δ)` modulo the deleted vertices.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w v' w'

namespace RelSystem

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] (R : RelSystem k V)

theorem path_nil' {V : Type v} [Quiver.{w} V] (x : V) :
    LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path x x) = 𝟙 (LinearPaths.obj x) := rfl

/-- The relations together with the identities of the vertices of `D`. -/
def del (D : Set V) : RelSystem k V where
  I := R.I ⊕ D
  s | .inl i => R.s i | .inr d => d.1
  t | .inl i => R.t i | .inr d => d.1
  rel | .inl i => R.rel i | .inr d => 𝟙 _

theorem ideal_le_del (D : Set V) {X Y : V} : R.ideal (LinearPaths.obj (k := k) X)
    (LinearPaths.obj Y) ≤ (R.del D).ideal _ _ := fun f hf ↦
  R.ideal_induction (P := fun f ↦ f ∈ (R.del D).ideal _ _) (zero_mem _)
    (fun _ _ hf hg ↦ add_mem hf hg) (fun c _ hf ↦ Submodule.smul_mem _ c hf)
    (fun i p p' ↦ (R.del D).comp_rel_comp_mem (Sum.inl i) _ _) hf

theorem path_comp_mem_del (D : Set V) {X d Y : V} (hd : d ∈ D) (p : Quiver.Path X d)
    (q : Quiver.Path d Y) : LinearPaths.path (k := k) (p.comp q) ∈ (R.del D).ideal _ _ := by
  have := (R.del D).comp_rel_comp_mem (Sum.inr ⟨d, hd⟩) (LinearPaths.path p) (LinearPaths.path q)
  change LinearPaths.path p ≫ 𝟙 _ ≫ LinearPaths.path q ∈ _ at this
  rwa [Category.id_comp, LinearPaths.path_comp_path] at this

theorem through_le_del (D : Set V) {X Y : V} :
    through k D X Y ≤ (R.del D).ideal _ _ :=
  Submodule.span_le.2 fun _ ⟨p, ⟨d, hd, hdD⟩, hf⟩ ↦ by
    obtain ⟨p₁, p₂, rfl⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hd
    rw [hf]
    exact R.path_comp_mem_del D hdD p₁ p₂

/-- Induction over the ideal of a deletion. -/
theorem del_induction (D : Set V) {X Y : V}
    {P : (LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y) → Prop}
    (h0 : P 0) (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : k) f, P f → P (c • f))
    (hgen : ∀ (i : R.I) (p : Quiver.Path X (R.s i)) (p' : Quiver.Path (R.t i) Y),
      P (LinearPaths.path p ≫ R.rel i ≫ LinearPaths.path p'))
    (hdel : ∀ (d : V) (_ : d ∈ D) (p : Quiver.Path X d) (p' : Quiver.Path d Y),
      P (LinearPaths.path p ≫ LinearPaths.path p'))
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y} (hf : f ∈ (R.del D).ideal _ _) : P f := by
  refine (R.del D).ideal_induction h0 hadd hsmul (fun i p p' ↦ ?_) hf
  rcases i with i | ⟨d, hd⟩
  · exact hgen i p p'
  · have := hdel d hd p p'
    change P (LinearPaths.path p ≫ 𝟙 _ ≫ LinearPaths.path p')
    rwa [Category.id_comp]

variable {W : Type v'} [Quiver.{w'} W]

/-- Relations of a deletion lift along a covering, if the relations do and the
deleted vertices of the cover contain the preimages of those of the base. -/
theorem lift_condition_del (φ : W ⥤q V) (RW : RelSystem k W) (RV : RelSystem k V)
    (DW : Set W) (DV : Set V) (hD : ∀ Z, φ.obj Z ∈ DV → Z ∈ DW)
    (hrel : ∀ (Z : W) (i' : RV.I) (h : RV.s i' = φ.obj Z), ∃ (i : RW.I) (hs : RW.s i = Z)
      (ht : RV.t i' = φ.obj (RW.t i)),
      LinearPaths.mapPaths φ _ _ (RW.rel i) = eqToHom (by rw [hs, h]) ≫ RV.rel i' ≫ eqToHom (by rw [ht]))
    (Z : W) (i' : (RV.del DV).I) (h : (RV.del DV).s i' = φ.obj Z) :
    ∃ (i : (RW.del DW).I) (hs : (RW.del DW).s i = Z) (ht : (RV.del DV).t i' = φ.obj ((RW.del DW).t i)),
      LinearPaths.mapPaths (k := k) φ _ _ ((RW.del DW).rel i) =
        eqToHom (by rw [hs, h]) ≫ (RV.del DV).rel i' ≫ eqToHom (by rw [ht]) := by
  rcases i' with i' | ⟨d, hd⟩
  · obtain ⟨i, hs, ht, hmap⟩ := hrel Z i' h
    exact ⟨Sum.inl i, hs, ht, hmap⟩
  · change d = φ.obj Z at h
    subst h
    refine ⟨Sum.inr ⟨Z, hD Z hd⟩, rfl, rfl, ?_⟩
    change LinearPaths.mapPaths φ _ _ (𝟙 (LinearPaths.obj Z)) = _ ≫ 𝟙 _ ≫ _
    rw [← path_nil', LinearPaths.mapPaths_path, Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl

/-- **Fixed-start lifting of relations**: every target component of the lift of
an element of the base ideal lies in the ideal of the cover. -/
theorem ofStar_liftStar_mem (φ : W ⥤q V) (hφ : φ.IsCovering) (RW : RelSystem k W)
    (RV : RelSystem k V)
    (hL : ∀ (X : W) (i' : RV.I) (p : Quiver.Path (φ.obj X) (RV.s i')) {y : V}
      (p' : Quiver.Path (RV.t i') y), ∃ (Y : W) (e : φ.obj Y = y)
        (g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y), g ∈ RW.ideal _ _ ∧
        LinearPaths.mapPaths φ X Y g =
          (LinearPaths.path p ≫ RV.rel i' ≫ LinearPaths.path p') ≫ eqToHom (by rw [e]))
    {X : W} {y : V} {F : LinearPaths.obj (k := k) (φ.obj X) ⟶ LinearPaths.obj y}
    (hF : F ∈ RV.ideal _ _) (Y : W) :
    ofStar Y (liftStar φ hφ X (toStar y F)) ∈ RW.ideal (LinearPaths.obj X) (LinearPaths.obj Y) := by
  classical
  let G : Submodule k (StarSpace (k := k) X) :=
    Submodule.span k {F | ∃ (Y' : W) (g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y'),
      g ∈ RW.ideal _ _ ∧ F = toStar Y' g}
  have hB : liftStar φ hφ X (toStar y F) ∈ G := by
    refine RV.ideal_induction (P := fun F ↦ liftStar φ hφ X (toStar y F) ∈ G) ?_ ?_ ?_ ?_ hF
    · simp
    · intro f g hf hg; rw [map_add, map_add]; exact add_mem hf hg
    · intro c f hf; rw [map_smul, map_smul]; exact Submodule.smul_mem _ c hf
    · intro i' p p'
      obtain ⟨Y', e, g, hg, hmap⟩ := hL X i' p p'
      subst e
      simp only [eqToHom_refl, Category.comp_id] at hmap
      rw [← hmap, liftStar_toStar_mapPaths]
      exact Submodule.subset_span ⟨Y', g, hg, rfl⟩
  have hC : ∀ F ∈ G, ofStar Y F ∈ RW.ideal (LinearPaths.obj X) (LinearPaths.obj Y) := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
        obtain ⟨Y', g, hg, rfl⟩ := hF
        by_cases hY : Y' = Y
        · subst hY; rw [ofStar_toStar]; exact hg
        · rw [ofStar_toStar_ne hY]; exact zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  exact hC _ hB

theorem liftStar_single (φ : W ⥤q V) (hφ : φ.IsCovering) {X Y : W} (P : Quiver.Path X Y) :
    liftStar (k := k) φ hφ X (Finsupp.single ⟨φ.obj Y, φ.mapPath P⟩ 1) = Finsupp.single ⟨Y, P⟩ 1 := by
  have := liftStar_toStar_mapPaths (k := k) φ hφ (LinearPaths.path P)
  rwa [LinearPaths.mapPaths_path, toStar_path, toStar_path] at this

/-- The two components of the lift of `a 𝟙 + b (φ P)` for a path `P : X → E`
whose image is closed. -/
theorem components (φ : W ⥤q V) (hφ : φ.IsCovering) {X E : W} (hXE : X ≠ E)
    (hE : φ.obj E = φ.obj X) (P : Quiver.Path X E) (a b : k) :
    ofStar E (liftStar φ hφ X (toStar (φ.obj X) (a • 𝟙 (LinearPaths.obj (k := k) (φ.obj X)) +
        b • LinearPaths.path ((φ.mapPath P).cast rfl hE)))) = b • LinearPaths.path P ∧
    ofStar X (liftStar φ hφ X (toStar (φ.obj X) (a • 𝟙 (LinearPaths.obj (k := k) (φ.obj X)) +
        b • LinearPaths.path ((φ.mapPath P).cast rfl hE)))) = a • 𝟙 (LinearPaths.obj X) := by
  have e1 : toStar (k := k) (φ.obj X) (𝟙 (LinearPaths.obj (φ.obj X))) =
      Finsupp.single ⟨φ.obj X, φ.mapPath (Quiver.Path.nil : Quiver.Path X X)⟩ 1 := by
    rw [← path_nil', toStar_path]; rfl
  have e2 : toStar (k := k) (φ.obj X) (LinearPaths.path ((φ.mapPath P).cast rfl hE)) =
      Finsupp.single ⟨φ.obj E, φ.mapPath P⟩ 1 := by
    rw [toStar_path]
    congr 1
    exact Sigma.ext hE.symm (by simp [Quiver.Path.cast_heq])
  have hX : liftStar φ hφ X (toStar (φ.obj X) (a • 𝟙 (LinearPaths.obj (k := k) (φ.obj X)) +
        b • LinearPaths.path ((φ.mapPath P).cast rfl hE))) =
      a • toStar X (𝟙 (LinearPaths.obj (k := k) X)) + b • toStar E (LinearPaths.path P) := by
    rw [map_add, map_smul, map_smul, e1, e2, map_add, map_smul, map_smul, liftStar_single,
      liftStar_single, ← path_nil', toStar_path, toStar_path]
  rw [hX]
  constructor
  · rw [map_add, map_smul, map_smul, ofStar_toStar_ne hXE, ofStar_toStar, smul_zero, zero_add]
  · rw [map_add, map_smul, map_smul, ofStar_toStar_ne (Ne.symm hXE), ofStar_toStar, smul_zero,
      add_zero]

end RelSystem

section Gauge

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)]

/-- A gauge transformation maps the ideal of a deletion of the mesh relations of
`c` into that of `c'`. -/
theorem gaugeMap_mem_del (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
    (c c' : MeshCoefficients k Q)
    (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a) (D : Set V)
    {X Y : V} {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ ((RelSystem.mesh c).del D).ideal _ _) :
    gaugeMap μ X Y f ∈ ((RelSystem.mesh c').del D).ideal _ _ := by
  refine (RelSystem.mesh c).del_induction D
    (P := fun f ↦ gaugeMap μ X Y f ∈ ((RelSystem.mesh c').del D).ideal _ _) (by simp)
    (fun f g hf hg ↦ by rw [map_add]; exact add_mem hf hg)
    (fun t f hf ↦ by rw [map_smul]; exact Submodule.smul_mem _ t hf) (fun i p p' ↦ ?_)
    (fun d hd p p' ↦ ?_) hf
  · have := gaugeMap_mem_ideal μ η c c' h ((RelSystem.mesh c).comp_rel_comp_mem i
      (LinearPaths.path p) (LinearPaths.path p'))
    exact (RelSystem.mesh c').ideal_le_del D this
  · rw [gaugeMap_comp, gaugeMap_path, gaugeMap_path, Linear.smul_comp, Linear.comp_smul,
      LinearPaths.path_comp_path]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      ((RelSystem.mesh c').path_comp_mem_del D hd p p'))

/-- A single path lies in the deletion ideal of `c'` if it lies in that of `c`. -/
theorem path_mem_del_of_gauge (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ)
    (c c' : MeshCoefficients k Q)
    (h : ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
      c' x y a = η x * c x y a * μ (Q.mate x y a) * μ a) (D : Set V)
    {X Y : V} (P : Quiver.Path X Y)
    (hP : LinearPaths.path (k := k) P ∈ ((RelSystem.mesh c).del D).ideal _ _) :
    LinearPaths.path (k := k) P ∈ ((RelSystem.mesh c').del D).ideal _ _ := by
  have := gaugeMap_mem_del μ η c c' h D hP
  rw [gaugeMap_path] at this
  have h2 := Submodule.smul_mem _ (((pathWt μ P)⁻¹ : kˣ) : k) this
  rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h2

end Gauge

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D) [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

/-- Forgetting heights maps the signed mesh ideal with deleted vertices into the
ideal of `Π(Δ)` with deleted vertices. -/
theorem forget_mem_preproj_del (DZ : Set T.ZVert) (Del : Set T.Dbl)
    (hD : ∀ Z ∈ DZ, T.toDbl Z.v ∈ Del) {X Y : T.ZVert}
    {f : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y}
    (hf : f ∈ ((RelSystem.mesh (T.zSigned k)).del DZ).ideal _ _) :
    LinearPaths.mapPaths T.forget X Y f ∈ ((T.preproj k).del Del).ideal _ _ := by
  refine RelSystem.mapPaths_mem_ideal T.forget _ _ (fun i p p' ↦ ?_) hf
  rcases i with i | ⟨d, hd⟩
  · rw [LinearPaths.mapPaths_comp, LinearPaths.mapPaths_comp, LinearPaths.mapPaths_path,
      LinearPaths.mapPaths_path]
    change _ ≫ LinearPaths.mapPaths T.forget _ _ (meshRelation (T.zSigned k) i) ≫ _ ∈ _
    rw [mapPaths_forget_meshRelation]
    exact (T.preproj k).ideal_le_del Del ((T.preproj k).comp_rel_comp_mem (T.toDbl i.1.v) _ _)
  · change LinearPaths.mapPaths T.forget _ _ (LinearPaths.path p ≫ 𝟙 _ ≫ LinearPaths.path p') ∈ _
    rw [Category.id_comp, LinearPaths.path_comp_path, LinearPaths.mapPaths_path,
      Prefunctor.mapPath_comp]
    exact (T.preproj k).path_comp_mem_del Del (hD d hd) _ _

include hπ hτ in
/-- Mesh relations with deleted vertices lift along `π` from a fixed start. -/
theorem lift_del (Dset : Set V) (X : T.ZVert) (i' : ((RelSystem.mesh c).del Dset).I)
    (p : Quiver.Path (π.obj X) (((RelSystem.mesh c).del Dset).s i')) {y : V}
    (p' : Quiver.Path (((RelSystem.mesh c).del Dset).t i') y) :
    ∃ (Y : T.ZVert) (e : π.obj Y = y)
      (g : LinearPaths.obj (k := k) X ⟶ LinearPaths.obj Y),
      g ∈ ((RelSystem.mesh (T.pullCoeff hQ π c)).del {Z | π.obj Z ∈ Dset}).ideal _ _ ∧
      LinearPaths.mapPaths π X Y g = (LinearPaths.path p ≫ ((RelSystem.mesh c).del Dset).rel i' ≫
        LinearPaths.path p') ≫ eqToHom (by rw [e]) := by
  refine RelSystem.lift_condition π hπ _ _ (RelSystem.lift_condition_del π _ _ _ _
    (fun Z hZ ↦ hZ) (fun Z i' h ↦ ?_)) X i' p p'
  have ht : i'.1 = π.obj (T.ztauInv Z) := by
    apply hQ.tauE.injective
    rw [← hτ, T.ztau_ztauInv]
    exact h
  have hi : i' = T.piNP hQ π (T.ztauInv Z) := Subtype.ext ht
  subst hi
  refine ⟨⟨T.ztauInv Z, trivial⟩, T.ztau_ztauInv Z, rfl, ?_⟩
  change LinearPaths.mapPaths _ _ _ (meshRelation (T.pullCoeff hQ π c) _) = _
  rw [T.mapPaths_meshRelation hQ π hπ hτ]
  simp

include hπ hτ in
/-- **Fixed-start lifting into `Π(Δ)` modulo deleted vertices.** If
`a 𝟙 + b (π P)` vanishes in the object quotient `C(Q)/[D]` for a path
`P : X → E` with closed image, then `b P` and `a 𝟙` vanish in `Π(Δ)` modulo the
deleted vertices, after forgetting heights. -/
theorem transfer_del (Dset : Set V) (Del : Set T.Dbl)
    (hD : ∀ Z : T.ZVert, π.obj Z ∈ Dset → T.toDbl Z.v ∈ Del)
    {X E : T.ZVert} (hXE : X ≠ E) (hE : π.obj E = π.obj X) (P : Quiver.Path X E) (a b : k)
    (hmem : a • 𝟙 (LinearPaths.obj (k := k) (π.obj X)) +
        b • LinearPaths.path ((π.mapPath P).cast rfl hE) ∈
      meshIdealSub c _ _ ⊔ through k Dset (π.obj X) (π.obj X)) :
    b • LinearPaths.path (k := k) (T.forget.mapPath P) ∈ ((T.preproj k).del Del).ideal _ _ ∧
      a • LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path (T.forget.obj X) (T.forget.obj X)) ∈
        ((T.preproj k).del Del).ideal _ _ := by
  have hmem' : a • 𝟙 (LinearPaths.obj (k := k) (π.obj X)) +
      b • LinearPaths.path ((π.mapPath P).cast rfl hE) ∈ ((RelSystem.mesh c).del Dset).ideal _ _ :=
    sup_le ((RelSystem.mesh c).ideal_le_del Dset) ((RelSystem.mesh c).through_le_del Dset) hmem
  have hL := T.lift_del hQ π c hπ hτ Dset
  obtain ⟨hcE, hcX⟩ := RelSystem.components π hπ hXE hE P a b
  have uE := RelSystem.ofStar_liftStar_mem π hπ _ _ hL hmem' E
  have uX := RelSystem.ofStar_liftStar_mem π hπ _ _ hL hmem' X
  rw [hcE] at uE
  rw [hcX] at uX
  obtain ⟨μ, hμ⟩ := T.exists_gauge (T.pullCoeff hQ π c)
  have step : ∀ {Y : T.ZVert} (R : Quiver.Path X Y) (t : k),
      t • LinearPaths.path (k := k) R ∈
        ((RelSystem.mesh (T.pullCoeff hQ π c)).del {Z | π.obj Z ∈ Dset}).ideal _ _ →
      t • LinearPaths.path (k := k) (T.forget.mapPath R) ∈ ((T.preproj k).del Del).ideal _ _ := by
    intro Y R t ht
    by_cases ht0 : t = 0
    · rw [ht0, zero_smul]; exact zero_mem _
    have h1 : LinearPaths.path (k := k) R ∈
        ((RelSystem.mesh (T.pullCoeff hQ π c)).del {Z | π.obj Z ∈ Dset}).ideal _ _ := by
      have := Submodule.smul_mem _ t⁻¹ ht
      rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
    have h2 := path_mem_del_of_gauge μ (fun _ ↦ 1) _ _ hμ _ R h1
    have h3 := T.forget_mem_preproj_del (k := k) {Z | π.obj Z ∈ Dset} Del (fun Z hZ ↦ hD Z hZ) h2
    rw [LinearPaths.mapPaths_path] at h3
    exact Submodule.smul_mem _ t h3
  refine ⟨step P b uE, ?_⟩
  have := step (Quiver.Path.nil : Quiver.Path X X) a (by rwa [RelSystem.path_nil'])
  exact this

end OrientedTree

end MultiplicativeBasisDeformations
