import OAI.Hierarchy.DescentCorePairs
import OAI.Hierarchy.DescentStarMerges

namespace OAI
/-! # Original sites and the real ordered thin pack or thick center holding them -/

namespace Hierarchy.DescentPacking
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {U C : Type} [Fintype C] [DecidableEq C]

/-- This classifier uses the immutable old membership stream and the actual output
of whole-item packing. Its address does not depend on the replacement profile. -/
def packLabel (traffic : U → C → ℕ) (group : U → C) (B : ℕ) (thin thick : C → List U) (u : U) :
    OldSite (fun _ => traffic) B thin thick :=
  if hit : ∃ j : SlabSlot (fun _ => traffic) B thin thick (group u),
      u∈((slabPacking traffic B (thin (group u)) (thick (group u))).decisions.get j).1
    then .inr ⟨group u,hit.choose⟩ else .inl (group u)

theorem packLabel_thick (traffic : U → C → ℕ) (group : U → C) (B : ℕ) (thin thick : C → List U)
    (disjoint : ∀c,(thin c).Disjoint (thick c)) {u : U} {c : C} (home : group u=c)
    (old : u∈thick c) : packLabel traffic group B thin thick u=.inl c := by
  subst c
  unfold packLabel
  split
  · rename_i hit
    obtain ⟨j,member⟩ := hit
    have stream : u∈thin (group u) := by
      rw [←thin_stream traffic B (thin _) (thick _)]
      exact List.mem_flatten.mpr ⟨_,List.mem_map.mpr ⟨_,List.get_mem _ j,rfl⟩,member⟩
    exact False.elim (List.disjoint_left.mp (disjoint _) stream old)
  · rfl

theorem packLabel_slot (traffic : U → C → ℕ) (group : U → C) (B : ℕ) (thin thick : C → List U)
    (nod : ∀c,(thin c).Nodup) {u : U} {c : C} (home : group u=c)
    (j : SlabSlot (fun _ => traffic) B thin thick c)
    (old : u∈((slabPacking traffic B (thin c) (thick c)).decisions.get j).1) :
    packLabel traffic group B thin thick u=.inr ⟨c,j⟩ := by
  subst c
  let ds := (slabPacking traffic B (thin (group u)) (thick (group u))).decisions
  have hit : ∃j : Fin ds.length,u∈(ds.get j).1 := ⟨j,old⟩
  unfold packLabel
  rw [dite_eq_left hit]
  have uniq := pack_get ds (by simpa [ds,thin_stream] using nod (group u))
  obtain ⟨a,ha,hae⟩ := List.mem_iff_getElem.mp hit.choose_spec
  obtain ⟨b,hb,hbe⟩ := List.mem_iff_getElem.mp old
  have eq : (⟨hit.choose,⟨a,ha⟩⟩ : Σ i : Fin ds.length, Fin (ds.get i).1.length)=⟨j,⟨b,hb⟩⟩ :=
    uniq (hae.trans hbe.symm)
  rw [show hit.choose=j from congrArg Sigma.fst eq]

/-- Enumerate the original tape ordinals once, independent of the group filter. -/
def siteStream (U : Type*) [Fintype U] : List U := List.ofFn (Fintype.equivFin U).symm

@[simp] theorem mem_siteStream [Fintype U] (u : U) : u∈siteStream U :=
  List.mem_ofFn.mpr ⟨Fintype.equivFin U u,(Fintype.equivFin U).symm_apply_apply _⟩

theorem siteStream_nodup [Fintype U] : (siteStream U).Nodup :=
  List.nodup_ofFn.mpr (Fintype.equivFin U).symm.injective

/-- The literal old-site stream, restricted without reordering the table. -/
def groupStream [Fintype U] (group : U → C) (c : C) : List U :=
  (siteStream U).filter fun u => decide (group u=c)

omit [Fintype C] in
theorem groupStream_ordered [Fintype U] (group : U → C) (c : C) :
    (groupStream group c).Pairwise (fun a b => originalId U a < originalId U b) := by
  unfold groupStream siteStream
  apply List.Pairwise.filter
  apply List.pairwise_ofFn.mpr
  intro i j lt
  change ((Fintype.equivFin U) ((Fintype.equivFin U).symm i)).val <
    ((Fintype.equivFin U) ((Fintype.equivFin U).symm j)).val
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact Fin.lt_def.mp lt

omit [Fintype C] in
@[simp] theorem mem_groupStream [Fintype U] (group : U → C) (c : C) (u : U) :
    u∈groupStream group c ↔ group u=c := by simp [groupStream]

omit [Fintype C] in
theorem amount_groupStream [Fintype U] (pay : U → ℕ) (group : U → C) (c : C) :
    amount pay (groupStream group c)=∑ u, if group u=c then pay u else 0 := by
  let old := (Finset.univ.filter fun u => group u=c).toList
  have same : (groupStream group c).Perm old := by
    apply (List.perm_ext_iff_of_nodup ((siteStream_nodup (U:=U)).filter _) (Finset.nodup_toList _)).mpr
    intro u
    simp []
  calc
    _ = (old.map pay).sum := (same.map pay).sum_eq
    _ = _ := by simp only [old,Finset.sum_map_toList,Finset.sum_filter]

def colorSites [Fintype U] (group : U → C) (color : U → Bool) (t : Bool) (c : C) : List U :=
  (groupStream group c).filter fun u => color u == t

omit [Fintype C] in
@[simp] theorem mem_colorSites [Fintype U] (group : U → C) (color : U → Bool) (t : Bool) (c : C) (u : U) :
    u∈colorSites group color t c ↔ group u=c ∧ color u=t := by simp [colorSites]

omit [Fintype C] in
theorem colorSites_nodup [Fintype U] (group : U → C) (color : U → Bool) (t : Bool) (c : C) :
    (colorSites group color t c).Nodup := ((siteStream_nodup (U:=U)).filter _).filter _

omit [Fintype C] in
theorem colorSites_ordered [Fintype U] (group : U → C) (color : U → Bool) (t : Bool) (c : C) :
    (colorSites group color t c).Pairwise (fun a b => originalId U a < originalId U b) :=
  List.Pairwise.filter _ (groupStream_ordered group c)

omit [Fintype C] in
theorem colorSites_disjoint [Fintype U] (group : U → C) (color : U → Bool) (c : C) :
    (colorSites group color false c).Disjoint (colorSites group color true c) := by
  apply List.disjoint_left.mpr
  intro u h h'
  have lo := ((mem_colorSites ..).mp h).2
  have hi := ((mem_colorSites ..).mp h').2
  simp_all

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

variable (core : Finset N.Edge) (group : N.Site → C) (color : N.Site → Bool) (B : ℕ)

abbrev nativeTraffic := edgeTraffic (coreGraph N core) (fun e => group (N.dst e.1))
abbrev thinList [Fintype U] (group : U → C) (color : U → Bool) := colorSites group color false
abbrev thickList [Fintype U] (group : U → C) (color : U → Bool) := colorSites group color true

def colorPick := pairedCore N core (fun e => group (N.dst e)) group B (thinList group color) (thickList group color)
  (colorSites_nodup group color false) (colorSites_nodup group color true) (colorSites_disjoint group color)
  (fun _ _ h => ((mem_colorSites ..).mp h).1) (fun _ _ h => ((mem_colorSites ..).mp h).1)

abbrev coloredPack := packLabel (nativeTraffic N core group) group B (thinList group color) (thickList group color)

theorem colorPick_thick_src (p) : coloredPack N core group color B
    (N.src (colorPick N core group color B (p,0)))=.inl p.1 := by
  let N₀ := coreGraph N core
  let dest := fun e : N₀.Edge => group (N.dst e.1)
  let a := thickAtom (edgeTraffic N₀ dest) p.2
  change packLabel _ _ _ _ _ (N₀.src ((graphAtom N₀ dest (coreId N core)).symm a))=_
  rw [graphAtom_src N₀ dest a (coreId N core)]
  have old := List.get_mem (thickList group color p.1)
    (oldThick (edgeTraffic N₀ dest) B (thinList group color p.1) (thickList group color p.1) p.2).2.1
  exact packLabel_thick _ _ _ _ _ (colorSites_disjoint group color) ((mem_colorSites ..).mp old).1 old

theorem colorPick_thin_src (p) : coloredPack N core group color B
    (N.src (colorPick N core group color B (p,1)))=
      .inr (thinSite (fun _ => nativeTraffic N core group) B (thinList group color) (thickList group color) p) := by
  let N₀ := coreGraph N core
  let dest := fun e : N₀.Edge => group (N.dst e.1)
  let a := thinAtom (edgeTraffic N₀ dest) p.2
  change packLabel _ _ _ _ _ (N₀.src ((graphAtom N₀ dest (coreId N core)).symm a))=_
  rw [graphAtom_src N₀ dest a (coreId N core)]
  have old := thinAtom_in (edgeTraffic N₀ dest) p.2
  apply packLabel_slot _ _ _ _ _ (colorSites_nodup group color false) ((mem_colorSites ..).mp old).1
  exact List.get_mem _ _

/-- The affine sheet depends only on the block in the pre-stage group, hence
has equal values at the ends of each of its core cables. -/
theorem colorPick_thick_dst (same : ∀e∈core,color (N.src e)=color (N.dst e)) (p) :
    coloredPack N core group color B (N.dst (colorPick N core group color B (p,0)))=.inl p.2.1 := by
  let N₀ := coreGraph N core
  let dest := fun e : N₀.Edge => group (N.dst e.1)
  let a := thickAtom (edgeTraffic N₀ dest) p.2
  let e := (graphAtom N₀ dest (coreId N core)).symm a
  change packLabel _ _ _ _ _ (N.dst e.1)=_
  have home : group (N.dst e.1)=p.2.1 := graphAtom_dest N₀ dest a (coreId N core)
  have old := List.get_mem (thickList group color p.1)
    (oldThick (edgeTraffic N₀ dest) B (thinList group color p.1) (thickList group color p.1) p.2).2.1
  have src : color (N.src e.1)=true := by
    change color (N₀.src ((graphAtom N₀ dest (coreId N core)).symm a))=true
    rw [graphAtom_src N₀ dest a (coreId N core)]
    exact ((mem_colorSites ..).mp old).2
  have dst : color (N.dst e.1)=true := (same e.1 e.2).symm.trans src
  exact packLabel_thick _ _ _ _ _ (colorSites_disjoint group color) home ((mem_colorSites ..).mpr ⟨home,dst⟩)

end
end Hierarchy.DescentPacking

end OAI
