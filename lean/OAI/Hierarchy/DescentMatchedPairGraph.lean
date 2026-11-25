import OAI.Hierarchy.DescentMatchedPairRead
import OAI.Hierarchy.DescentPackLabels

namespace OAI
/-! # Recovering the two original graph edges and four real sites of a physical pair -/

namespace Hierarchy.DescentPacking.PairRAM
open Computability.BorderVNP.Crossing
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits)
  {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)
  (color : N.Site→Bool) (B : ℕ) (c : C)
local notation "T" => nativeTraffic N core home
local notation "thinSites" => thinList home color c
local notation "thickSites" => thickList home color c
local notation "packing" => slabPacking T B thinSites thickSites
local notation "M" => Matched T B thinSites thickSites

def rawOffset (j : Locations (packing).decisions) : ℕ :=
  ProtocolRAMPortRanks.«prefix» (fun i : Locations (packing).decisions=>amount (live T) ((packing).decisions.get i).1)
    Fin.val j

def thickOffset (v : C) : ℕ :=
  ProtocolRAMPortRanks.«prefix» (fun d=>Fintype.card (ThickPool T thickSites d)) (fun d=>(Fintype.equivFin C d).val) v

def original (a : Atom (nativeTraffic N core home)) : N.Edge :=
  ((graphAtom (coreGraph N core) (fun e=>home (N.dst e.val)) (coreId N core)).symm a).val

/-- Prior tables contain all old edge occurrences, including those never matched.
The thick directory is split by destination then old site. The thin directory
is split by pack and preserves site, destination and original parallel-edge order. -/
structure OriginalRows (h : Contents) (edge : N.Edge→ℕ) (site : N.Site→ℕ) : Prop where
  thin : ∀ (j : Locations (packing).decisions) (o : ThinPool T ((packing).decisions.get j).1),
    h.thinEdge (rawOffset N core home color B c j+(thinPoolOrder T ((packing).decisions.get j).1 o).val)=
      edge (original N core home ⟨((packing).decisions.get j).1.get o.1,o.2⟩)
  thick : ∀ (v : C) (o : ThickPool T thickSites v),
    h.thickEdge (thickOffset N core home color c v+(thickPoolOrder T thickSites v o).val)=
      edge (original N core home ⟨(thickSites).get o.1,v,o.2⟩)
  src : ∀e,h.src (edge e)=site (N.src e)
  dst : ∀e,h.dst (edge e)=site (N.dst e)

private theorem ordered_thin (e : M) :
    (thinPoolOrder T ((packing).decisions.get e.2.1.val).1 (oldThin T B thinSites thickSites e).2).val=e.2.2.val := by
  change (thinPoolOrder T _ ((thinPoolOrder T _).symm _)).val=_
  exact congrArg Fin.val ((thinPoolOrder T ((packing).decisions.get e.2.1.val).1).apply_symm_apply _)

private theorem ordered_thick (e : M) :
    (thickPoolOrder T thickSites e.1 (oldThick T B thinSites thickSites e).2).val=(thickEnd packing e).2.val := by
  change (thickPoolOrder T _ _ ((thickPoolOrder T _ _).symm _)).val=_
  exact congrArg Fin.val ((thickPoolOrder T thickSites e.1).apply_symm_apply _)

private theorem edge_zero (e : M) :
    original N core home (thickAtom T e)=colorPick N core home color B (⟨c,e⟩,0) := rfl

private theorem edge_one (e : M) :
    original N core home (thinAtom T e)=colorPick N core home color B (⟨c,e⟩,1) := by
  change _=original N core home (if (1:Fin 2)=0 then thickAtom T e else thinAtom T e)
  simp

/-- The input counters of the stage, expressed exclusively in terms of earlier
physical whole items. The ordinal offset permits concatenating multiple colonies. -/
structure Position (h : Contents) (e : M) (base : ℕ) : Prop where
  thin : h.rawBefore=rawOffset N core home color B c e.2.1.val
  thick : h.binStart h.choice=thickOffset N core home color c e.1
  used : h.capacity h.choice-h.remaining h.choice=
    ∑i : Locations (packing).decisions,if i.val < e.2.1.val.val ∧ ((packing).decisions.get i).2=some e.1 then
      amount (live T) ((packing).decisions.get i).1 else 0
  dense : h.denseBefore=base+
    ∑i : Locations (packing).decisions,if i.val < e.2.1.val.val ∧ ((packing).decisions.get i).2.isSome then
      amount (live T) ((packing).decisions.get i).1 else 0

def actual (edge : N.Edge→ℕ) (site : N.Site→ℕ) (idx z prof : ℕ) (e : M) : Fin 9→ℕ :=
  let thick := colorPick N core home color B (⟨c,e⟩,0)
  let thin := colorPick N core home color B (⟨c,e⟩,1)
  ![idx,edge thick,edge thin,site (N.src thick),site (N.dst thick),site (N.src thin),site (N.dst thin),z,prof]

theorem actual_values {h : Contents} {edge : N.Edge→ℕ} {site : N.Site→ℕ}
    (d : OriginalRows N core home color B c h edge site) (e : M) {base : ℕ}
    (p : Position N core home color B c h e base) (z : ℕ) (f : Fin 9) :
    let idx := base+(pairNumber (amount (live T)) (packing).decisions e).val
    values h z e.2.2.val f=actual N core home color B c edge site idx z (h.profile idx) e f := by
  have index : h.denseBefore+e.2.2.val=base+(pairNumber (amount (live T)) (packing).decisions e).val := by
    rw [p.dense,pairNumber_prefix,Nat.add_assoc]
  have thin : h.thinEdge (thinIndex h e.2.2.val)=edge (colorPick N core home color B (⟨c,e⟩,1)) := by
    have eqn := d.thin e.2.1.val (oldThin T B thinSites thickSites e).2
    rw [ordered_thin] at eqn
    rw [← edge_one N core home color B c e, thinIndex, p.thin]
    exact eqn
  have th : h.thickEdge (thickIndex h e.2.2.val)=edge (colorPick N core home color B (⟨c,e⟩,0)) := by
    have eqn := d.thick e.1 (oldThick T B thinSites thickSites e).2
    rw [ordered_thick,thickEnd_prefix] at eqn
    rw [← edge_zero N core home color B c e, thickIndex, p.thick, p.used]
    exact eqn
  fin_cases f <;> simp [values,actual,index,thin,th,d.src,d.dst]

end
end Hierarchy.DescentPacking.PairRAM

end OAI
