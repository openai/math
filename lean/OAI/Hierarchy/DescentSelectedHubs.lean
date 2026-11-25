import OAI.Hierarchy.DescentStageMeasures
import OAI.Hierarchy.DescentHubCoalescence
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # Hub marks on the actual selected, coalesced and unbundled graphs -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P : Type*} {bits : P→ℕ}

omit [Field F] in
/-- On the measured occupied colonies, equality of colored pack IDs preserves the actual host row. -/
theorem colored_pack_hub {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}
    (A : MarkedWorld F d P bits) (pos : A.graph.Site→V) (block : A.graph.Site→DescentColonies.Block k)
    (full : A.graph.Site→ℕ) (near : V→Finset V) (D a B pairCap : ℕ)
    (small : ∀v i,StarKeys.blockMass A.graph pos block full v i≤B)
    (color : A.graph.Site→Bool) (hostHub : V→Bool) (u v : A.graph.Site) :
    let home := StarKeys.occupiedHome A.graph pos block full near D a B small
    DescentPacking.coloredPack A.graph A.core home color pairCap u=DescentPacking.coloredPack A.graph A.core home color pairCap v →
      hostHub (pos u)=hostHub (pos v) := by
  intro home same
  have first := (StarKeys.pack_home A.graph pairCap home color A.core u).symm.trans
    ((congrArg StarKeys.packColony same).trans (StarKeys.pack_home A.graph pairCap home color A.core v))
  let col := StarKeys.occupiedAddress A.graph B near D a (StarKeys.blockMass A.graph pos block full) small pos block
  simpa only [home,col,StarKeys.occupiedHome,StarKeys.occupiedAddress_colonyOf,StarKeys.colonyCode] using
    congrArg (fun c => hostHub (col c).1) first

/-- The actual native host key has the inherited hub flag, even when a live thin slot moves to
its center. The representative belongs to the very same quotient site. -/
theorem native_key_hub {C V : Type} [Fintype C] [DecidableEq C] [DecidableEq V]
    (N : Network d P bits) (core : Finset N.Edge) (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)
    (col : C ↪ V×(ℕ×ℕ)) (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool) (hostHub : V→Bool)
    (mark : Merged N (DescentPacking.colorPick N core home color B) l (DescentPacking.coloredPack N core home color B)→Bool)
    (old : ∀u,mark (newSite N (DescentPacking.colorPick N core home color B) l
      (DescentPacking.coloredPack N core home color B) (.inl u))=hostHub (col (home u)).1) (v) :
    hostHub (StarKeys.nativeKey N core home color B col same l v).1=mark v := by
  let pick := DescentPacking.colorPick N core home color B
  let pack := DescentPacking.coloredPack N core home color B
  let slot := StarKeys.chosenSlot N core home color B
  let center := StarKeys.chosenCenter N core home color B l
  obtain ⟨u,rfl⟩ := old_surjective N pick l pack v
  obtain ⟨w,member,atSite⟩ := StarKeys.representative N pick l pack slot center
    (DescentPacking.colorPick_thin_src N core home color B) (StarKeys.native_centerAt N core home color B same l) u
  have addr := StarKeys.packed_home N core home color B col w
  change hostHub (StarKeys.packAddress N core home color B col (StarKeys.resolve slot center (pack u))).1 = _
  calc
    _ = hostHub (StarKeys.packAddress N core home color B col (pack w)).1 :=
      congrArg (fun x => hostHub (StarKeys.packAddress N core home color B col x).1) member.symm
    _ = hostHub (col (home w)).1 := congrArg (fun k => hostHub k.1) addr
    _ = mark (newSite N pick l pack (.inl w)) := (old w).symm
    _ = _ := congrArg mark atSite.symm

section Selected
variable (A : MarkedWorld F d P bits) {I C : Type} [Fintype I] (G : PoweredGadget F)
variable (pick : I×Fin 2 ↪ A.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,A.graph.width (pick (i,s))=z i*G.b) (pack : A.graph.Site→C) (p : I→Profile G.C)
variable (hub : A.graph.Site→Bool) (inc : HubIncidence A hub) (picked : ∀t,pick t∈A.core)
variable (packed : ∀u v,pack u=pack v → hub u=hub v)
local notation "sw" => branchWidth G z p
local notation "lay" => bestLayout sw
local notation "A′" => A.selected G pick z hz fit pack p

/-- Old sites keep their marks, and every installed motif party belongs to a nonhub. -/
def selectedHub : (A′).graph.Site→Bool :=
  Quot.lift (r:=Join A.graph pick lay pack) (Sum.elim hub (fun _=>false)) (by
    intro a b rel
    cases rel with
    | source i s => exact (inc.inside _ (picked (i,s))).1
    | target i s => exact (inc.inside _ (picked (i,s))).2
    | privateWire => rfl
    | old u v h => exact packed u v h)

local notation "mark" => selectedHub A G pick z hz fit pack p hub inc picked packed

@[simp] theorem selected_old_hub (u : A.graph.Site) : mark (newSite A.graph pick lay pack (.inl u))=hub u := rfl
@[simp] theorem selected_party_hub (i : I) (j : Fin 6) : mark (newSite A.graph pick lay pack (.inr (i,j)))=false := rfl

theorem selected_true_iff (v : (A′).graph.Site) : mark v=true ↔
    ∃u : A.graph.Site,hub u=true ∧ newSite A.graph pick lay pack (.inl u)=v := by
  obtain ⟨u,rfl⟩ := old_surjective A.graph pick lay pack v
  constructor
  · intro h
    exact ⟨u,h,rfl⟩
  · rintro ⟨w,hw,eq⟩
    exact (congrArg mark eq).symm.trans hw

theorem selected_pin_hub (pin : P) : mark ((A′).graph.attach pin)=hub (A.graph.attach pin) := rfl

include inc picked in
omit [Field F] in
private theorem old_target_hub (e : A.graph.Edge) :
    Sum.elim hub (fun _=>false) (GadgetNetwork.target A.graph pick (.inl e)) = hub (A.graph.dst e) := by
  cases hs : GadgetNetwork.selected A.graph pick e with
  | none => simp [GadgetNetwork.target,hs]
  | some t =>
    have h := (inc.inside _ (picked t)).2
    rw [GadgetNetwork.selected_spec A.graph pick hs] at h
    simpa [GadgetNetwork.target,hs] using h.symm

theorem selected_hubs : HubIncidence A′ mark := by
  let zeroPos := fun _ : Merged A.graph pick lay pack => (0:EuclideanSpace ℝ (Fin d))
  let ball := fun u => (by simp [zeroPos] : ‖zeroPos u‖≤1)
  have oldDst := old_target_hub A pick hub inc picked
  constructor
  · intro e he
    have mem := (GadgetNetwork.mem_nextCore A.graph pick sw lay pack zeroPos ball A.core e).mp he
    rcases e with ⟨e,external⟩
    rcases e with e | (⟨i,s⟩ | ⟨i,t⟩)
    · change hub (A.graph.src e)=false ∧ Sum.elim hub (fun _=>false) (GadgetNetwork.target A.graph pick (.inl e))=false
      rw [oldDst]
      exact inc.inside e mem
    · exact ⟨rfl,(inc.inside _ (picked (i,s))).2⟩
    · exact ⟨rfl,rfl⟩
  · intro e he
    have mem := mt (GadgetNetwork.mem_nextCore A.graph pick sw lay pack zeroPos ball A.core e).mpr he
    rcases e with ⟨e,external⟩
    rcases e with e | extra
    · change hub (A.graph.src e)≠Sum.elim hub (fun _=>false) (GadgetNetwork.target A.graph pick (.inl e))
      rw [oldDst]
      exact inc.outside e mem
    · exact (mem trivial).elim
include hub inc picked packed in
/-- Every old tether survives at the images of its two old endpoints with its original width. -/
theorem selected_tether_image (e : A.graph.Edge) (old : e∉A.core) :
    ∃t : (A′).graph.Edge,t∉(A′).core ∧ (A′).graph.width t=A.graph.width e ∧
      (A′).graph.src t=newSite A.graph pick lay pack (.inl (A.graph.src e)) ∧
      (A′).graph.dst t=newSite A.graph pick lay pack (.inl (A.graph.dst e)) := by
  have unused : GadgetNetwork.selected A.graph pick e=none := by
    cases hs : GadgetNetwork.selected A.graph pick e with
    | none => rfl
    | some t => exact (old (GadgetNetwork.selected_spec A.graph pick hs ▸ picked t)).elim
  have dest : GadgetNetwork.target A.graph pick (.inl e)=.inl (A.graph.dst e) := by simp [GadgetNetwork.target,unused]
  have cross : newSite A.graph pick lay pack (.inl (A.graph.src e)) ≠ newSite A.graph pick lay pack (GadgetNetwork.target A.graph pick (.inl e)) := by
    rw [dest]
    exact fun h=>inc.outside e old (congrArg mark h)
  let t : (A′).graph.Edge := ⟨.inl e,cross⟩
  refine ⟨t,?_,rfl,rfl,congrArg (newSite A.graph pick lay pack) dest⟩
  let zeroPos := fun _ : Merged A.graph pick lay pack => (0:EuclideanSpace ℝ (Fin d))
  let ball := fun u => (by simp [zeroPos] : ‖zeroPos u‖≤1)
  exact mt (GadgetNetwork.mem_nextCore A.graph pick sw lay pack zeroPos ball A.core t).mp old
end Selected

section Coalesced
variable {V P : Type} {bits : P→ℕ} [DecidableEq V] (A : MarkedWorld F d P bits)
variable (key : A.graph.Site→Key V) (hub : V→Bool) (k g : ℕ)
local notation "A′" => A.coalesced key hub k g

def coalescedHub (v : (A′).graph.Site) := hub v.val.1

@[simp] theorem coalesced_at_hub (u : A.graph.Site) :
    coalescedHub A key hub k g (address A key hub k g u)=hub (key u).1 := by
  change hub (mergeHub hub k g (key u)).1=hub (key u).1
  cases h : hub (key u).1 <;> simp [mergeHub,h]

omit [Field F] in
/-- A saturated old stack lands at the common coarse prefix, in slot zero of the same host row. -/
theorem coalesced_hub_address {a : ℕ} (ag : a≤g) (gk : g≤k) (u : A.graph.Site)
    (yes : hub (key u).1=true) (x : DescentColonies.Block k)
    (prefixKey : (key u).2.1=(k-a,DescentColonies.group (k-a) x)) :
    (address A key hub k g u).val=((key u).1,(k-g,DescentColonies.group (k-g) x),0) := by
  change mergeHub hub k g (key u)=_
  have view : key u=((key u).1,(k-a,DescentColonies.group (k-a) x),(key u).2.2) :=
    Prod.ext rfl (Prod.ext prefixKey rfl)
  exact (congrArg (mergeHub hub k g) view).trans (merge_hub_read hub ag gk _ yes x _)

theorem coalesced_pin_hub (p : P) : coalescedHub A key hub k g ((A′).graph.attach p)=hub (key (A.graph.attach p)).1 :=
  coalesced_at_hub A key hub k g _

theorem coalesced_hubs (oldHub : A.graph.Site→Bool) (inc : HubIncidence A oldHub)
    (same : ∀u,hub (key u).1=oldHub u) : HubIncidence A′ (coalescedHub A key hub k g) := by
  constructor
  · intro e he
    change coalescedHub A key hub k g (address A key hub k g (A.graph.src e.val))=false ∧
      coalescedHub A key hub k g (address A key hub k g (A.graph.dst e.val))=false
    simp only [coalesced_at_hub,same]
    exact inc.inside e.val (Finset.mem_filter.mp he).2
  · intro e he
    change coalescedHub A key hub k g (address A key hub k g (A.graph.src e.val))≠
      coalescedHub A key hub k g (address A key hub k g (A.graph.dst e.val))
    simp only [coalesced_at_hub,same]
    have in_univ (ft : Fintype (A′).graph.Edge) : e ∈ @Finset.univ _ ft := @Finset.mem_univ _ ft e
    exact inc.outside e.val fun h => he (Finset.mem_filter.mpr ⟨in_univ _, h⟩)
/-- Coarsening equal-prefix hubs cannot absorb a cable between opposite marks. -/
theorem coalesced_tether_image (oldHub : A.graph.Site→Bool) (inc : HubIncidence A oldHub)
    (same : ∀u,hub (key u).1=oldHub u) (e : A.graph.Edge) (old : e∉A.core) :
    ∃t : (A′).graph.Edge,t∉(A′).core ∧ (A′).graph.width t=A.graph.width e ∧
      (A′).graph.src t=address A key hub k g (A.graph.src e) ∧ (A′).graph.dst t=address A key hub k g (A.graph.dst e) := by
  have cross : address A key hub k g (A.graph.src e)≠address A key hub k g (A.graph.dst e) := by
    intro eq
    have flags := congrArg (coalescedHub A key hub k g) eq
    simp only [coalesced_at_hub,same] at flags
    exact inc.outside e old flags
  let t : (A′).graph.Edge := ⟨e,cross⟩
  exact ⟨t,fun ht=>old (Finset.mem_filter.mp ht).2,rfl,rfl,rfl⟩
end Coalesced

section Pieces
variable (A : MarkedWorld F d P bits) (q : ℕ) (m : A.graph.Edge→ℕ) (fit : ∀e∈A.core,A.graph.width e=m e*q)
variable (hub : A.graph.Site→Bool)
local notation "A′" => A.pieces q m fit

omit [Field F] in
theorem pieces_pin_hub (p : P) : hub ((A′).graph.attach p)=hub (A.graph.attach p) := rfl

omit [Field F] in
theorem pieces_hubs (inc : HubIncidence A hub) : HubIncidence A′ hub := by
  constructor
  · intro e he
    exact inc.inside _ ((DescentCableUnbundling.mem_nextCore A.graph A.core m q e).mp he)
  · intro e he
    exact inc.outside _ (mt (DescentCableUnbundling.mem_nextCore A.graph A.core m q e).mpr he)
omit [Field F] in
/-- The one old tether is still a single edge after unbundling every marked core cable. -/
theorem pieces_tether_image (e : A.graph.Edge) (old : e∉A.core) :
    ∃t : (A′).graph.Edge,t∉(A′).core ∧ (A′).graph.width t=A.graph.width e ∧
      (A′).graph.src t=A.graph.src e ∧ (A′).graph.dst t=A.graph.dst e := by
  let t : (A′).graph.Edge := .inl ⟨e,old⟩
  exact ⟨t,mt (DescentCableUnbundling.mem_nextCore A.graph A.core m q t).mp old,rfl,rfl,rfl⟩
end Pieces

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
