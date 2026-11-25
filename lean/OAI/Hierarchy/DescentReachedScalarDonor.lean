import OAI.Hierarchy.DescentReachedAtomHaloRAM
import OAI.Hierarchy.DescentReachedAtomFieldRAM
import OAI.Hierarchy.DescentSortedHaloRaster

namespace OAI
/-! # Actual sorted halo ports feeding previous-book and born-role operands -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack
local notation "M" => ticket.issued.measured_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => (deg+1)^4*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "hostRows" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching hostRows
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

theorem exact_host (v : cap.V) (z : Fin (Fintype.card cap.V)) : (∃j,hostRows (cap.vertex v) j=some z) ↔ ∃u∈(A).near v,cap.vertex u=z :=by
  have yes:∃u,cap.vertex u=cap.vertex v:=⟨v,rfl⟩
  simp only [hostRotor,dite_eq_left yes,cap.vertex.injective yes.choose_spec,Option.map_eq_some_iff]
  constructor
  · rintro ⟨j,u,hit,eqn⟩;exact ⟨u,(hostRoster_mem A (cap.vertex.trans Fin.valEmbedding) v u).2 ⟨j,hit⟩,eqn⟩
  · rintro ⟨u,h,eqn⟩;obtain ⟨j,atLocal⟩:=(hostRoster_mem A (cap.vertex.trans Fin.valEmbedding) v u).1 h;exact ⟨j,u,atLocal,eqn⟩

/-- Every occupied donor slot uses its actual old block and its previous
host's distinct coordinate in the four-hop native directory. -/
theorem actual_donor (label : C) (u : W.graph.Site) (here : u∈(halo).member label) :
    let i : Fin (breadth deg)×Fin (2^k) := finProdFinEquiv.symm ((halo).slot label ⟨u,here⟩)
    DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) i.1=some (cap.vertex ((A).pos u).2) ∧ i.2=(A).block u ∧ ((A).pos u).1=label.val.1.1 :=by
  let root:=label.val.1
  have belongs:(A).pos u∈around near 4 root:=(Finset.mem_filter.mp here).2
  have converted:=belongs;rw [show root=(root.1,root.2) from rfl,grouped] at converted
  obtain ⟨v,hit,arrived⟩:=Finset.mem_map.mp converted
  have same:(root.1,v)=(A).pos u:=arrived
  have member:((A).pos u).2∈around (A).near 4 root.2:=by rw [←same];exact hit
  let old:↥(around (A).near 4 root.2):=⟨((A).pos u).2,member⟩
  have aligned:∀g v z,name (g,v)<name (g,z) ↔ cap.vertex v<cap.vertex z:=by
    intro g v z
    change (finProdFinEquiv (g,cap.vertex v)).val < (finProdFinEquiv (g,cap.vertex z)).val ↔ (cap.vertex v).val < (cap.vertex z).val
    simp only [finProdFinEquiv_apply_val,Nat.add_lt_add_iff_right]
  have ranked: (Halo.fromRank (around near 4) name (around_room _ _ (A).stage.degree 4)).slot root ⟨(A).pos u,belongs⟩=
      (Halo.fromRank (around (A).near 4) (cap.vertex.trans Fin.valEmbedding) (around_room _ _ (A).degreeBound 4)).slot root.2 old:=by
    have matched:=group_slot (A).near cap.vertex (A).degreeBound name aligned root.2 root.1 old (A).stage.degree
    have siteEq : (A).pos u = (root.1,old.val) := Prod.ext (congrArg Prod.fst same).symm rfl
    have equal : (⟨(A).pos u,belongs⟩ : ↥(around near 4 root)) =
        ⟨(root.1,old.val),siteEq ▸ belongs⟩ := Subtype.ext siteEq
    exact (congrArg ((Halo.fromRank (around near 4) name (around_room _ _ (A).stage.degree 4)).slot root) equal).trans matched
  have unpair: (finProdFinEquiv.symm ((halo).slot label ⟨u,here⟩) : Fin (breadth deg)×Fin (2^k))=
      ((Halo.fromRank (around near 4) name (around_room _ _ (A).stage.degree 4)).slot root ⟨(A).pos u,belongs⟩,(A).block u) :=Equiv.symm_apply_apply ..
  dsimp only
  rw [unpair,ranked]
  exact ⟨sorted_slot (A).near cap.vertex hostRows (exact_host (cap:=cap)) (A).degreeBound root.2 old,rfl,(congrArg Prod.fst same).symm⟩

variable {a K : ℕ}
/-- This is the value supplied by `run_halo` for each scalar candidate before the venue filter. -/
def received (label : C) (bank : Block k→Fin (K+(A).cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell a)
    (j : Fin (Width bound K (A).cap)) : Cell a :=
  (DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) (DescentOrdinaryAtomFieldRAM.bookRoot deg k K (A).cap j)).elim 0
    (fun v=>bank (DescentOrdinaryAtomFieldRAM.bookBlock deg k K (A).cap j) (DescentOrdinaryAtomFieldRAM.bookItem deg k K (A).cap j) v label.val.1.1)

theorem received_at (label : C) (bank : Block k→Fin (K+(A).cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell a)
    (u : W.graph.Site) (h : u∈(halo).member label) (j : Fin (K+(A).cap*6)) :
    received ticket label bank (finProdFinEquiv ((halo).slot label ⟨u,h⟩,j))=bank ((A).block u) j (cap.vertex ((A).pos u).2) ((A).pos u).1 :=by
  obtain ⟨real,bl,gr⟩:=actual_donor ticket label u h
  let d : Fin (breadth deg*2^k) := (halo).slot label ⟨u,h⟩
  have p := (finProdFinEquiv (m:=breadth deg*2^k) (n:=K+(A).cap*6)).symm_apply_apply (d,j)
  let read (q : Fin (breadth deg*2^k) × Fin (K+(A).cap*6)) :=
    let t : Fin (breadth deg) × Block k := finProdFinEquiv.symm q.1
    (DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) t.1).elim 0
      (fun v => bank t.2 q.2 v label.val.1.1)
  refine (congrArg read p).trans ?_
  let here := (finProdFinEquiv.symm d : Fin (breadth deg) × Block k).2
  let stored (h : Option (Fin (Fintype.card cap.V))) := h.elim 0 (fun v => bank here j v label.val.1.1)
  refine (congrArg stored real).trans ?_
  exact (congrArg (fun x => bank x j (cap.vertex ((A).pos u).2) label.val.1.1) bl).trans
    (congrArg (fun g => bank ((A).block u) j (cap.vertex ((A).pos u).2) g) gr.symm)

local notation "roots_" => reachedHalo_members ticket
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "used" => fun j : (r).pairs=>(r).picked (j,0)
local notation "capK" => maxNodes arch.bit
local notation "x₁" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "x₂" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "ok₁" => fun v : (sel).graph.Site=>(by simp : ‖x₁ v‖≤1)
local notation "ok₂" => fun v : C=>(by simp : ‖x₂ v‖≤1)
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "first" => quotientBits stepGraph group x₁ ok₁ base
local notation "second" => quotientBits (quotient stepGraph group x₁ ok₁) addr x₂ ok₂ first
variable (prior : Local arch.bit)
local notation "oldRank" => bounded arch.bit prior
variable (oldBank : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (a*maxNodes arch.bit))
    (newBank : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell a)

def donorWord (x : Block k) (j : Fin (capK+(A).cap*6)) (v : Fin (Fintype.card cap.V)) (group_ : Fin (S.groupCount i)) : Cell a :=
  (finSumFinEquiv.symm j).elim (fun t=>(encode a capK).symm (oldBank x v group_) t)
    (fun pair=>let f:=finProdFinEquiv.symm pair;newBank x f.1 f.2 v group_)

/-- At every selected scalar position the physically fetched bank contains
its authentic source value. The excluded slots may hold arbitrary bytes. -/
theorem candidate_word (label : C) (node : (second label).Node) :
    let j:=short A native S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr x₁ x₂ ok₁ ok₂ halo (roots_).1 (roots_).2 oldRank label node
    received ticket label (donorWord arch oldBank newBank) j=rawFields (carried ticket arch oldBank label) (created ticket newBank label) j :=by
  intro j
  let f:=roster arch.bit (r).pick units stageLimit ((r).profile c) group addr x₁ x₂ ok₁ ok₂ label node
  let position:=book A native S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr halo (roots_).1 (roots_).2 oldRank label
  change received ticket label (donorWord arch oldBank newBank) (position f)=rawFields _ _ (position f)
  rcases f with ⟨⟨u|⟨i,j⟩,h⟩,scalar⟩
  · have supported:u∈(halo).member label:=h ▸ (roots_).1 u
    have found:donorAt halo label ((halo).slot label ⟨u,supported⟩)=some u:=(donorAt_eq halo label).2 ⟨supported,rfl⟩
    let slot := (halo).slot label ⟨u,supported⟩
    let item : Fin (capK+(A).cap*6) := finSumFinEquiv (Sum.inl (oldRank u scalar))
    change received ticket label (donorWord arch oldBank newBank) (finProdFinEquiv (slot,item)) =
      rawFields (carried ticket arch oldBank label) (created ticket newBank label) (finProdFinEquiv (slot,item))
    rw [received_at ticket label _ u supported item]
    simp only [donorWord,rawFields,item,Equiv.symm_apply_apply,Sum.elim_inl,carried,slot,found,Option.elim_some]
  · let u:=W.graph.src ((r).pick (i,0))
    have supported:u∈(halo).member label:=h ▸ (roots_).2 i j
    have found:donorAt halo label ((halo).slot label ⟨u,supported⟩)=some u:=(donorAt_eq halo label).2 ⟨supported,rfl⟩
    let slot := (halo).slot label ⟨u,supported⟩
    let edge := outgoingSlot A native S cap.valid (r).pick used i
    let item : Fin (capK+(A).cap*6) := finSumFinEquiv (Sum.inr (finProdFinEquiv (edge,j)))
    change received ticket label (donorWord arch oldBank newBank) (finProdFinEquiv (slot,item)) =
      rawFields (carried ticket arch oldBank label) (created ticket newBank label) (finProdFinEquiv (slot,item))
    rw [received_at ticket label _ u supported item]
    simp only [donorWord,rawFields,item,Equiv.symm_apply_apply,Sum.elim_inr,created,slot,found,Option.elim_some]

/-- The mask makes the entire packed output identical whenever the fetched
bytes agree at its actual occupied donors. -/
theorem pack_agrees {W K a : ℕ} (bits : Fin W→Cell 1) (left right : Fin W→Cell a)
    (same : ∀i,bits i≠0→left i=right i) :
    DescentPackedLocalAtoms.pack a W K (encode 1 W bits) (encode a W left)=DescentPackedLocalAtoms.pack a W K (encode 1 W bits) (encode a W right) :=by
  simp only [DescentPackedLocalAtoms.pack,Equiv.symm_apply_apply]
  apply congrArg (encode a K);funext t
  simp only [DescentPackedLocalAtoms.field]
  split
  · rename_i exists_;exact same _ exists_.choose_spec.1
  · rfl

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
