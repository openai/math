import OAI.Hierarchy.DescentDatedOriginalRawWalk

namespace OAI
/-! # Actual old donors in the four-hop source chart of captured ordinary edges -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentCableDonorNames
open DescentHostDirectory DescentOrdinaryDonorHalo
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "names" => cableNames k rank
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "traffic" => nativeTraffic N W.core home
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "pick" => colorPick N W.core home color A.cap
local notation "Packs" => coloredPack N W.core home color A.cap
local notation "venue" => newSite N pick lay Packs
local notation "key" => nativeKey N W.core home color A.cap addr same lay

private theorem location_reverse {u v : J×V} (a : Address)
    (reached : location (rotor A rank) u a=some v) :
    u∈insert v (groupedNear A.near v) :=by
  unfold location at reached
  split at reached
  · cases Option.some.inj reached
    exact Finset.mem_insert_self _ _
  · split at reached
    · unfold rotor at reached
      split at reached
      next live =>
        cases Option.some.inj reached
        exact Finset.mem_insert_of_mem ((grouped_symmetric A.near A.symmetric u _).mp live.choose.property)
      next => contradiction
    · contradiction

private theorem around_next {s u v : J×V} {j : ℕ}
    (old : u∈around (groupedNear A.near) j s) (hop : v∈insert u (groupedNear A.near u)) :
    v∈around (groupedNear A.near) (j+1) s :=
  Finset.mem_biUnion.mpr ⟨u,old,hop⟩

/-- Reversing the two genuine old rotor moves and filling the two unused steps
gives membership in the clipped chart without assuming a numeric path. -/
theorem walked_donor {p : J×V} {walk_ : Walk} {x : Key (J×V)}
    (actual : walked (rotor A rank) p walk_ x) :
    p∈around (groupedNear A.near) 4 x.1 :=by
  have reached:=actual.1
  change ((location (rotor A rank) p (walk_.1,0,0)).bind _)=some x.1 at reached
  cases hop : location (rotor A rank) p (walk_.1,0,0) with
  | none => simp [hop] at reached
  | some middle =>
    simp only [hop,Option.bind_some] at reached
    have start : x.1∈around (groupedNear A.near) 0 x.1:=by simp [around]
    have one:=around_next A start (Finset.mem_insert_self _ _)
    have two:=around_next A one (Finset.mem_insert_self _ _)
    have three:=around_next A two (location_reverse A rank walk_.2 reached)
    exact around_next A three (location_reverse A rank _ hop)

variable {H : ℕ} (hosts : V↪Fin H) (roster : Fin H→Fin A.degree→Option (Fin H))
    (listed : ∀v y,y∈A.near v→∃j,roster (hosts v) j=some (hosts y))
local notation "accepted" => DescentHaloCompilation.atSource A.near hosts roster listed A.pos A.block coord key

include ready profile coord named fit winner df edgeOrder in
theorem raw_donor_membership (e : DescentRawCablePanel.Live A pick) :
    (N).src (anchor pick e.val)∈(accepted).member (venue (GadgetNetwork.source N e.val)) :=by
  obtain ⟨ports,_,actual⟩:=raw_parent_actual A native S ready rank win he coord named fit winner df edgeOrder
    profile same lay e
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,walked_donor A rank actual.src⟩

include ready profile coord named fit winner df edgeOrder in
theorem inherited_donor_membership (u : (N).Site) :
    u∈(accepted).member (venue (.inl u)) :=by
  let t : Fin (2*A.cap):=⟨0,by have pos:=A.capPos; omega⟩
  have actual:=prior_head A native S ready names win next he rank coord named fit winner
    (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay u t
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,walked_donor A rank actual⟩

include ready profile coord named fit winner df edgeOrder in
theorem birth_donor_membership (p : NativePair N W.core home color A.cap) (party : Fin 6) :
    (N).src (pick (p,0))∈(accepted).member (venue (.inr (p,party))) :=by
  have marked (q : NativePair N W.core home color A.cap) : pick (q,0)∈W.core := by
    rcases q with ⟨c,q⟩
    have eqn : (picked A he c q true).val = pick (⟨c,q⟩,0) := picked_old A he c q true
    exact (congrArg (fun e => e∈W.core) eqn).mp (picked A he c q true).property.1
  let donor : Positive:=⟨pick (p,0),A.quantum_positive _ (marked p)⟩
  obtain ⟨steps,_,actual⟩:=parent_born A native S ready rank win he coord named fit winner
    df edgeOrder profile same lay donor p rfl
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,walked_donor A rank (actual party)⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z)))
    (named : A.SiteNamed (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=
      1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (order : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)

open DescentSixParty.StarKeys DescentPacking
local notation "N" => W.graph
local notation "pick" => colorPick N W.core home color A.cap
local notation "packs" => coloredPack N W.core home color A.cap
variable (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e))
local notation "own" => nativeKey N W.core home color A.cap addr same lay
local notation "venue" => newSite N pick lay packs
local notation "left" e => (venue (GadgetNetwork.source W.graph (e).val))
local notation "anchor_" e => (⟨anchor pick (e).val,(e).property⟩:Positive)

include coord named fit winner df order in
theorem original_capture_donor (roster : Fin H→Fin A.degree→Option (Fin H))
    (listed : ∀v y,y∈A.near v→∃j,roster (hosts v) j=some (hosts y))
    (agrees : ∀v j,roster (hosts v) j=near (hosts v) j)
    (mapped : ∀(z : J×V) j,roster (hosts z.2) j=((rotor A rank) z j).map (fun t=>hosts t.2))
    (symmetric : ∀v v' j,roster v j=some v'→∃i,roster v' i=some v)
    (e : DescentRawCablePanel.Live A pick) (pitch outBits : ℕ) (room : breadth A.degree ≤ 2^outBits) :
    let u : DepotRAM.Material.Setup:=⟨profile,G.b,A.stage.k,DescentHostDegree.gainExponent 20 A.stage.Δ,slots,pitch,outBits⟩
    let accepted:=DescentHaloCompilation.atSource A.near hosts roster listed A.pos A.block coord own
    let donor:=W.graph.src (anchor_ e).val
    let seat : DepotRAM.Material.Seat fmt:=(A.block donor,out (anchor_ e),DescentCableDonorNames.role e.val)
    let h:=hosts (A.pos donor).2
    let g:=groups (A.pos donor).1
    let records:=nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m roster hub lay bytes h g
    let rev:=DescentHaloPackedRebase.digest (DepotRAM.Material.reverseEntries fmt roster h)
    let observation:=DepotRAM.Material.rawObserved fmt u records rev seat
    let inside : donor∈accepted.member (left e):=
      raw_donor_membership A native S ready rank win he coord named fit winner df order profile same lay
        hosts roster listed e
    (observation 4).val*2^k+(A.block donor).val=(accepted.slot (left e) ⟨donor,inside⟩).val :=by
  exact original_capture_slot A native S ready groups hosts win he hm profile dest m hub lay bytes slots
    coord named fit winner df order same roster listed agrees mapped symmetric e pitch outBits room
    (raw_donor_membership A native S ready rank win he coord named fit winner df order profile same lay
      hosts roster listed e)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
