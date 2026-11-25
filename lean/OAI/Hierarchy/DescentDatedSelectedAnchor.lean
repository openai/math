import OAI.Hierarchy.DescentDatedMatcherRead
import OAI.Hierarchy.DescentDatedTerrainSibling
import OAI.Hierarchy.DescentPackedMatchDonorRead
import OAI.Hierarchy.DescentDonorSelection

namespace OAI
/-! # The old demand arm's true first donor, read from the earlier accepted pair -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
local notation "seat" => slot he A groups hosts hm
variable (b : ℕ) (m : Memory w) (sumSize : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i : Fin ((2^(k+1)*H)*chunks G M),
      m (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile)
        (Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap
          (spread groups hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))
variable (c : ScanColonies he A.stage)
local notation "num" => pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)
local notation "x" => inputs s A.cap (heap (addr c).2) (panel (addr c).1) (fun _=>0)


local notation "record" => donorWord s m b (seat c)
local notation "label" => fun (u : Pair) (side : Bool)=>rawTriple A native S ready names he c side (picked A he c u side) 0
local notation "picker" => colorPick W.graph W.core home color A.cap

include coord named fit winner df edgeOrder sumSize stored in
theorem match_record (side : Bool) (e : Pair) (j : Fin (s).pairs) :
    (record j 0=1 ∧ record j (matchColumn side)=label e side) ↔ (num e).val=j.val := by
  have read (u : Pair) (j : Fin (s).pairs) (at_ : (num u).val=j.val) :
      record j 0=1 ∧ record j (matchColumn side)=label u side := by
    obtain ⟨s',atS,live_,h,l⟩:=donor_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
      profile b m sumSize stored c u
    have same : s'=j:=Fin.ext (atS.trans at_)
    cases same
    exact ⟨live_,by cases side <;> first | exact h | exact l⟩
  constructor
  · rintro ⟨live_,found⟩
    obtain ⟨u,ordinal,_⟩:=(valid_iff A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
      profile b m sumSize stored c j).1 live_
    have same:=edge_handle A native S ready rank he c c side side (picked A he c u side) (picked A he c e side)
      rfl ((read u j ordinal).2.symm.trans found)
    simp only [picked_old] at same
    have pair:=congrArg Prod.fst ((picker).injective same)
    have eqn : u=e:=heq_iff_eq.mp (Sigma.mk.inj pair).2
    simpa only [eqn] using ordinal
  · exact read e j

include coord named fit winner df edgeOrder sumSize stored in
theorem matching_at_pair (side : Bool) (e : Pair) :
    ∃j,matchingRow record side (label e side)=some j ∧ record j 8=label e true ∧ record j 5=label e false := by
  obtain ⟨j,numAt,present,thick,thin⟩:=donor_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c e
  have exactRow:=match_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c side e
  cases chosen : matchingRow record side (label e side) with
  | none =>
    have witness:=decide_eq_true ((exactRow j).2 numAt.symm)
    exact False.elim (List.find?_eq_none.mp chosen j (List.mem_finRange j) witness)
  | some v =>
    have hit := List.find?_some
      («p» := fun j : Fin (s).pairs => decide (record j 0=1 ∧ record j (matchColumn side)=label e side)) chosen
    have eqn := (exactRow v).1 (of_decide_eq_true hit)
    have unique : v=j:=Fin.ext (eqn.symm.trans numAt.symm)
    subst v
    exact ⟨j,rfl,thick,thin⟩

include coord named fit winner df edgeOrder sumSize stored in
theorem selected_anchor (side : Bool) (e : Pair) :
    selectedAnchor record side (label e side)=some (label e true,if side then (1:ℕ) else 2) := by
  obtain ⟨j,read,first,_⟩:=matching_at_pair A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c side e
  simp [selectedAnchor,read,first]

include coord named fit winner df edgeOrder sumSize stored in
theorem selected_sibling (e : Pair) :
    DescentOperandPriorIncidence.TerrainAnchor.sibling record (label e true)=some (label e false) := by
  obtain ⟨j,read,_,second⟩:=matching_at_pair A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c true e
  simp [DescentOperandPriorIncidence.TerrainAnchor.sibling,read,second]

include coord named fit winner df edgeOrder sumSize stored in
theorem selected_donor_address (side : Bool) (e : Pair) :
    let original:=picked A he c e side
    let first:=picked A he c e true
    selectedAnchor record side (donorAddress A native S ready
      ⟨original.val,A.quantum_positive _ original.property.1⟩)=
      some (donorAddress A native S ready ⟨first.val,A.quantum_positive _ first.property.1⟩,
        if side then (1:ℕ) else 2) := by
  dsimp only
  simpa only [source_handle_eq A native S ready rank he] using
    selected_anchor A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m
      sumSize stored c side e

include coord named fit winner df edgeOrder sumSize stored in
theorem selected_absent (side : Bool) (key : ℕ) (miss : ∀u : Pair,label u side≠key) :
    selectedAnchor record side key=none := by
  unfold selectedAnchor
  suffices empty : matchingRow record side key=none by rw [empty];rfl
  apply List.find?_eq_none.mpr
  intro j _ hit
  obtain ⟨live_,hit_⟩:=of_decide_eq_true hit
  obtain ⟨u,numAt,_⟩:=(valid_iff A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c j).1 live_
  have entry:=(match_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c side u j).2 numAt
  exact miss u (entry.2.symm.trans hit_)

include coord named fit winner df edgeOrder sumSize stored in
theorem retarget_matched (side : Bool) (e : Pair) :
    retarget record true (label e side)=(label e true,if side then (1:ℕ) else 2) := by
  have chosen:=selected_anchor A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored c side e
  cases side with
  | true=>simp [retarget,chosen]
  | false=>
    have miss : ∀u : Pair,label u true≠label e false := by
      intro u eqn
      have same:=edge_handle A native S ready rank he c c true false (picked A he c u true)
        (picked A he c e false) rfl eqn
      simp only [picked_old] at same
      have bad:=congrArg Prod.snd ((picker).injective same)
      exact (by decide : (0:Fin 2)≠1) bad
    have empty:=selected_absent A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
      profile b m sumSize stored c true _ miss
    simp [retarget,empty,chosen]

include coord named fit winner df edgeOrder sumSize stored in
theorem retarget_unreplaced (q : DescentSharedCableNames.Stage.Positive A)
    (atRack : (addr c).1=A.pos (W.graph.src q.val))
    (miss : ∀ (u : Pair) (side : Bool),(picked A he c u side).val≠q.val) :
    retarget record true (donorAddress A native S ready q)=(donorAddress A native S ready q,0) := by
  have empty (side : Bool) : selectedAnchor record side (donorAddress A native S ready q)=none := by
    apply selected_absent A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
      profile b m sumSize stored c side
    intro u hit
    exact miss u side ((source_handle_identifies A native S ready rank he q side c atRack _).1 hit)
  simp [retarget,empty]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
