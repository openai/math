import OAI.Hierarchy.DescentPackedMatchRails
import OAI.Hierarchy.DescentPackedMatchPanelSource
import OAI.Hierarchy.DescentPackedMatchFuture
import OAI.Hierarchy.DescentPackedMatchPrepareSpace
import OAI.Hierarchy.DescentPackedMatchPrepareArrangement

namespace OAI
/-! # Both parts of the ordinary matcher in one native execution -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalEpochDecoder DescentKernelHistory.BitDescription DescentPackedColony
open scoped Classical Fin.CommRing BigOperators
open DescentSixParty.StarKeys
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
attribute [local irreducible] Gather.ROM.after Gather.ROM.machine Gather.ROM.ticks Prepare.ROM.after ProtocolRAM.result
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "rankOf" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "names" => cableNames k rankOf
local notation "peers" => rotor A rankOf
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "p" => 2*A.cap
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap ((nativeAddress he A.stage) ((scanHomeAt he A.stage) u)).2+((scanColorAt he A.stage) u).toNat)
    (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "R" => M*(s).pairs
local notation "slotOf" => slot he A groups hosts hm


variable (P₀ : Ports A.degree) (romBase unit seats : ℕ)
    (act : Bank) (vals : Fin (2^k)→Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap a M H G
local notation "maskBits" => Prepare.bits H G M
local notation "shapeBits" => Prepare.ROM.headBits H A.degree
local notation "C" => Prepare.ROM.chart romBase A.degree a M maskBits act vals wire
local notation "Z" => Prepare.ROM.roster romBase k A.degree A.cap a M H G shapeBits P₀.roster
local notation "statics" => Prepare.staticWords k A.degree A.cap a M H G
local notation "stamp" => Prepare.ROM.program w romBase k A.degree A.cap a short M H G
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "rowBits" => Prepare.bits H G M
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "ps" => Prepare.passes C Z base H G M A.degree
local notation "wins" => Prepare.gatedBank (k:=k) base H G M A.degree rowBits
local notation "marked" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree rowBits
local notation "field" => Gather.expr wins marked {P₀ with roster:=outB} H
local notation "plan" => Gather.ROM.place s short r A.degree p K H G M unit nextBase seats
local notation "E" => Gather.ROM.machine s short r A.degree p A.cap K H G M unit nextBase seats w field

include coord named fit winner df in
theorem run_rails_observed (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (m : Memory w) (rs : Fin H→Fin A.degree→Option (Fin H))
    (neighbors : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (sources : Accessible P₀ act H G M w romBase)
    (inputBanks : Prepare.ROM.OldRoom act vals wire P₀.roster H G A.degree M w romBase)
    (signedUnit : DescentSignedCableCodec.width A.degree A.cap≤unit)
    (raster : Reads act (Prepare.actors A groups hosts) M m)
    (published : Fin H→Fin G→Fin r→Cell a)
    (liveWin : ∀u,published (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=win (A.pos u) (A.block u))
    (selected : ∀x,Reads (vals x) (fun h g=>published h g x) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups hosts x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (large : Gather.matchUnit s short r A.degree p≤unit) (bitsFit : unit*M≤w/2) (room : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j<(plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit R stream j).val:Word w)) :
    let warm:=Prepare.ROM.after romBase k A.degree A.cap a short M H G m
    let endState:=Gather.ROM.after s short r A.degree p A.cap K H G M unit nextBase seats field (ProtocolRAM.result ps warm)
    let code:=((stamp).seq (ProtocolRAM.program w ps)).seq E
    let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
    code.Exec m endState (((4+10*statics)+clock ps)+Gather.ROM.ticks s short r A.degree p K H G M unit nextBase seats field) ∧
      (∀i,endState ((plan).layout.topology.base+i.val)=((keys i).val:Word w)) ∧
      ((∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i) → ∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃i : Fin (s).pairs,i.val=j ∧ digit (s).digit (finProdFinEquiv ((slotOf c).2,i)).val (endState ((plan).layout.out+(slotOf c).1.val)).val=
          DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      (∀i,i < romBase ∨ (plan).endAddr ≤ i → endState i=m i) ∧ CheapCode code ∧
      Rails {P₀ with roster:=outB} wins marked real (hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding)))
        M nextBase endState ∧
      Gather.ROM.DonorWord (M:=M) (Gather.ROM.donorExpr s short r A.degree p K H G M unit nextBase seats field)
        (plan).source.base real endState := by
  have shortUnit : short≤unit :=
    (Nat.le_add_left short (short*«fields» r A.degree p)).trans ((le_max_left ..).trans large)
  have keyRoom : M*max (DescentSignedCableCodec.width A.degree A.cap) short≤w/2 := by
    calc
      _ ≤ M*unit := Nat.mul_le_mul_left M (max_le signedUnit shortUnit)
      _ = unit*M := Nat.mul_comm ..
      _ ≤ _ := bitsFit
  have oneLane : short≤unit*M := shortUnit.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left unit hm)
  have range : max H A.degree<2^w :=
    max_lt (sources.offRoom.trans_lt sources.offsets.2.1)
      (df.trans_le (Nat.pow_le_pow_right (by decide) ((oneLane.trans bitsFit).trans (Nat.div_le_self ..))))
  have rawAbove : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have endAbove : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have stageBelow : Prepare.stop k H G M A.degree A.cap base≤nextBase :=
    (Nat.le_add_right ..).trans (le_max_left ..)
  obtain ⟨separated,prepRoom,sortRoom⟩:=Prepare.ROM.arranged romBase k A.degree A.cap a short M H G w act vals wire P₀.roster
    inputBanks keyRoom range (stageBelow.trans_lt (rawAbove.trans_lt (endAbove.trans_lt room)))
  have oldBase : romBase≤base := (Nat.le_add_right ..).trans separated
  have initial : Accessible P₀ act H G M w base := by
    have up {b : Bank} (low : b.Fits w romBase) : b.Fits w base:=⟨low.1,low.2.1,low.2.2.trans oldBase⟩
    exact ⟨fun i=>up (sources.ids i),sources.idsRoom,up sources.roster,sources.rosterRoom,up sources.offsets,sources.offRoom,
      up sources.chunks,sources.chunkRoom,up sources.source,sources.srcRoom⟩
  obtain ⟨first,own,old,ports,early,cheap⟩:=Prepare.ROM.from_published A native S ready groups hosts win P₀ outB
    romBase maskBits shapeBits rowBits act vals wire published liveWin m rs neighbors prepRoom sortRoom separated
    ((Nat.add_le_add_left sources.srcRoom _).trans sources.source.2.2)
    (fun x=>(Nat.add_le_add_left (inputBanks.winner x).2 _).trans (inputBanks.winner x).1.2.2)
    (fun x j=>(Nat.add_le_add_left (inputBanks.signed x j).2 _).trans (inputBanks.signed x j).1.2.2)
    (fun j=>(Nat.add_le_add_left (sources.idsRoom j) _).trans (sources.ids j).2.2)
    ((Nat.add_le_add_left sources.rosterRoom _).trans sources.roster.2.2)
    ((Nat.add_le_add_left sources.offRoom _).trans sources.offsets.2.2)
    ((Nat.add_le_add_left sources.chunkRoom _).trans sources.chunks.2.2) raster selected cables mounted
  obtain ⟨access,mf,mr,prev⟩:=Prepare.space (k:=k) (cap:=A.cap) P₀ base act initial (rawAbove.trans_lt (endAbove.trans_lt room))
  have keeps (i : ℕ) : ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m) ((plan).raw.base+i)=m ((plan).raw.base+i) :=
    early _ (.inr (prev.trans (rawAbove.trans (Nat.le_add_right ..))))
  obtain ⟨second,rows,profile_,low,cheap'⟩:=ordinary_run_observed A native S ready (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
    win he groups hosts hm coord named fit winner df profile choice stream wins marked {P₀ with roster:=outB}
    unit nextBase seats (ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m)) large bitsFit room ports access mf mr own old cap (fun i hi=>(keeps i).trans (raw i hi))
  have before : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
  have issuedRails : Rails {P₀ with roster:=outB} wins marked real
      (hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))) M nextBase
      (ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m)) :=
    ⟨access,mf,mr,own,old,ports,gathered_fields A native S ready names win peers groups hosts
      (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
      (DescentGroupPeerOrder.rotor_group A (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))
      wins marked {P₀ with roster:=outB} nextBase (ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m)) ports access mf mr own old⟩
  have word:=Gather.ROM.panel_source s short r A.degree p A.cap K H G M unit nextBase seats w field real (ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m))
    large bitsFit room (early_expr wins marked {P₀ with roster:=outB} nextBase access mf) issuedRails.fieldsRead
  refine ⟨?_,rows,profile_,?_,cheap_seq cheap cheap',issuedRails.moved ⟨0,Nat.two_pow_pos k⟩ low,word⟩
  · intro P₁ R₁ K₁ machine
    exact Procedure.Exec.then first second machine
  · intro i outside
    rcases outside with lo|hi
    · exact (low i (lo.trans_le (oldBase.trans before))).trans (early i (.inl lo))
    · exact (Gather.ROM.future s short r A.degree p A.cap K H G M unit nextBase seats field (ProtocolRAM.result ps (Prepare.ROM.after romBase k A.degree A.cap a short M H G m)) i hi).trans
        (early i (.inr (stageBelow.trans (rawAbove.trans (endAbove.trans hi)))))

include coord named fit winner df in
theorem run_rails (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i)
    (m : Memory w) (rs : Fin H→Fin A.degree→Option (Fin H))
    (neighbors : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (sources : Accessible P₀ act H G M w romBase)
    (inputBanks : Prepare.ROM.OldRoom act vals wire P₀.roster H G A.degree M w romBase)
    (signedUnit : DescentSignedCableCodec.width A.degree A.cap≤unit)
    (raster : Reads act (Prepare.actors A groups hosts) M m)
    (published : Fin H→Fin G→Fin r→Cell a)
    (liveWin : ∀u,published (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=win (A.pos u) (A.block u))
    (selected : ∀x,Reads (vals x) (fun h g=>published h g x) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups hosts x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (large : Gather.matchUnit s short r A.degree p≤unit) (bitsFit : unit*M≤w/2) (room : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j<(plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit R stream j).val:Word w)) :
    let warm:=Prepare.ROM.after romBase k A.degree A.cap a short M H G m
    let endState:=Gather.ROM.after s short r A.degree p A.cap K H G M unit nextBase seats field (ProtocolRAM.result ps warm)
    let code:=((stamp).seq (ProtocolRAM.program w ps)).seq E
    let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
    code.Exec m endState (((4+10*statics)+clock ps)+Gather.ROM.ticks s short r A.degree p K H G M unit nextBase seats field) ∧
      (∀i,endState ((plan).layout.topology.base+i.val)=((keys i).val:Word w)) ∧
      (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃i : Fin (s).pairs,i.val=j ∧ digit (s).digit (finProdFinEquiv ((slotOf c).2,i)).val (endState ((plan).layout.out+(slotOf c).1.val)).val=
          DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      (∀i,i < romBase ∨ (plan).endAddr ≤ i → endState i=m i) ∧ CheapCode code ∧
      Rails {P₀ with roster:=outB} wins marked real (hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding)))
        M nextBase endState ∧
      Gather.ROM.DonorWord (M:=M) (Gather.ROM.donorExpr s short r A.degree p K H G M unit nextBase seats field)
        (plan).source.base real endState := by
  obtain ⟨cpu,top,rows,frame_,cost,rails,donor⟩:=run_rails_observed A native S ready win he groups hosts hm coord named fit winner df profile P₀ romBase unit seats act vals wire choice stream m rs neighbors sources inputBanks signedUnit raster published liveWin selected cables mounted large bitsFit room cap raw
  exact ⟨cpu,top,rows pins,frame_,cost,rails,donor⟩

include coord named fit winner df in
theorem run (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i)
    (m : Memory w) (rs : Fin H→Fin A.degree→Option (Fin H))
    (neighbors : ∀h j,j∈(List.ofFn (rs h)).filterMap id ↔ ∃v u : V,h=hosts v ∧ j=hosts u ∧ v∈A.near u)
    (sources : Accessible P₀ act H G M w romBase)
    (inputBanks : Prepare.ROM.OldRoom act vals wire P₀.roster H G A.degree M w romBase)
    (signedUnit : DescentSignedCableCodec.width A.degree A.cap≤unit)
    (raster : Reads act (Prepare.actors A groups hosts) M m)
    (published : Fin H→Fin G→Fin r→Cell a)
    (liveWin : ∀u,published (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=win (A.pos u) (A.block u))
    (selected : ∀x,Reads (vals x) (fun h g=>published h g x) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups hosts x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (large : Gather.matchUnit s short r A.degree p≤unit) (bitsFit : unit*M≤w/2) (room : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j<(plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit R stream j).val:Word w)) :
    let warm:=Prepare.ROM.after romBase k A.degree A.cap a short M H G m
    let endState:=Gather.ROM.after s short r A.degree p A.cap K H G M unit nextBase seats field (ProtocolRAM.result ps warm)
    let code:=((stamp).seq (ProtocolRAM.program w ps)).seq E
    let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
    code.Exec m endState (((4+10*statics)+clock ps)+Gather.ROM.ticks s short r A.degree p K H G M unit nextBase seats field) ∧
      (∀i,endState ((plan).layout.topology.base+i.val)=((keys i).val:Word w)) ∧
      (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃i : Fin (s).pairs,i.val=j ∧ digit (s).digit (finProdFinEquiv ((slotOf c).2,i)).val (endState ((plan).layout.out+(slotOf c).1.val)).val=
          DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      (∀i,i < romBase ∨ (plan).endAddr ≤ i → endState i=m i) ∧ CheapCode code := by
  obtain ⟨exec,top,values,frame,cheap,_⟩:=run_rails A native S ready win he groups hosts hm coord named fit winner
    df profile P₀ romBase unit seats act vals wire choice stream pins m rs neighbors sources inputBanks signedUnit raster
    published liveWin selected cables mounted large bitsFit room cap raw
  exact ⟨exec,top,values,frame,cheap⟩

/-- Two distinct signed old wires back each surviving pair. -/
theorem capacity_of_edges (seats : ℕ) (paid : Fintype.card W.graph.Edge≤2*seats) :
    Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats := by
  let pick:=colorPick W.graph W.core home color A.cap
  have inj:=Fintype.card_le_of_injective pick pick.injective
  change Fintype.card (NativePair W.graph W.core home color A.cap × Fin 2)≤_ at inj
  rw [Fintype.card_prod,Fintype.card_fin] at inj
  omega

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepared

end OAI
