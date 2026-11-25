import OAI.Hierarchy.DescentDonorRetainedRegister
import OAI.Hierarchy.DescentNativeDonorTape
import OAI.Hierarchy.DescentPrivateDepotPort
import OAI.Hierarchy.DescentPrivateGatherPhase

namespace OAI
/-! # Date at which the native gather fills the ordinary ticket's actual donor bank -/


namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
attribute [local irreducible] Stage.nativeParts physicalRows DepotRAM.chip DepotRAM.after DepotRAM.program
  DepotRAM.output packDonor StarKeys.nativeKey OrdinaryLink.donorKey OrdinaryLink.measuredDonors

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords (M:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ) (issued : Memory w)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm
  profile dest issued roster (A).hub lay bytes

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (issued (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

local notation "M" => port.groupsPerWord

include named fit winner df order sumSize stored mounted birth in
/-- The only data read from the preceding program are the six bounded physical
fields. The stage's signed widths, topology and fresh six-party atoms determine
every cell consumed by the next private-register opcode. -/
theorem depot_date_board
    (tabs : DepotRAM.Tables6) (inputs : DepotRAM.Fields) (rom : DescentSIMDLookup.Banks) (mem : Memory w)
    (fitCode : DepotRAM.FitsInputs fmt tabs inputs M rom.source.base w)
    (endAt : DescentSIMDLookup.Fits rom (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt) M H (S.groupCount i) w (port.base+1))
    (static : DepotRAM.Fixed fmt tabs M mem) (loaded : DepotRAM.Loaded fmt inputs measured M mem)
    (literal : ∀pin : Cell (DepotRAM.totalBits fmt*M) ⊕ Fin (H*chunks (S.groupCount i) M),∀bit : Fin w,
      wordBits w (mem (fixedAddr rom pin)) bit=wordBits w (fixedWord (DepotRAM.output fmt (A).cap profile G.b slots) pin) bit)
    (earlier : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let phase:=DepotRAM.phase tabs inputs rom (port.base+1) H (S.groupCount i) M w
    (phase.Runs mem ∧ (∀a,a<rom.source.base→phase.image mem a=mem a) ∧
      MeterPort.Pins ticket port (phase.image mem)) ∧
      DescentPackedColony.Reads rom.source (fun h j=>DepotRAM.combine fmt (measured h j)) M (phase.image mem) := by
  intro phase
  refine ⟨?_,DepotRAM.retained fmt tabs inputs rom (port.base+1) fitCode endAt measured mem static loaded⟩
  · have chart : ticket.donorChart.col=addr := eq_of_heq ticket.donorChart.native
    have key : ticket.donorKey=StarKeys.nativeKey W.graph W.core home color (T).cap addr ticket.donorChart.same lay := by
      unfold OrdinaryLink.donorKey IssuedDonorChart.key
      exact congrArg (fun loc => StarKeys.nativeKey W.graph W.core home color (T).cap loc ticket.donorChart.same lay) chart
    obtain ⟨exec_,read,low,_⟩:=Stage.donor_tape A native S prior.valid rank win he grp hosts hm
      prior.valid.coordinates named fit winner df order profile b m sumSize stored choice dest issued roster mounted (A).hub
      ticket.donorChart.same lay birth slots bytes (T).k (port.base+1) (A).capPos tabs inputs rom mem fitCode endAt static loaded literal earlier
    refine ⟨exec_,low,?_⟩
    have seen := ticket.measuredDonors_publicHub port.vertex
    have aligned := seen.trans (congrArg (fun key₀ => physicalRows (a:=bytes) (hCode:=(T).k) A S prior.valid
      native hosts grp (rr).pick lay (rr).pack key₀ (fun v => (A).hub v.2) slots ((rr).profile choice)
      (relative (rr).pick lay (rr).pack key₀)) (congrArg (fun (f : _ ↪ _) => f.toFun) key))
    intro ix
    exact (read ix).trans (congrArg (fun vals : Fin H → Fin (S.groupCount i * 2^k * (A).cap) →
        Donor 3 bytes (normBits (A).cap G.b G.C G.k) =>
      ((data («M»:=port.groupsPerWord*(2^k*(A).cap)) (fun v j => packDonor (vals v j)) ix).val:Computability.VPVNP.BurstRAM.Word w)) aligned.symm)

include named fit winner df order sumSize stored mounted birth in
theorem depot_date
    (tabs : DepotRAM.Tables6) (inputs : DepotRAM.Fields) (rom : DescentSIMDLookup.Banks) (mem : Memory w)
    (fitCode : DepotRAM.FitsInputs fmt tabs inputs M rom.source.base w)
    (endAt : DescentSIMDLookup.Fits rom (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt) M H (S.groupCount i) w (port.base+1))
    (static : DepotRAM.Fixed fmt tabs M mem) (loaded : DepotRAM.Loaded fmt inputs measured M mem)
    (literal : ∀pin : Cell (DepotRAM.totalBits fmt*M) ⊕ Fin (H*chunks (S.groupCount i) M),∀bit : Fin w,
      wordBits w (mem (fixedAddr rom pin)) bit=wordBits w (fixedWord (DepotRAM.output fmt (A).cap profile G.b slots) pin) bit)
    (earlier : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let phase:=DepotRAM.phase tabs inputs rom (port.base+1) H (S.groupCount i) M w
    phase.Runs mem ∧ (∀a,a<rom.source.base→phase.image mem a=mem a) ∧ MeterPort.Pins ticket port (phase.image mem) := by
  exact (depot_date_board ticket port win hm named fit winner df order profile b m sumSize stored dest issued roster mounted
    birth tabs inputs rom mem fitCode endAt static loaded literal earlier).1

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
