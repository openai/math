import OAI.Hierarchy.DescentPackedFieldLanePrice
import OAI.Hierarchy.DescentPackedPrivateChronology
import OAI.Hierarchy.DescentRawCableRoster

namespace OAI
/-! # The actual old, arm and supply panel advances the written private register -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section

set_option quotPrecheck false
set_option maxHeartbeats 1000000

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} (path : Path start source)
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable {H a lanesPerWord : ℕ} (vertex : source.V↪Fin H)
local notation "A" => source.placement
local notation "r" => BitDescription.scannedRows he T
local notation "N" => rawGraph he T c
local notation "fromOwner" => (originalId ((T.result he).state c).graph.Site) ∘ rawInput he T c ((r).state c)
local notation "owner" => rawOwner he T c n ((r).state c) (originalId _)
local notation "samples" => Live A (r).pick
local notation "units" => normalized A ((r).profile c)
local notation "rank" => slot A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _) (r).pick
local notation "width" => span (S.groupCount i) k (A).cap
variable (roomUnit : ∀ e : Live source.placement (BitDescription.scannedRows he T).pick,
  normalized source.placement ((BitDescription.scannedRows he T).profile c) e.val < 2^a)

/-- Both equalities are the genuine quotient comparisons, at the actual chronological
donor/motif slot. A missing source or absent lane contains the all-zero output cell. -/
def OrdinaryLink.privatePanel (_ : OrdinaryLink source he T c n target) : Fin H→Fin width→Cell (2+a) :=
  place rank (fun e : samples=>cell
    (decide (fromOwner ((N).src e.val)=fromOwner ((N).dst e.val)))
    (decide (owner ((N).src e.val)=owner ((N).dst e.val))) ⟨units e.val,roomUnit e⟩)

theorem OrdinaryLink.privatePanel_fee :
    (∑v,∑j,score (ticket.privatePanel vertex roomUnit v j))*T.z=
      ∑e:(N).Edge,if owner ((N).src e)=owner ((N).dst e) then (N).width e else 0 := by
  let donor:=GadgetNetwork.physical W.graph (r).pick (branchWidth G (fun _=>(A).z) ((r).profile c))
  have fit (t : (r).pairs×Fin 2) : W.graph.width ((r).pick t)=(A).z*G.b := ((r).fit t.1 t.2).trans (congrArg (·*G.b) ticket.quantum)
  have measured:=stage_fee A S source.valid (source.order.trans Fin.valEmbedding) vertex (Equiv.refl _) (r).pick
    ((r).profile c) fit fromOwner owner roomUnit
  have same (e : (N).Edge) : donor.width e=(N).width e := by
    rcases e with e|⟨i,j⟩|⟨i,j⟩
    · rfl
    · rfl
    · change (A).z*_=T.z*_
      rw [ticket.quantum]
  calc
    _ = (∑v,∑j,score (ticket.privatePanel vertex roomUnit v j))*(A).z := congrArg _ ticket.quantum
    _ = ∑e:(N).Edge,if owner ((N).src e)=owner ((N).dst e) then donor.width e else 0 := measured
    _ = _ := Finset.sum_congr rfl (fun e _=>by rw [same])

/-- A single real packed score and prefix pass consumes the actual stage slots and
preserves the global held invariant. Only its authenticated native ROM and packed
input reads are required from the preceding row writer. -/
theorem Path.Held.issued_panel (L : Layout) (C : Counters) (m : Memory bw)
    (held : path.Held C.prior m) (room : L.Room bw H width lanesPerWord) (space : C.scaling.Room bw)
    (positive : 0<lanesPerWord) (rows : Layout.count H width lanesPerWord≤L.source.size)
    (bitsFit : L.rom.bits=(2+a)*lanesPerWord)
    (ready : DescentPackedScore.Input (M:=lanesPerWord) L.source L.rom score (ticket.privatePanel vertex roomUnit) m)
    (atEnd : C.words=L.starts+Layout.count H width lanesPerWord) (prior : C.prior<L.words) :
    (DescentPackedPrivateAccumulator.program L C bw H width lanesPerWord T.z).Exec m (DescentPackedPrivateAccumulator.image L C H width lanesPerWord T.z m)
      (Layout.billed H width lanesPerWord+C.scaling.steps T.z) ∧
    (path.ordinary ticket).Held C.out (DescentPackedPrivateAccumulator.image L C H width lanesPerWord T.z m) :=
  Path.Held.packed_ordinary path ticket L C (ticket.privatePanel vertex roomUnit) m held room space
    positive rows bitsFit ready atEnd prior (ticket.privatePanel_fee vertex roomUnit)

local notation "cellBits" => normBits source.placement.cap G.b G.C G.k
local notation "panelLanes" => lanes bw (2+cellBits)

/-- The fixed output-cell width follows from the local signed port budget at the
actual donor. It includes the largest possible motif-profile coordinate. -/
def OrdinaryLink.issuedPanel : Fin H→Fin width→Cell (2+cellBits) :=
  ticket.privatePanel vertex (fun e : Live source.placement (BitDescription.scannedRows he T).pick =>
      normalized_fits source.placement S source.valid ((BitDescription.scannedRows he T).profile c) e.val)

/-- The native update uses as many packed cells as fit in half a CPU word. The
real old/arm/supply roster supplies every input to the fee equality. -/
theorem Path.Held.issued_packed (L : Layout) (C : Counters) (m : Memory bw)
    (held : path.Held C.prior m) (room : L.Room bw H width panelLanes) (space : C.scaling.Room bw)
    (wide : 2*(2+cellBits)≤bw) (rows : Layout.count H width panelLanes≤L.source.size)
    (bitsFit : L.rom.bits=(2+cellBits)*panelLanes)
    (ready : DescentPackedScore.Input (M:=panelLanes) L.source L.rom score (ticket.issuedPanel vertex) m)
    (atEnd : C.words=L.starts+Layout.count H width panelLanes) (prior : C.prior<L.words) :
    (DescentPackedPrivateAccumulator.program L C bw H width panelLanes T.z).Exec m (DescentPackedPrivateAccumulator.image L C H width panelLanes T.z m)
      (Layout.billed H width panelLanes+C.scaling.steps T.z) ∧
    (path.ordinary ticket).Held C.out (DescentPackedPrivateAccumulator.image L C H width panelLanes T.z m) ∧
    (Layout.billed H width panelLanes+C.scaling.steps T.z)*bw≤
      40*(bw+H*bw+4*H*width*(2+cellBits))+(56+4*ProtocolRAMPortScale.bitWidth T.z)*bw ∧
    2^((2+cellBits)*panelLanes)≤2^(bw/2) := by
  have unitPos : 0<2+cellBits := Nat.add_pos_left (by decide) _
  have pos : 0<panelLanes := (occupancy bw (2+cellBits) unitPos wide).1
  obtain ⟨exec,next⟩ := Path.Held.issued_panel path ticket vertex
    (fun e : Live source.placement (BitDescription.scannedRows he T).pick =>
      normalized_fits source.placement S source.valid ((BitDescription.scannedRows he T).profile c) e.val) L C m held room space pos rows bitsFit ready atEnd prior
  exact ⟨exec,next,DescentPackedPrivateAccumulator.tariff C bw H width (2+cellBits) T.z unitPos wide⟩

/-- The status resolver and the private counter share the producer's original lane
pitch. A narrower status is written per lane; its lookup bank is correspondingly smaller. -/
theorem Path.Held.issued_wide (full : ℕ) (inside : 2+cellBits≤full)
    (L : Layout) (C : Counters) (m : Memory bw) (held : path.Held C.prior m)
    (room : L.Room bw H width (lanes bw full)) (space : C.scaling.Room bw)
    (wide : 2*full≤bw) (rows : Layout.count H width (lanes bw full)≤L.source.size)
    (bitsFit : L.rom.bits=(2+cellBits)*lanes bw full)
    (ready : DescentPackedScore.Input (M:=lanes bw full) L.source L.rom score (ticket.issuedPanel vertex) m)
    (atEnd : C.words=L.starts+Layout.count H width (lanes bw full)) (prior : C.prior<L.words) :
    (DescentPackedPrivateAccumulator.program L C bw H width (lanes bw full) T.z).Exec m
      (DescentPackedPrivateAccumulator.image L C H width (lanes bw full) T.z m)
      (Layout.billed H width (lanes bw full)+C.scaling.steps T.z) ∧
    (path.ordinary ticket).Held C.out (DescentPackedPrivateAccumulator.image L C H width (lanes bw full) T.z m) ∧
    (Layout.billed H width (lanes bw full)+C.scaling.steps T.z)*bw≤
      40*(bw+H*bw+4*H*width*full)+(56+4*ProtocolRAMPortScale.bitWidth T.z)*bw ∧
    2^((2+cellBits)*lanes bw full)≤2^(bw/2) := by
  have fullPos : 0<full := (Nat.add_pos_left (by decide : 0<2) cellBits).trans_le inside
  have pos : 0<lanes bw full := (occupancy bw full fullPos wide).1
  obtain ⟨exec,next⟩ := Path.Held.issued_panel path ticket vertex
    (fun e : Live source.placement (BitDescription.scannedRows he T).pick =>
      normalized_fits source.placement S source.valid ((BitDescription.scannedRows he T).profile c) e.val) L C m held room space pos rows bitsFit ready atEnd prior
  exact ⟨exec,next,DescentPackedPrivateAccumulator.tariff_wide C bw H width (2+cellBits) full T.z fullPos inside wide⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
