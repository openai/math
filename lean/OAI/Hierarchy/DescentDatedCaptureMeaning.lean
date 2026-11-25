import OAI.Hierarchy.DescentDatedCaptureFields
import OAI.Hierarchy.DescentOrdinaryRawMass

namespace OAI
/-! # The two physical capture flags at the actual old outgoing ticket -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentHostDegree DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
set_option quotPrecheck false

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

local notation "cellBits" => normBits (A).cap G.b G.C G.k
local notation "donorCols" => S.groupCount i*2^k*(A).cap
local notation "gain" => gainExponent 20 T.Δ
local notation "shelf" => 2^DescentHostDegree.packExponent 20 T.Δ+2
local notation "readAt" => ticket.issuedPanel vertex

/-- Decode the two comparisons on the original raw source. A cable already
captured in the first quotient never contributes a second-capture observation. -/
theorem OrdinaryLink.capture_at (e : samples) :
    let f:=decide (fromOwner ((N).src e.val)=fromOwner ((N).dst e.val))
    let l:=decide (owner ((N).src e.val)=owner ((N).dst e.val))
    DepotRAM.Operand.datum true ((readAt) (rank e).1 (rank e).2)=f ∧
      DepotRAM.Operand.datum false ((readAt) (rank e).1 (rank e).2)=(!f && l) := by
  have found : ∃a : samples,rank a=((rank e).1,(rank e).2):=⟨e,rfl⟩
  have same:found.choose=e:=(rank).injective found.choose_spec
  simp only [OrdinaryLink.issuedPanel,OrdinaryLink.privatePanel,place,dite_eq_left found,same]
  exact DepotRAM.Operand.capture_values _

/-- The donor contains exactly the flags consumed by the two capture arms of the
five-field scalar resolver, also for a selected original, emitted arm or supply. -/
theorem OrdinaryLink.donor_captures (e : samples) :
    let idx:=finProdFinEquiv.symm (rank e).2
    let reportWord:=report T.k gain shelf (ticket.measuredDonors vertex (rank e).1 idx.1) idx.2
    let f:=decide (fromOwner ((N).src e.val)=fromOwner ((N).dst e.val))
    let l:=decide (owner ((N).src e.val)=owner ((N).dst e.val))
    DepotRAM.Operand.datum true reportWord=f ∧ DepotRAM.Operand.datum false reportWord=(!f && l) := by
  dsimp only
  rw [ticket.donor_words vertex (rank e).1 (rank e).2]
  exact ticket.capture_at vertex e

/-- The same register image has both capture flags clear at every absent source
or absent gadget role. This includes empty old incidences. -/
theorem OrdinaryLink.donor_captures_hole (h : Fin H) (j' : Fin width)
    (absent : ¬∃e : samples,rank e=(h,j')) :
    let pos:=finProdFinEquiv.symm j'
    let reportWord:=report T.k gain shelf (ticket.measuredDonors vertex h pos.1) pos.2
    DepotRAM.Operand.datum true reportWord=false ∧ DepotRAM.Operand.datum false reportWord=false := by
  dsimp only
  rw [ticket.donor_words vertex h j']
  simp only [OrdinaryLink.issuedPanel,OrdinaryLink.privatePanel,place,dite_eq_right absent]
  rw [←cell_zero cellBits]
  exact DepotRAM.Operand.capture_values _

end
end Hierarchy.DescentSixParty.Chronology

end OAI
