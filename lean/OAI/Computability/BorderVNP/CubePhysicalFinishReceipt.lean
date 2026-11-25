import OAI.Computability.BorderVNP.DiagonalPositiveFinishInput
import OAI.Computability.BorderVNP.CubePhysicalSignedClaim

/-! # The signed finish receipt for the parsed header of a physical path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open scoped BigOperators Classical

variable {l : ReportLayout} {n d blocks b h K s D B T w : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell] {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry (Fin l.parameters) (Fin l.gadgets))) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Fin l.gadgets)
    (words : PowerWords (Fin T) (Fin l.parameters) (Fin l.gadgets) B N tags)
    (label : Cell → Label (n+1) d) (team : Fin d → Fin T) (a : Path N cell n d blocks b h K s) (t : Fin T)
    (o : Orders tags words label team a t)
    (uses : PowerSlot (Fin T) (Fin l.parameters) B → UseRead)
    (cells : ∀ c : Cell, CellRead {v : N.Site // cell v = c} l.gadgets)
    (packets : Packet n d blocks × Vertex (n+1) → PacketRead)
    (reports : Cell → ReportCell l)
variable {reserve axes groups cap width : ℕ} (p : PositiveFields reserve axes groups cap T (l.parameters+l.gadgets) width)

local notation "rows" => physicalRow slot tags x pos words label team a
local notation "cs" => teamReports tags words label team a t o reports
local notation "Finish" => Evaluator.finishExpansion Evaluator.signedOccurrences

/-- The chronological operands whose addresses the team's selected-ID suffix
actually materializes, including all repeated table entries. -/
noncomputable abbrev receiptOperands (post : AfterTasks) (q : ReportCursor) (frame trueAddr : ℕ) : List Operand :=
  let earlier := cellOperands cs q
  let f := post.suffixFrame earlier.length o.nVertex l.zeroAddr l.parameters
  earlier++f.packetOperands frame trueAddr (fun i => (pathPacketID pos a (o.vertices i).val).val)

/-- A positive-header receipt at the actual post-cell state. The common claim is read
from the parsed bit bank. The local counts are obtained independently, from the
checked cells and native packet lookups of this same physical path. -/
noncomputable def finishReceipt (post : AfterTasks) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (state bank : Bank w) (mem selected : Memory w) (es : List (TeamRAM.Event w))
    (q : ReportCursor) (raw trueAddr : ℕ)
    (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      state mem es bank selected)
    (seed : SelectedSeed post pub mem raw (l.parameters+l.gadgets) T t.val width)
    (kept : ∀ k,k<post.start → k≠(pub 0).val+35 → selected k=mem k)
    (frame : (pub 0).val+101<post.start) (rawLo : (pub 0).val+45 ≤ raw)
    (rawHi : raw+T*(l.parameters+l.gadgets)*width ≤ post.start)
    (room : post.localBase+(l.parameters+l.gadgets)+T*(l.parameters+l.gadgets)+
      (l.parameters+l.gadgets)+(l.parameters+l.gadgets)+1+(l.parameters+l.gadgets)*w<2^w)
    (teamsFit : T<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (useBit : ∀ i,(uses i).bit=words.localUse (pathEdges slot a) (fun _ port => x port.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v=c}) g, (((cells c).observed v).filterMap Prod.snd).count g.val=
      (counters (tags v.val (pathEdges slot a v.val) (fun port => x port.val))).2 g)
    (source : UseOccurrence cs ≃ {i // routedPowerOwner tags words label team a i=t})
    (align : ∀ u, let i := (source u).val
      occurrencePair cs u = (i.2.1.val,if (uses i).bit then 2^i.2.2.val else 0))
    (fields : ∀ c,(cells c).directory.reportedCounts =
      countFields ((reports c).privateWires+(reports c).supplied) l.gadgets l.countWidth)
    (digits : ∀ c g j,(reports c).counts g j=
      (cells c).bank ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val))
    (rawBits : DiagonalTallyBits.WordsAt mem raw p.tallyWords)
    (bounded : ∀ j, rows t j<2^w) :
    let os := receiptOperands tags pos words label team a t o reports post q (pub 0).val trueAddr
    supplied selected post.fresh post.descriptors os → (selected ((pub 0).val+35)).val=os.length →
    os.length ≤ post.bound.operands →
    (∀ k,operandReads post.descriptors os k → outsidePointers (pub 0).val k ∧ k≠(pub 0).val+34) →
    FinishInput t rows width pub mac state mem p.tallyWords := by
  intro os suppliedRows count capacity sep
  let item (i : Fin o.nVertex) := packetOperand l.parameters (post.ids+i.val) l.zeroAddr ((pub 0).val+82)
    trueAddr (pathPacketID pos a (o.vertices i).val).val
  have perm : (os.map Operand.pair).Perm ((operands tags pos words label team a t o uses cells packets).map Operand.pair) :=
    emittedPairs_perm tags pos words label team a t o uses cells packets reports q item source align fields digits
      (fun _ => packetOperand_pair ..)
  have claims := signedClaim_source slot tags x pos words label team a t o uses cells packets post pub mac
    state bank mem selected es raw width os p.tallyWords prepared seed kept frame rawLo rawHi room teamsFit
    widthFit wpos suppliedRows count capacity sep rawBits p.tallyWords_length p.tallyWords_width perm
    useBit siteID bounded prepared
  exact ⟨post,raw,os,es,bank,selected,prepared,claims.1,claims.2,capacity⟩

omit [Fintype Cell] in
/-- On the canonical claim, every actual finish returns the typed path tally in
the query bank, with the parameter powers summed across their routed owner teams. -/
theorem finishReceipt_physical_bits (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (state : Bank w)
    (mem : Memory w) (receipt : FinishInput t rows width pub mac state mem p.tallyWords)
    (canonical : p.subtotals = canonicalSubtotals width rows)
    (bounded : ∀ i c,rows i c<2^width) (sumFit : ∀ c, ∑ i,rows i c<2^w)
    (z : Evaluator.Returns Finish pub mac state mem) (c : Fin (l.parameters+l.gadgets)) (j : ℕ) (hj : j<w) :
    z.val.2.2 (receipt.post.localBase+(l.parameters+l.gadgets)+T*(l.parameters+l.gadgets)+
      (l.parameters+l.gadgets)+(l.parameters+l.gadgets)+1+(c.val*w+j)) =
    word w (((∑ i : Fin T,tallyRow (pathTally slot tags x pos words label team a) i c).testBit j).toNat) := by
  have eq : p.tallyWords=DiagonalTallyRAM.broadcast width rows := by
    change splitFields width (T*(l.parameters+l.gadgets)) (List.ofFn p.subtotals) = _
    rw [canonical,ofFn_canonicalSubtotals,splitFields_broadcast]
  obtain ⟨z',_,_,actual⟩ := receipt.complete eq bounded sumFit
  rw [finish_eq z z']
  exact (actual c j hj).trans (congrArg (fun v : ℕ => word w (v.testBit j).toNat)
    (sum_physicalRow slot tags x pos words label team a c))

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
