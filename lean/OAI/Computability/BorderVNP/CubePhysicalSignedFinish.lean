import OAI.Computability.BorderVNP.DiagonalTallySignedFinish
import OAI.Computability.BorderVNP.CubePhysicalAlignedTally
import OAI.Computability.BorderVNP.CubePhysicalReportLedger

/-! # Physical path exponents and scalar multiplicities in the linked signed evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
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

include packets in
/-- Starting with the real selected-ID and descriptor scan, the full post-cell stage
of the linked native evaluator writes the precise parameter powers and gadget counts
of this same path. Repeated selected IDs and zero-valued scalar positions contribute
their full multiplicity. The serialized output address is length-only. -/
theorem signedFinish_physical (post : AfterTasks) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (state bank : Bank w) (mem selected : Memory w) (es : List (TeamRAM.Event w))
    (q : ReportCursor) (raw width trueAddr budget : ℕ)
    (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      state mem es bank selected) (clock : traceCost es ≤ budget)
    (seed : SelectedSeed post pub mem raw (l.parameters+l.gadgets) T t.val width)
    (kept : ∀ k,k<post.start → k≠(pub 0).val+35 → selected k=mem k)
    (frame : (pub 0).val+101<post.start) (rawLo : (pub 0).val+45 ≤ raw)
    (rawHi : raw+(T*(l.parameters+l.gadgets))*width ≤ post.start)
    (room : post.localBase+(l.parameters+l.gadgets)+T*(l.parameters+l.gadgets)+
      (l.parameters+l.gadgets)+(l.parameters+l.gadgets)+1+(l.parameters+l.gadgets)*w<2^w)
    (teamsFit : T<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (useBit : ∀ i, (uses i).bit=words.localUse (pathEdges slot a) (fun _ p => x p.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v=c}) g, (((cells c).observed v).filterMap Prod.snd).count g.val=
      (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g)
    (source : UseOccurrence (teamReports tags words label team a t o reports) ≃
      {i // routedPowerOwner tags words label team a i=t})
    (align : ∀ u, let i := (source u).val
      occurrencePair (teamReports tags words label team a t o reports) u =
        (i.2.1.val,if (uses i).bit then 2^i.2.2.val else 0))
    (fields : ∀ c,(cells c).directory.reportedCounts =
      countFields ((reports c).privateWires+(reports c).supplied) l.gadgets l.countWidth)
    (digits : ∀ c g j,(reports c).counts g j=
      (cells c).bank ((reports c).privateWires+(reports c).supplied+g.val*l.countWidth+j.val)) :
    let cs := teamReports tags words label team a t o reports
    let earlier := cellOperands cs q
    let f := post.suffixFrame earlier.length o.nVertex l.zeroAddr l.parameters
    let ids := fun i => (pathPacketID pos a (o.vertices i).val).val
    let os := earlier++f.packetOperands (pub 0).val trueAddr ids
    let ar := post.arenaFor os.length raw (l.parameters+l.gadgets) T t.val width
    let rows := physicalRow slot tags x pos words label team a
    supplied selected post.fresh post.descriptors os → (selected ((pub 0).val+35)).val=os.length →
    os.length ≤ post.bound.operands →
    (∀ k,operandReads post.descriptors os k → outsidePointers (pub 0).val k ∧ k≠(pub 0).val+34) →
    DiagonalTallyBits.WordsAt mem raw (DiagonalTallyRAM.broadcast width rows) →
    (∀ i j,rows i j<2^width) → (∀ c, ∑ i,rows i c<2^w) →
    ∃ fs z mz, Runs pub mac (Evaluator.finishExpansion Evaluator.signedOccurrences) state mem fs z mz ∧
      traceCost fs ≤ budget+(alignTallies.slots+allocateTallies.slots+ar.work w os) ∧
      (∀ e∈fs,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin (l.parameters+l.gadgets),∀ j<w,
        mz (post.localBase+(l.parameters+l.gadgets)+T*(l.parameters+l.gadgets)+
          (l.parameters+l.gadgets)+(l.parameters+l.gadgets)+1+(c.val*w+j)) =
        word w (((∑ i : Fin T,tallyRow (pathTally slot tags x pos words label team a) i c).testBit j).toNat) := by
  intro cs earlier f ids os ar rows suppliedRows count cap sep rawBits rowFit sumFit
  let item (i : Fin o.nVertex) := packetOperand l.parameters (post.ids+i.val) l.zeroAddr ((pub 0).val+82) trueAddr (ids i)
  have perm : (os.map Operand.pair).Perm ((operands tags pos words label team a t o uses cells packets).map Operand.pair) :=
    emittedPairs_perm tags pos words label team a t o uses cells packets reports q item source align fields digits
      (fun _ => packetOperand_pair ..)
  have correct (c : Fin (l.parameters+l.gadgets)) : ar.localRow os c.val=rows t c :=
    (increment_pair_perm perm ar.frame.localBase c.val).trans
      (increment_eq_row slot tags x pos words label team a t o uses cells packets ar.frame.localBase c useBit siteID)
  have coords (op : Operand) (hm : op∈os) : op.pair.1<l.parameters+l.gadgets := by
    obtain ⟨other,ho,eq⟩ := List.mem_map.mp (perm.mem_iff.mp (List.mem_map.mpr ⟨op,hm,rfl⟩))
    rw [←eq]
    exact operands_coordinates tags pos words label team a t o uses cells packets other ho
  have sums (c : ℕ) (hc : c<l.parameters+l.gadgets) : ar.localRow os c<2^w :=
    (correct ⟨c,hc⟩) ▸ (rowFit t ⟨c,hc⟩).trans_le (Nat.pow_le_pow_right (by decide) widthFit)
  have input := seed.alignedInput post pub mem selected raw _ T t.val width os _ kept frame rawLo rawHi room
    t.isLt teamsFit widthFit wpos suppliedRows count cap sep coords sums rawBits (by simp [DiagonalTallyRAM.broadcast])
    (by intro bs hb; obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb; exact length_wordBits _)
  obtain ⟨fs,z,mz,run,cost,positive,data⟩ := signedFinish_runs ar pub mac state bank mem selected es os
    post.descriptors budget rows prepared clock input (fun c => correct c) rowFit sumFit
  refine ⟨fs,z,mz,run,cost,positive,fun c j hj => ?_⟩
  have actual := data c j hj
  have dst : (ar.bitFrame w).dst = post.localBase+(l.parameters+l.gadgets)+T*(l.parameters+l.gadgets)+
      (l.parameters+l.gadgets)+(l.parameters+l.gadgets)+1 := (post.fixed_outputs cap raw _ T t.val width w).2.2.2
  rw [dst] at actual
  exact actual.trans (congrArg (fun u : ℕ => word w (u.testBit j).toNat)
    (sum_physicalRow slot tags x pos words label team a c))

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
