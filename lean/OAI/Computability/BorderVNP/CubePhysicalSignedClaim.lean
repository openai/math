import OAI.Computability.BorderVNP.CubePhysicalSignedFinish

/-! # Inverting an arbitrary common claim at the physical signed native tail -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA
open scoped BigOperators Classical

variable {n d blocks b h K s D B T H U w : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry (Fin H) (Fin U)))
    (x : Ports bits) (pos : Packet n d blocks → TableEntry n b h K s → Fin U)
    (words : PowerWords (Fin T) (Fin H) (Fin U) B N tags)
    (label : Cell → Label (n+1) d) (team : Fin d → Fin T) (a : Path N cell n d blocks b h K s) (t : Fin T)
    (o : Orders tags words label team a t) (uses : PowerSlot (Fin T) (Fin H) B → UseRead)
    (cells : ∀ c : Cell, CellRead {v : N.Site // cell v=c} U)
    (packets : Packet n d blocks × Vertex (n+1) → PacketRead)

/-- On an arbitrary returning selected-operand prefix, the checked cell and packet
observations recover the actual local row of the physical path. The common tape can
still contain any claimed bits. This provides the concrete allocator inputs for the
all-team inversion of the common broadcast. -/
theorem signedClaim_source (post : AfterTasks) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (state bank : Bank w) (mem selected : Memory w) (es : List (TeamRAM.Event w))
    (raw width : ℕ) (os : List Operand) (xs : List (List Bool))
    (prepared : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      state mem es bank selected)
    (seed : SelectedSeed post pub mem raw (H+U) T t.val width)
    (kept : ∀ k,k<post.start → k≠(pub 0).val+35 → selected k=mem k)
    (frame : (pub 0).val+101<post.start) (rawLo : (pub 0).val+45 ≤ raw) (rawHi : raw+T*(H+U)*width ≤ post.start)
    (room : post.localBase+(H+U)+T*(H+U)+(H+U)+(H+U)+1+(H+U)*w<2^w)
    (teamsFit : T<2^w) (widthFit : width ≤ w) (wpos : 0<w)
    (suppliedRows : supplied selected post.fresh post.descriptors os) (count : (selected ((pub 0).val+35)).val=os.length)
    (capacity : os.length ≤ post.bound.operands)
    (sep : ∀ k,operandReads post.descriptors os k → outsidePointers (pub 0).val k ∧ k≠(pub 0).val+34)
    (rawBits : DiagonalTallyBits.WordsAt mem raw xs) (size : xs.length=T*(H+U)) (widths : ∀ v∈xs,v.length=width)
    (perm : (os.map Operand.pair).Perm ((operands tags pos words label team a t o uses cells packets).map Operand.pair))
    (useBit : ∀ i,(uses i).bit=words.localUse (pathEdges slot a) (fun _ p => x p.val) i.1 i.2.1 i.2.2)
    (siteID : ∀ c (v : {v : N.Site // cell v=c}) g, (((cells c).observed v).filterMap Prod.snd).count g.val=
      (counters (tags v.val (pathEdges slot a v.val) (fun p => x p.val))).2 g)
    (bounded : ∀ j,physicalRow slot tags x pos words label team a t j<2^w)
    {fs u mu} (returned : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      state mem fs u mu) :
    let ar := post.arenaFor os.length raw (H+U) T t.val width
    AlignedAllocationInput ar pub mu os xs post.descriptors ∧
      ∀ c : Fin (H+U), ar.localRow os c.val=physicalRow slot tags x pos words label team a t c := by
  intro ar
  obtain ⟨_,_,same⟩ := returned.unique_of_deterministic (by decide) prepared
  rw [same]
  have actual (c : Fin (H+U)) : ar.localRow os c.val=physicalRow slot tags x pos words label team a t c :=
    (increment_pair_perm perm ar.frame.localBase c.val).trans
      (increment_eq_row slot tags x pos words label team a t o uses cells packets ar.frame.localBase c useBit siteID)
  refine ⟨seed.alignedInput post pub mem selected raw (H+U) T t.val width os xs kept frame rawLo rawHi room t.isLt
    teamsFit widthFit wpos suppliedRows count capacity sep ?_ (fun c hc => (actual ⟨c,hc⟩) ▸ bounded ⟨c,hc⟩) rawBits size widths,actual⟩
  intro op hm
  obtain ⟨other,ho,eq⟩ := List.mem_map.mp (perm.mem_iff.mp (List.mem_map.mpr ⟨op,hm,rfl⟩))
  rw [←eq]
  exact operands_coordinates tags pos words label team a t o uses cells packets other ho

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
