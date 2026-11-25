import OAI.Computability.BorderVNP.CubeISAOwnedRawPacketLoop

/-! # Raw selector observations from the actual packet-stage entry frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedStages

open Cube Cube.Scatter Physical Physical.Owned Cube.Tally VPVNP.BurstRAM DiagonalResidueRAM Owned OwnedVertex

variable {w n b h K s : ℕ}

/-- The real setup and the returning packet scan reveal each native selector
chunk. The observations do not presuppose any selector tuple. -/
theorem rawPacketStage_chunks (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : OwnedRowSetup.Layout) (src : Set ℕ) (i : Fin (n+1)) (pair : Symbols l.d) (high : Bool)
    (sel : ℕ) (chunks : Fin (packetTrials n l.d l.blocks) → List Bool) (r : Bank w) (m : Memory w)
    (entry : Entry i pair.val.1 pair.val.2 r) (group : readings r 3 = (if high then pair.val.2 else pair.val.1).val)
    (start : r 36 = word w sel) (loaded : l.Loaded n (readings pub) (readings m))
    (fit : PacketRoom l w n b h K s (pub 0).val)
    (source : ∀ p : Packet n l.d l.blocks, p.1.1 i = pair → ∀ x ∈ src,
      x < bankAt l.bank (bankWidth n b h K s) p ∨ bankAt l.bank (bankWidth n b h K s) p+bankWidth n b h K s ≤ x)
    (length : ∀ t, packetTrialValid t → (chunks t).length = selectorWidth n K h)
    (bits : ∀ t, packetTrialValid t → Resident src m
      (sel+selectedPrefix (blocks := l.blocks) i pair t.val*selectorWidth n K h) (chunks t))
    {es t mt} (path : Runs pub mac (packetStage n b h K s) r m es t mt) :
    Keeps r t ∧ t 36 = word w (sel+(2*l.blocks*(l.d.choose 2)^n)*selectorWidth n K h) ∧
      (∀ x ∈ src, mt x = m x) ∧
      ∀ k : Fin (packetTrials n l.d l.blocks), ∀ hk : packetTrialValid k,
        ∃ u : Selector n K h, chunks k = selectorStream u ∧ SelectorRead.Stored (readings mt)
          (bankAt l.bank (bankWidth n b h K s) (packetRowEquiv i pair ⟨k,hk⟩).val) u := by
  obtain ⟨v,mv,_,_,_,setup,scan⟩ := Runs.seq_iff.mp path
  have count : Fintype.card (Selector n K h) < 2^w := (le_max_left ..).trans_lt fit.keys
  have width : selectorWidth n K h < 2^w := (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans_lt count
  have first := (OwnedRowSetup.packet_run pub mac r m l i pair b h K s loaded fit.layout
    fit.trials width count fit.stride entry.zero entry.one entry.axis entry.left entry.right).asTest
    (OwnedRowSetup.packet_deterministic ..)
  obtain ⟨ready,dim,bitsAt,countAt,keep,mem⟩ := (first.sound setup).2
  have hm : mv = m := funext fun j => Fin.ext (congrFun mem j)
  subst mv
  obtain ⟨low,rest⟩ := rawPacketLoop_return src i pair high l.bank sel chunks v m ready
    ((keep 3 (by decide)).trans group) ((keep 4 (by decide)).trans entry.axis) dim bitsAt countAt
    ((Fin.ext (keep 36 (by decide))).trans start) fit.positive fit.keys fit.bank source length bits scan
  exact ⟨keeps_setup_loop keep low,rest⟩

/-- The raw selector prefix at the directed physical address is the exact encoding
of a recovered packet tuple on this row. This follows from an arbitrary returning
packet stage even if its declared crossing length or crossing words are wrong. -/
theorem rawPacketStage_return (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : OwnedRowSetup.Layout) (src : Set ℕ) (i : Fin (n+1)) (pair : Symbols l.d) (high : Bool)
    (sel : ℕ) (raw : List Bool) (r : Bank w) (m : Memory w)
    (entry : Entry i pair.val.1 pair.val.2 r) (group : readings r 3 = (if high then pair.val.2 else pair.val.1).val)
    (start : r 36 = word w sel) (loaded : l.Loaded n (readings pub) (readings m))
    (fit : PacketRoom l w n b h K s (pub 0).val)
    (source : ∀ p : Packet n l.d l.blocks, p.1.1 i = pair → ∀ x ∈ src,
      x < bankAt l.bank (bankWidth n b h K s) p ∨ bankAt l.bank (bankWidth n b h K s) p+bankWidth n b h K s ≤ x)
    (len : raw.length = 2*l.blocks*(l.d.choose 2)^n*selectorWidth n K h) (bits : Resident src m sel raw)
    {es t mt} (path : Runs pub mac (packetStage n b h K s) r m es t mt) :
    Keeps r t ∧ t 36 = word w (sel+raw.length) ∧ (∀ x ∈ src, mt x = m x) ∧
      ∃ S : Packet n l.d l.blocks → Selector n K h, raw = commonSelectors S i pair ∧
        ∀ p : Packet n l.d l.blocks, p.1.1 i = pair →
          SelectorRead.Stored (readings mt) (bankAt l.bank (bankWidth n b h K s) p) (S p) := by
  let offset (t : Fin (packetTrials n l.d l.blocks)) := selectedPrefix (blocks := l.blocks) i pair t.val*selectorWidth n K h
  have size := selectorChunk_fits K h raw i pair len
  obtain ⟨control,endSel,keep,checked⟩ := rawPacketStage_chunks pub mac l src i pair high sel
    (selectorChunk K h raw i pair) r m entry group start loaded fit source
    (fun t ht => rawChunk_length raw (offset t) _ (size t ht))
    (fun t ht => bits.chunk (offset t) _ ((Nat.le_add_right ..).trans (size t ht))) path
  obtain ⟨S,encoded,stored⟩ := exists_selectors_of_chunks i pair raw len
    (fun p u => SelectorRead.Stored (readings mt) (bankAt l.bank (bankWidth n b h K s) p) u) checked
  exact ⟨control,len.symm ▸ endSel,keep,S,encoded,fun p hp => stored ⟨p,hp⟩⟩

end RoutingISA.OwnedStages

end BorderVNP
end Computability
end OAI
