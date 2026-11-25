import OAI.Computability.MultitapeWeakETH.HistoryIncidence
import OAI.Computability.MultitapeWeakETH.HistoryPacket

/-! # Reading a selected child packet length directly from the execution log -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget
open DescriptorSpace PairSimulation LocalHistory TraversalRows TraversalRoles
open private clocks from OAI.Computability.MultitapeWeakETH.DescriptorProgram
open scoped Fin.CommRing
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

private abbrev Q := (LogQuery × Tally) × Tally

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory

set_option maxHeartbeats 1600000 in
/-- One uniform polynomial-time program on a volume, retained writes, pass index and child
ordinal. Its output is the exact width of the recursive child argument, for every possible
assignment on that child. -/
theorem history_operand (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ size : Q → Tally, Poly size ∧ ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      1 ≤ s → slotDegree S ≤ s → ∀ (z : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X z
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState z) m →
        ∀ i : Fin past.length, let V := (past[i.val]'i.isLt).input
        ∀ (v : V.network.Site) (h : V.network.Half v),
          size (((volume,writes log),tally i.val),tally ((siteOrder V).entries.symm v).val) =
            tally (NodeArguments.packed V v h).length := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have cost : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  obtain ⟨_,fuel,_⟩ := clocks B
  let cap (q : Q) := tally (scale B (index (4*stepSize B) q.1.1.1.length)+24)
  have cp : Poly cap := (show Poly (fun q : Q => q.1.1.1) by fun_prop).compose
    (show Poly (fun q : Tally => tally (scale B (index (4*stepSize B) q.length)+24)) from fuel)
  let input (q : Q) := (((historyQuery B q).1.1,cap q),q.2)
  have inp : Poly input := ((historyQuery_poly B).fstCompose.fstCompose.pair cp).pair Easy.snd.poly
  refine ⟨fun q => ChildScan.packetSize rd (slotDegree S) (input q),inp.compose (ChildScan.packetSize_poly rd cost _),?_⟩
  intro volume s n w u X initial L base E hs hd z log past m stored i V v h
  have pub := CompiledResident.read stored.2 i
  let T := packedIncidence L w i.val (V.positions*2^(past[i.val]'i.isLt).inputExponent)
  have inc : m (levelStart L i.val+16) = ((2^(past[i.val]'i.isLt).inputExponent : ℕ) : Word w) ∧
      m (levelStart L i.val+19) = T.actualIn ∧ m (levelStart L i.val+20) = T.width ∧ T.ActualColumns V m :=
    history_incidence pub
  have room : levelStart L i.val+20 < 2^w := (CompiledResident.child_directory pub).room
  have loc (j : ℕ) (hj : j ≤ 20) : (((levelStart L i.val : Word w)+(j : Word w))).val = levelStart L i.val+j := by
    rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt]; omega
  have natFit : n < 2^w := stored.1.2.1.startup.length ▸ (m (levelStart L 0+29)).isLt
  have width : V.maxWireWidth ≤ n := (history_size hs z (past[i.val]'i.isLt) (List.getElem_mem i.isLt)).2
  have degree := (past[i.val]'i.isLt).oldDegree_le
  let ctx : LogQuery := (tally s,writes log)
  have exactRead (a : Word w) : rd (ctx,wordBits a)=wordBits (m a.val) := spec s log a
  have addr (j : Tally) : historyHeader B (volume,j) = wordBits ((levelStart L j.length : ℕ) : Word w) := rfl
  change ChildScan.packetSize rd _ (((ctx,historyHeader B (volume,tally i.val)),tally (n+24)),_) = _
  rw [addr,tally_length]
  apply ChildScan.packetSize_eq rd V T ctx m exactRead _ _ _ _ _ _ inc.2.2.2
    (width.trans (Nat.le_add_right ..)) (width.trans_lt natFit) degree
    ((degree.trans (hd.trans (scale_ge B s))).trans_lt natFit)
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=16),loc 16 (by decide)] using inc.1
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=19),loc 19 (by decide)] using inc.2.1
  · simpa only [← Nat.cast_ofNat (R:=Word w) (n:=20),loc 20 (by decide)] using inc.2.2.1

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
