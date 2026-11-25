import OAI.Computability.MultitapeWeakETH.HistoryProgram
import OAI.Computability.MultitapeWeakETH.HistoryOperand
import OAI.Computability.MultitapeWeakETH.PlacedPackets

/-! # The joint child argument reader on an actual sparse execution history -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget
open DescriptorSpace PairSimulation LocalHistory TraversalRows TraversalRoles NetworkKernel
open private placementLayer from OAI.Computability.VPVNP.PairTraversalStageSize
open scoped Fin.CommRing Classical
noncomputable section

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
  {f : B.Entry → R} {hf : B.IsSolution f}

def outputOrder (V : SelectedLevel B f hf) : Order (V.pass.step.term V.term).output.Site :=
  (V.pass.output_eq V.term).symm ▸ siteOrder (V.pass.next V.term)

def outputSite (V : SelectedLevel B f hf) (j : Fin (levelLayer B f hf V).count) :=
  (outputOrder V).entries j

def childOrder (V : SelectedLevel B f hf) (j : Fin (levelLayer B f hf V).count) :=
  (siteOrder V.input).restrict (fun u => outputSite V j = (V.pass.step.term V.term).place u)

private theorem sizes_on_fiber (V : SelectedLevel B f hf) (j : Fin (levelLayer B f hf V).count)
    (size : Tally → Tally) (get : ∀ u (h : V.input.network.Half u),
      size (tally ((siteOrder V.input).entries.symm u).val) = tally (NodeArguments.packed V.input u h).length) :
    (((levelLayer B f hf V).ids j).map tally).map size =
      ChildScan.packetWidths V.input (V.pass.step.term V.term) (outputSite V j) (childOrder V j) := by
  change ((List.ofFn (fun i => ((siteOrder V.input).entries.symm ((childOrder V j).entries i).val).val)).map tally).map size = _
  simp only [List.map_ofFn,Function.comp_def,ChildScan.packetWidths]
  apply congrArg List.ofFn
  funext i
  let u := ((childOrder V j).entries i).val
  let zero : V.input.network.Half u := (fun _ _ _ => false,fun _ _ _ => false)
  exact (get u zero).trans (congrArg tally (NodeArguments.packed_length V.input u zero))

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels levelLayer BlockSchedule.Templates.execute

set_option maxHeartbeats 1600000 in
/-- The private candidate starts with exactly the concatenated child arguments in placement
order. An accepted prefix decodes to the joint old assignment used by the local kernel. -/
theorem history_children (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ parse : HistorySite × Bits.Word → Option (List Bits.Word × Bits.Word), Poly parse ∧ ∀ volume : Tally,
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
        ∀ (i : Fin past.length), let V := past[i.val]'i.isLt
        ∀ (j : Fin (levelLayer B f hf V).count) bits rows tail,
          parse ((((volume,writes log),tally i.val),tally j.val),bits) = some (rows,tail) ↔
          ∃ h : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j),
            rows = ChildScan.packets V.input _ _ (childOrder V j) h ∧ bits = rows.flatten ++ tail := by
  obtain ⟨_,ids,_,ip,isIds⟩ := history_program B f hf
  obtain ⟨size,sp,isSize⟩ := history_operand B f hf
  let sizes (q : HistorySite) := (ids q).map fun j => size (q.1,j)
  have prog : Poly sizes := (Easy.fst.poly.pair ip).compose (Poly.push default [] sp)
  refine ⟨fun q => ChildScan.splitPackets (sizes q.1,q.2),((Easy.fst.poly.compose prog).pair Easy.snd.poly).compose ChildScan.splitPackets_poly,?_⟩
  intro volume s n w u X initial L base E hs hd z log past m resident i V j bits rows tail
  let point : HistoryPoint := ((volume,writes log),tally i.val)
  have idsEq := (isIds volume z log resident).2 i j
  have sizeEq := isSize volume hs hd z log resident i
  change ChildScan.splitPackets (sizes (point,tally j.val),bits) = some (rows,tail) ↔ _
  have sizesEq : sizes (point,tally j.val) = ChildScan.packetWidths V.input _ _ (childOrder V j) := by
    unfold sizes
    exact (congrArg (List.map (fun idx => size (point,idx))) idsEq).trans (sizes_on_fiber V j _ sizeEq)
  rw [sizesEq]
  exact ChildScan.placed_packets_iff V.input _ _ (childOrder V j) bits rows tail

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
