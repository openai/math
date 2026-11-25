import OAI.Computability.MultitapeWeakETH.TerminalProgram
import OAI.Computability.MultitapeWeakETH.HistoryChildren
import OAI.Computability.MultitapeWeakETH.PlacedMemory

/-! # Reading keyed private child packets from the native chronological row -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression BurstRAM CompressorRecords DescriptorSpace PairSimulation LocalHistory
open TraversalRows TraversalRoles NetworkKernel DyadicBudget NodeArguments.ChildScan
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical Fin.CommRing
noncomputable section

abbrev ChildResult := (List Tally × NamedPackets.Bank) × Bits.Word

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

/-- The job list retains its unary ordinals while the operand reader receives the
same identifiers encoded at the native word width. -/
private def tagChildren (children : HistorySite → List Tally) (q : (HistorySite × Bits.Word) × (List Bits.Word × Bits.Word)) :
    Option ChildResult :=
  let site := q.1.1
  let ids := children site
  let head := historyHeader B (site.1.1.1,site.1.2)
  some ((ids,NamedPackets.keys (head,ids),q.2.1),q.2.2)

private theorem tagChildren_poly {children : HistorySite → List Tally} (hc : Poly children) : Poly (tagChildren B children) := by
  let X := (HistorySite × Bits.Word) × (List Bits.Word × Bits.Word)
  have ids : Poly (fun q : X => children q.1.1) := (Easy.fst.compose Easy.fst).poly.compose hc
  have head : Poly (fun q : X => historyHeader B (q.1.1.1.1.1,q.1.1.1.2)) := by
    apply Poly.compose (g:=historyHeader B) _ (historyHeader_poly B)
    dsimp only [X]
    fun_prop
  exact ((ids.pair (((head.pair ids).compose NamedPackets.keys_poly).pair (Easy.snd.compose Easy.fst).poly)).pair
    (Easy.snd.compose Easy.snd).poly).compose Easy.some.poly

private theorem child_ids {f : B.Entry → R} {hf : B.IsSolution f} (V : SelectedLevel B f hf)
    (j : Fin (levelLayer B f hf V).count) : (levelLayer B f hf V).ids j =
      List.ofFn (fun n => ((siteOrder V.input).entries.symm ((childOrder V j).entries n).val).val) := rfl

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels levelLayer

set_option maxHeartbeats 1200000 in
theorem history_child_bank (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ run : HistorySite × Bits.Word → Option ChildResult, Poly run ∧ ∀ volume : Tally,
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
        ∀ (j : Fin (levelLayer B f hf V).count) bits ids bank tail,
          run ((((volume,writes log),tally i.val),tally j.val),bits) = some ((ids,bank),tail) ↔
          ∃ h : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j),
            ids = ((levelLayer B f hf V).ids j).map tally ∧
            bank = NamedPackets.placedBank V.input _ _ (childOrder V j) h w ∧ bits = bank.2.flatten ++ tail := by
  obtain ⟨_,children,_,hc,isIds⟩ := history_program B f hf
  obtain ⟨parse,hp,isParse⟩ := history_children B f hf
  refine ⟨fun q => (parse q).bind (fun a => tagChildren B children (q,a)),
    bind_poly ([],[]) hp (tagChildren_poly B hc),?_⟩
  intro volume s n w u X initial L base E hs hd path log past m resident i V j bits ids bank tail
  let point : HistorySite := (((volume,writes log),tally i.val),tally j.val)
  let actual := ((levelLayer B f hf V).ids j).map tally
  have numbers : children point = actual := (isIds volume path log resident).2 i j
  have head : historyHeader B (volume,tally i.val) = wordBits ((levelStart L i.val : ℕ) : Word w) := by
    unfold historyHeader
    rw [tally_length]
  have keys (h : Placed (V.pass.step.term V.term).place V.input.network.Half (outputSite V j)) :
      NamedPackets.keys (historyHeader B (volume,tally i.val),actual) =
        (NamedPackets.placedBank V.input _ _ (childOrder V j) h w).1 := by
    rw [head,NamedPackets.keys_eq]
    rw [child_ids B,List.map_ofFn]
    rfl
  let bankFor (rows : List Bits.Word) : NamedPackets.Bank := (NamedPackets.keys (historyHeader B (volume,tally i.val),actual),rows)
  have tagged (rows rest) : tagChildren B children ((point,bits),rows,rest) = some ((actual,bankFor rows),rest) := by
    change some ((children point,(NamedPackets.keys (_,children point),rows)),rest) = _
    rw [numbers]
  have decode := isParse volume hs hd path log resident i j bits
  change (parse (point,bits)).bind _ = _ ↔ _
  constructor
  · intro ok
    cases p : parse (point,bits) with
    | none => simp only [p,Option.bind_none] at ok; contradiction
    | some v =>
      rcases v with ⟨rows,rest⟩
      rw [p,Option.bind_some,tagged] at ok
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := (Prod.mk.inj (Option.some.inj ok)).imp_left Prod.mk.inj
      obtain ⟨h,rowsEq,stream⟩ := (decode rows rest).mp p
      exact ⟨h,rfl,Prod.ext (keys h) rowsEq,stream⟩
  · rintro ⟨h,rfl,rfl,stream⟩
    let rows := ChildScan.packets V.input _ _ (childOrder V j) h
    have p := (decode rows tail).mpr ⟨h,rfl,stream⟩
    change parse (point,bits) = some (rows,tail) at p
    rw [p,Option.bind_some,tagged]
    exact congrArg (fun b => some ((actual,b),tail)) (Prod.ext (keys h) rfl)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
