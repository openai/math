import OAI.Computability.MultitapeWeakETH.ShrinkHiddenPackets
import OAI.Computability.MultitapeWeakETH.ShrinkHiddenCapacity
import OAI.Computability.MultitapeWeakETH.HistoryChildren

/-! # The ordered hidden-field parser on actual chronological shrinking occurrences -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Carry Staff Strip VPVNP Compression Compression.ShrinkMotif
open CompressorRecords DescriptorSpace PairSimulation LocalHistory BurstRAM ShrinkBlockInputs
open TraversalRows TraversalRoles NetworkKernel DyadicBudget ShrinkRole Filter
open private clocks from OAI.Computability.MultitapeWeakETH.DescriptorProgram
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

private def hiddenQuery (q : HistorySite) : ShrinkHidden.Query LogQuery :=
  let n := scale B (index (4*stepSize B) q.1.1.1.length)
  (((historyQuery B q).1.1,tally (n*n)),q.2)

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

private theorem hiddenQuery_poly : Poly (hiddenQuery B) := by
  obtain ⟨_,fuel,_⟩ := clocks B
  have cap := fuel.minused (Realizes.fix 24)
  have square := cap.times cap
  change Poly (fun q : Tally => tally (((scale B (index (4*stepSize B) q.length)+24)-24)*
    ((scale B (index (4*stepSize B) q.length)+24)-24))) at square
  simp only [Nat.add_sub_cancel] at square
  exact ((historyQuery_poly B).fstCompose.fstCompose.pair
    ((show Poly (fun q : HistorySite => q.1.1.1) by fun_prop).compose square)).pair Easy.snd.poly

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 6000 in
/-- Each shrinking stage has one fixed tape program. Past a common grid threshold, its
output at every retained occurrence identifies exactly the consumed typed hidden assignment. -/
theorem history_hidden (i : Fin S.steps) (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ run : HistorySite × Bits.Word → ShrinkHidden.Parsed, Poly run ∧ ∃ s₀ : ℕ, ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      s₀ ≤ s → ∀ (z : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X z
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState z) m →
        ∀ (j : Fin past.length) {g : ℕ} (Z : State (a i) (packingLaneBits (a i) g))
          (sel : SelectedScore.Selection B Z) (selector : List Bool),
          (past[j.val]'j.isLt) = shrinkLevel B f hf i Z sel selector →
          ∀ (v : MapResidentRows.Site Z) (bits : Bits.Word) (ids fields : List Bits.Word) (tail : Bits.Word),
            let side := SelectedFinish.chosen B Z sel
            let widths := ShrinkHiddenRows.widths Z B.shrink sel
            let site := (MapResidentRows.siteIndex Z v).val
            run (((((volume,writes log),tally j.val),tally site)),bits) = (ids,some (fields,tail)) ↔
              ∃ h : Placed (Z.packingData.shrinkInternalOwner side) (internalLabel widths side) v,
                let rows := ShrinkHiddenSlots.rows Z side widths v h
                ids = rows.map (fun e => wordBits (e.1 : Word w)) ∧
                  fields = rows.map Prod.snd ∧ bits = ShrinkHiddenGuess.stream rows ++ tail := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have rp : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  obtain ⟨scan,cost,exec⟩ := ShrinkHidden.scan_program rd rp (ShrinkVertexImage.hiddenStride i) B.shrink.selectorBits
  obtain ⟨N,late⟩ := eventually_atTop.mp (ShrinkHidden.eventually_facts B)
  refine ⟨fun q => ShrinkHidden.parse (scan (hiddenQuery B q.1),q.2),
    ((Easy.fst.poly.compose ((hiddenQuery_poly B).compose cost)).pair Easy.snd.poly).compose ShrinkHidden.parse_poly,
    max 1 N,?_⟩
  intro volume s n w u X initial L base E hs z log past m resident j g Z sel selector occurrence v bits ids fields tail side widths site
  let V := past[j.val]'j.isLt
  have member : V ∈ executeLevels B f hf s (lanes_fit B s) X z := List.getElem_mem j.isLt
  have hs₁ := (le_max_left 1 N).trans hs
  obtain ⟨pos,wide⟩ := history_size hs₁ z V member
  have degree := V.oldDegree_le
  have stored := CompiledResident.read resident.2 j
  change V = shrinkLevel B f hf i Z sel selector at occurrence
  change CompiledResident.payload B f hf (0 : Word w) X.positions s n j.val V m at stored
  rw [occurrence] at stored pos wide degree
  have payload := (CompiledResident.shrink_payload ..).mp stored
  have facts := late n (((le_max_right 1 N).trans hs).trans (scale_ge B s)) i Z sel X.positions s j.val
    (0 : Word w) m payload (pos.trans (source_positions B hs₁)) wide degree v
  let ctx : LogQuery := (tally s,writes log)
  let args := PackedHidden.arguments B i Z sel (0 : Word w) X.positions s j.val n ShrinkHidden.regions v
  let seed := PackedHidden.zeroRows B i Z sel v
  have rowCount : seed.length = ShrinkVertexImage.hiddenStride i := ShrinkHiddenRows.rows_length ..
  have agree := exec ctx (levelStart L j.val) (n*n) m args seed (spec s log) facts.1.headers
    facts.1.headRoom facts.1.selectors facts.1.rowStride facts.1.countFit facts.1.count rowCount.le facts.1.valid facts.2
  have ptr : historyHeader B (volume,tally j.val) = wordBits ((levelStart L j.val : ℕ) : Word w) := by
    unfold historyHeader
    rw [tally_length]
  rw [facts.1.owner] at agree
  change ShrinkHidden.parse (scan (((ctx,historyHeader B (volume,tally j.val)),tally (n*n)),tally site),bits) = _ ↔ _
  rw [ptr]
  change ShrinkHidden.parse (scan (ShrinkHidden.query ctx _ _ site),bits) = _ ↔ _
  rw [agree]
  exact ShrinkHidden.parse_iff Z side widths v w _ bits ids fields tail

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
