import OAI.Computability.MultitapeWeakETH.HistoryHidden
import OAI.Computability.MultitapeWeakETH.HistoryShrinkBounds
import OAI.Computability.MultitapeWeakETH.ShrinkSiteProgram

/-! # Running selected shrinking sites against chronological descriptor memory -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression BurstRAM CompressorRecords DescriptorSpace
open PairSimulation LocalHistory TraversalRows TraversalRoles NetworkKernel DyadicBudget ShrinkBlockInputs ShrinkMap ShrinkRole Filter
open private hiddenQuery hiddenQuery_poly from OAI.Computability.MultitapeWeakETH.HistoryHidden
open scoped Classical Fin.CommRing
noncomputable section

set_option allowUnsafeReducibility true in
attribute [local reducible] Compression.PackingData.shrinkTermLayout
set_option allowUnsafeReducibility true in
attribute [local irreducible] Compression.ShrinkEnergy.chosenLayout

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)

/-- The three transmitted operands are the keyed old packets, the parent packet and
the keyed hidden fields. The other input locates the selected site in the native log. -/
abbrev ShrinkQuery := HistorySite × ((NamedPackets.Bank × Bits.Word) × NamedPackets.Bank)

private def liftShrink (q : ShrinkHidden.Query LogQuery × ((NamedPackets.Bank × Bits.Word) × NamedPackets.Bank)) :
    ShrinkHidden.Query (Buffers LogQuery) :=
  ((((((q.1.1.1.1,q.2.1.1),q.2.1.2),q.2.2),q.1.1.1.2),q.1.1.2),q.1.2)

private def shrinkQuery (q : ShrinkQuery) := liftShrink (hiddenQuery B q.1,q.2)

private theorem shrinkQuery_poly : Poly (shrinkQuery B) :=
  ((Easy.fst.poly.compose (hiddenQuery_poly B)).pair Easy.snd.poly).compose
    (show Poly liftShrink by unfold liftShrink; fun_prop)

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory executeLevels

set_option maxHeartbeats 1800000 in
/-- The program returns the full row check at every selected occurrence, with a
common grid threshold independent of the chronological level and assignment. -/
theorem history_shrink (i : Fin S.steps) (number : (MotifConversion.parameterData B.shrink).Entry → ℕ)
    (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ run : ShrinkQuery → Option (List Tally), Poly run ∧ ∃ s₀ : ℕ, ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let u := stepSize B*s
      let X := source B s
      let initial : TaggedLayer := ⟨leafLayer (siteOrder X),.cursor⟩
      let L := gridLayout B volume
      let base := entryMemory B (3*u) u n s w
      let E := B.execute f hf s (lanes_fit B s) X
      s₀ ≤ s → ∀ (path : E.Choices) (log : CallProgram.Stores w),
        let past := executeLevels B f hf s (lanes_fit B s) X path
        let m := memory base log
        CompiledResident.resident B f hf 0 X.positions s n initial
          (Frame.data (k:=8) (BlockHeaderRun.header w L 0+6) base) past (E.finalState path) m →
        ∀ (j : Fin past.length) {g : ℕ} (z : SiteArguments B i g) (selector : List Bool),
          (past[j.val]'j.isLt) = shrinkLevel B f hf i z.state z.choice selector →
          let buffers := z.buffers (tally s,writes log) w
          run (((((volume,writes log),tally j.val),tally (MapResidentRows.siteIndex z.state z.owner).val)),
            (buffers.1.1.2,buffers.1.2),buffers.2) = checked (z.results number) := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have rp : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  obtain ⟨kernel,cost,ev⟩ := site_program B i rd rp number
  obtain ⟨N,bounds⟩ := eventually_atTop.mp (history_shrink_bounds B f hf)
  refine ⟨fun q => kernel (shrinkQuery B q),(shrinkQuery_poly B).compose cost,N,?_⟩
  intro volume s n w u X initial L base E hs path log past m resident j g z selector occurrence buffers
  let V := past[j.val]'j.isLt
  have member : V ∈ executeLevels B f hf s (lanes_fit B s) X path := List.getElem_mem j.isLt
  have stored := CompiledResident.read resident.2 j
  change V = shrinkLevel B f hf i z.state z.choice selector at occurrence
  change CompiledResident.payload B f hf (0 : Word w) X.positions s n j.val V m at stored
  rw [occurrence] at member stored
  let d : Level w := ⟨0,X.positions,s,n,j.val,m⟩
  have ready : z.Ready d := bounds s hs path i z selector member j.val m ((CompiledResident.shrink_payload ..).mp stored)
  have ptr : historyHeader B (volume,tally j.val) = wordBits (d.head B) := by
    unfold historyHeader Level.head
    rw [tally_length]
    rfl
  let site := (MapResidentRows.siteIndex z.state z.owner).val
  change kernel (((buffers,historyHeader B (volume,tally j.val)),tally (n*n)),tally site) = _
  rw [ptr]
  exact ev (tally s,writes log) z d ready (spec s log)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
