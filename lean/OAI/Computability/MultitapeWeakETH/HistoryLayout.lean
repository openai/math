import OAI.Computability.MultitapeWeakETH.SelectedChildren

/-! # Computing addresses in any selected chronological pass -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Carry Staff Strip VPVNP Compression CompressorRecords
open DyadicBudget BurstRAM DescriptorSpace
open private clocks from OAI.Computability.MultitapeWeakETH.DescriptorProgram
open private encoded_short from OAI.Computability.MultitapeWeakETH.TerminalLayout
open scoped Fin.CommRing
noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

def gridLayout (volume : Tally) : Layout :=
  let s := index (4*stepSize B) volume.length
  BlockProgram.layout B 0 (source B s).positions s

def historyHeader (q : Tally × Tally) : Bits.Word :=
  let s := index (4*stepSize B) q.1.length
  let w := CursorBounds.wordBits 1 (scale B s)
  BurstRAM.wordBits ((levelStart (gridLayout B q.1) q.2.length : ℕ) : Word w)

private abbrev pointReg : Regime (Tally × Tally) := ⟨size,send,Dom.base _⟩

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale

set_option maxHeartbeats 1200000 in
theorem historyHeader_poly : Poly (historyHeader B) := by
  obtain ⟨_,base,stride,_⟩ := layout_sizes B
  obtain ⟨_,_,width⟩ := clocks B
  have b : Realizes pointReg (fun q => levelsBase (gridLayout B q.1)) :=
    Easy.fst.poly.compose (show Poly (fun q => tally (levelsBase (gridLayout B q))) from base)
  have step : Realizes pointReg (fun q => levelWords (gridLayout B q.1)) :=
    Easy.fst.poly.compose (show Poly (fun q => tally (levelWords (gridLayout B q))) from stride)
  have i : Realizes pointReg (fun q => q.2.length) := by
    change Poly (fun q : Tally × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Tally) (Y:=Tally)).poly
  have w : Realizes pointReg (fun q => CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.1.length))) :=
    Easy.fst.poly.compose (show Poly (fun q : Tally => tally (CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.length)))) from width)
  have addr : Realizes pointReg (fun q => levelStart (gridLayout B q.1) q.2.length) := b.plus (i.times step)
  have bits : Poly (fun q : Tally × Tally => Bits.short (CursorBounds.wordBits 1 (scale B (index (4*stepSize B) q.1.length)))
      (levelStart (gridLayout B q.1) q.2.length)) := (Figure.of_spoken addr).write w
  convert bits using 1
  funext q
  exact encoded_short _ _

/-- Common physical lookup context of a selected pass at a particular chronological level. -/
def historyQuery (q : (LogQuery × Tally) × Tally) : ChildScan.Query LogQuery :=
  let volume := q.1.1.1
  let s := index (4*stepSize B) volume.length
  ((((tally s,q.1.1.2),historyHeader B (volume,q.1.2)),tally (endAddress (gridLayout B volume))),q.2)

theorem historyQuery_poly : Poly (historyQuery B) := by
  let X := (LogQuery × Tally) × Tally
  obtain ⟨ix,_,_⟩ := clocks B
  obtain ⟨_,_,_,size⟩ := layout_sizes B
  have volume : Poly (fun q : X => q.1.1.1) := by fun_prop
  have s := volume.compose (show Poly (fun q : Tally => tally (index (4*stepSize B) q.length)) from ix)
  have cap := volume.compose (show Poly (fun q : Tally => tally (endAddress (gridLayout B q))) from size)
  have head := (volume.pair (show Poly (fun q : X => q.1.2) by fun_prop)).compose (historyHeader_poly B)
  exact (((s.pair (show Poly (fun q : X => q.1.1.2) by fun_prop)).pair head).pair cap).pair Easy.snd.poly

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
