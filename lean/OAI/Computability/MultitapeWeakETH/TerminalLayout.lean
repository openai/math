import OAI.Computability.MultitapeWeakETH.TerminalColumns
import OAI.Computability.VPVNP.PairVertexLevelSchedule
import OAI.Computability.VPVNP.PairTerminalPrefixBudget

/-! # The terminal directory on the sparse-volume grid -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Carry Staff Strip VPVNP Compression CompressorRecords
open BurstRAM CursorBounds DyadicBudget DescriptorSpace PairSimulation
open private source_shape from OAI.Computability.MultitapeWeakETH.NativeScale
open private clocks from OAI.Computability.MultitapeWeakETH.DescriptorProgram
open scoped Fin.CommRing
noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Branches have the same terminal position count; their permutations
and widths will be read from their individual memories. -/
def sites (s : ℕ) := (source B s).positions / S.positionFactor^s

def count (s : ℕ) := sites B s * 2^S.degreeExponent 0

def lastDirectory (s w : ℕ) := packedIncidence (BlockProgram.layout B 0 (source B s).positions s)
  w (s*(S.steps+1)) (count B s)

theorem terminal_size {R : Type} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) (s : ℕ)
    (z : (B.execute f hf s (lanes_fit B s) (source B s)).Choices) :
    let Y := (B.execute f hf s (lanes_fit B s) (source B s)).finalState z
    sites B s = Y.positions ∧ count B s = TerminalPrefix.arcCount Y := by
  intro Y
  have pos : sites B s = Y.positions := by
    rw [sites,(B.branch_bounds f hf s (lanes_fit B s) (source B s) z).1]
    exact Nat.mul_div_cancel_left _ (pow_pos (by have := S.positionFactor_gt_two; omega) _)
  exact ⟨pos,by rw [count,pos,TerminalPrefix.Segment.arc_count_positions]⟩

abbrev DirectoryData := (Tally × Tally) × Bits.Word × Bits.Word

/-- From a unary volume compute the grid index, number of terminal arcs,
and the two native column heads as words at the scheduler's actual width. -/
def data (volume : Tally) : DirectoryData :=
  let s := index (4*stepSize B) volume.length
  let T := lastDirectory B s (CursorBounds.wordBits 1 (scale B s))
  ((tally s,tally (count B s)),BurstRAM.wordBits T.width,BurstRAM.wordBits T.actualIn)

private abbrev regime : Regime Tally := ⟨size,send,Dom.base _⟩

attribute [local irreducible] BlockProgram.script source scale

private theorem encoded_short (w x : ℕ) : BurstRAM.wordBits (CursorRAM.encode w x) = Bits.short w x := by
  apply Bits.word_inject
  · simp only [length_wordBits,Bits.short_length]
  · rw [value_native,Bits.value_short]
    rfl

/-- All earlier level headers use the same polynomially bounded base and stride.
The full allocation also gives a unary cap for reading child identifiers. -/
theorem layout_sizes :
    let s (q : Tally) := index (4*stepSize B) q.length
    let L (q : Tally) := BlockProgram.layout B 0 (source B (s q)).positions (s q)
    Realizes regime (fun q => (source B (s q)).positions) ∧
      Realizes regime (fun q => levelsBase (L q)) ∧ Realizes regime (fun q => levelWords (L q)) ∧
      Realizes regime (fun q => endAddress (L q)) := by
  intro s L
  let u (q : Tally) := stepSize B*s q
  obtain ⟨ix,fuel,_⟩ := clocks B
  let nat := fun t => Figure.natural (r:=regime) t
  have un : Realizes regime u := (Realizes.fix (stepSize B)).times ix
  have P : Figure regime (fun q => (source B (s q)).positions) := by
    convert (((nat 8).multiplied (Figure.of_spoken un)).added (nat 4)).multiplied
      ((nat 2).repeated ((Realizes.fix 3).times un)) using 1
    funext q
    exact (source_shape B (s q)).1
  have full : Dom regime.scale (fun q => (source B (s q)).positions) := by
    apply ((diameter _ fuel).add (Dom.const _ 4)).mono
    intro q
    by_cases hs : 1 ≤ s q
    · have le := source_positions B hs
      change _ ≤ scale B (s q)+24+4
      omega
    · have z : s q=0 := by omega
      rw [(source_shape B _).1,z]
      simp
  let P₀ := P.pay full
  let ar := Schedule.arity (BlockProgram.script B).catalog
  let slots := P₀.times (Realizes.fix (slotDegree S))
  have stride : Realizes regime (fun q => levelWords (L q)) :=
    ((Realizes.fix 66).plus ((Realizes.fix 6).times slots)).plus
      ((Realizes.fix 6).times (slots.times (Realizes.fix (BlockProgram.fieldCount B))))
  have rows : Realizes regime (fun q => directoryRows (L q)) := by
    convert (Realizes.fix (BlockProgram.initial B).length).plus
      (ix.times (Realizes.fix (BlockProgram.block B).length)) using 1
    funext q
    exact LevelFields.tight_rows ..
  have head : Realizes regime (fun q => levelsBase (L q)) :=
    (Realizes.fix (9+(ar+1)+1)).plus (rows.times (Realizes.fix (ar+3)))
  have levels : Realizes regime (fun q => (L q).levels) :=
    (Realizes.fix 1).plus ((Realizes.fix (S.steps+1)).times ix)
  exact ⟨P₀,head,stride,head.plus (levels.times stride)⟩

set_option maxHeartbeats 1200000 in
theorem data_poly : Poly (data B) := by
  let s (q : Tally) := index (4*stepSize B) q.length
  let w (q : Tally) := CursorBounds.wordBits 1 (scale B (s q))
  let L (q : Tally) := BlockProgram.layout B 0 (source B (s q)).positions (s q)
  obtain ⟨ix,_,width⟩ := clocks B
  obtain ⟨P,head₀,stride₀,_⟩ := layout_sizes B
  let head := Figure.of_spoken head₀
  let stride := Figure.of_spoken stride₀
  let nat := fun t => Figure.natural (r:=regime) t
  have cnt : Figure regime (fun q => count B (s q)) :=
    ((Figure.of_spoken P).quotients ((nat S.positionFactor).repeated ix)).multiplied (nat (2^S.degreeExponent 0))
  have paid := cnt.pay (((diameter _ P).mul (Dom.const _ (2^S.degreeExponent 0))).mono (fun q =>
    Nat.mul_le_mul_right _ (Nat.div_le_self ..)))
  let last := (Figure.of_spoken ix).multiplied (nat (S.steps+1))
  have start : Figure regime (fun q => incidenceStart (L q) (s q*(S.steps+1))) :=
    (head.added (last.multiplied stride)).added (nat 66)
  have column (c : Fin 6) : Poly (fun q => BurstRAM.wordBits ((lastDirectory B (s q) (w q)).column c)) := by
    let addr := start.added ((nat c.val).multiplied cnt)
    have code : Poly (fun q => Bits.short (w q) (incidenceBase (L q) (s q*(S.steps+1)) (count B (s q)) c)) := addr.write width
    convert code using 1
    funext q
    rw [lastDirectory,packed_column]
    exact encoded_short _ _
  have ip : Poly (fun q => tally (s q)) := ix
  have cp : Poly (fun q => tally (count B (s q))) := paid
  exact (ip.pair cp).pair ((column 5).pair (column 4))

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
