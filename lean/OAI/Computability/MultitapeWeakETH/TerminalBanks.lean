import OAI.Computability.MultitapeWeakETH.TerminalLayout

/-! # Recovering both terminal graph columns from the descriptor's actual write log -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget
open DescriptorSpace PairSimulation LocalHistory TraversalRoles TraversalRows TerminalWords
open scoped Fin.CommRing
noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

attribute [local irreducible] BlockProgram.script BlockProgram.layout source scale entryMemory

/-- The incidence heads computed from the public volume locate the current
graph of every selected branch in its terminal descriptor memory. -/
theorem terminal_actual {R : Type} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) (s : ℕ)
    {w n : ℕ} (z : (B.execute f hf s (lanes_fit B s) (source B s)).Choices)
    (initial : TaggedLayer) (frame : Fin 8 → Word w) (m : Memory w)
    (stored : CompiledResident.resident B f hf 0 (source B s).positions s n initial frame
      (executeLevels B f hf s (lanes_fit B s) (source B s) z)
      ((B.execute f hf s (lanes_fit B s) (source B s)).finalState z) m) :
    (lastDirectory B s w).ActualColumns ((B.execute f hf s (lanes_fit B s) (source B s)).finalState z) m := by
  let Y := (B.execute f hf s (lanes_fit B s) (source B s)).finalState z
  have storedCols := stored.1.2.1.incidence.actual
  have slots : count B s = IncidenceDirectory.slotCount Y := (terminal_size B f hf s z).2
  rw [VertexLevel.selected_pass_count] at storedCols
  simpa only [lastDirectory,slots,Y,Fin.val_zero] using storedCols

abbrev LogQuery := Tally × WriteBytes
abbrev Banks := List Tally × List Tally

/-- A single polynomial-time tape readout of a descriptor log yields the
outgoing widths and the inverse slot directory. The proof applies only
terminal storage obligations, so it also handles colliding final memories. -/
theorem banks_program : ∃ eval : LogQuery → Banks, Poly eval ∧ ∀ (volume : Tally),
    let s := index (4*stepSize B) volume.length
    let u := stepSize B*s
    let n := scale B s
    let w := CursorBounds.wordBits 1 n
    let base := entryMemory B (3*u) u n s w
    ∀ {a g : ℕ} (Y : State a g) (log : CallProgram.Stores w),
      count B s = TerminalPrefix.arcCount Y → TerminalPrefix.arcCount Y ≤ 2^w →
      Y.totalWidth ≤ volume.length → Y.totalWidth < 2^w →
      (lastDirectory B s w).ActualColumns Y (memory base log) →
      eval (volume,writes log) = (widths Y,inverse Y) := by
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  let rd (q : LogQuery × Bits.Word) := read ((q.1.1,q.2),q.1.2)
  have rdp : Poly rd := (((Easy.fst.compose Easy.fst).pair Easy.snd).pair (Easy.fst.compose Easy.snd)).poly.compose hr
  let D (q : LogQuery) := data B q.1
  let ctx (q : LogQuery) : LogQuery := ((D q).1.1,q.2)
  let one (width : Bool) (q : LogQuery) :=
    scan rd (((ctx q, bif width then (D q).2.1 else (D q).2.2), bif width then q.1 else (D q).1.2),(D q).1.2)
  have dp : Poly D := Easy.fst.poly.compose (data_poly B)
  have cp : Poly ctx := dp.fstCompose.fstCompose.pair Easy.snd.poly
  have program (b : Bool) : Poly (one b) := by
    cases b with
    | true => exact (((cp.pair dp.sndCompose.fstCompose).pair Easy.fst.poly).pair dp.fstCompose.sndCompose).compose (scan_poly rd rdp)
    | false => exact (((cp.pair dp.sndCompose.sndCompose).pair dp.fstCompose.sndCompose).pair dp.fstCompose.sndCompose).compose (scan_poly rd rdp)
  refine ⟨fun q => (one true q,one false q),(program true).pair (program false),?_⟩
  intro volume s u n w base a g Y log size fit cap word cols
  let ctx' : LogQuery := (tally s,writes log)
  have rdval (h : Word w) : Bits.value (rd (ctx',wordBits h)) = (memory base log h.val).val :=
    (congrArg Bits.value (spec s log h)).trans (value_native _)
  apply Prod.ext
  · change scan rd (((ctx',wordBits (lastDirectory B s w).width),volume),tally (count B s)) = _
    rw [size,← recover_tally volume]
    exact scan_widths rd Y _ ctx' _ rdval cols volume.length cap word
  · change scan rd (((ctx',wordBits (lastDirectory B s w).actualIn),tally (count B s)),tally (count B s)) = _
    rw [size]
    exact scan_inverse rd Y _ ctx' _ rdval cols fit

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
