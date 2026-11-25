import OAI.Computability.MultitapeWeakETH.TerminalBanks
import OAI.Computability.NearSquareRoot.PrecisionPlacedSlot

/-! # A physical candidate for the outer and shared-wire searches -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget TerminalWords
noncomputable section

private theorem bind_poly {X A Z : Type} [Codec X] [Codec A] [Codec Z] (fallback : A)
    {key : X → Option A} {f : X × A → Option Z} (hk : Poly key) (hf : Poly f) :
    Poly (fun q => (key q).bind (fun a => f (q,a))) := by
  let someKey := hk.compose (NearSquareRoot.PhaseTable.easyOption false (fun _ => true) (Easy.const true)).poly
  let item := hk.compose (NearSquareRoot.PhaseTable.easyOption fallback id Easy.identity).poly
  have out := Poly.choose someKey ((Poly.identity.pair item).compose hf) (Code.Poly.const none)
  convert out using 1
  funext q
  cases key q <;> rfl

abbrev SharedQuery := Candidate × Bits.Word
abbrev SharedData := (WriteBytes × Banks) × Bits.Word

/-- Read the directory and validate the shared word. The lookup context
retains the original log for the later local parser. -/
def withBanks (banks : LogQuery → Banks) (q : SharedQuery × WriteBytes) : Option SharedData :=
  let b := banks (q.1.1.1,q.2)
  (unpack (b.1.flatten,q.1.2)).map (fun bits => ((q.2,b),bits))

private theorem withBanks_poly (banks : LogQuery → Banks) (hb : Poly banks) : Poly (withBanks banks) := by
  let X := SharedQuery × WriteBytes
  have b : Poly (fun q : X => banks (q.1.1.1,q.2)) :=
    ((((Easy.fst.compose Easy.fst).compose Easy.fst).pair Easy.snd).poly).compose hb
  have payload := ((b.fstCompose.compose Easy.flatten.poly).pair (Easy.fst.compose Easy.snd).poly).compose unpack_poly
  have fields := Easy.snd.poly.pair b
  have pack : Poly (fun q : X × Bits.Word => some ((q.1.2,banks (q.1.1.1.1,q.1.2)),q.2)) :=
    ((Easy.fst.poly.compose fields).pair Easy.snd.poly).compose Easy.some.poly
  convert bind_poly [] payload pack using 1
  funext q
  dsimp only [withBanks]
  cases unpack ((banks (q.1.1.1,q.2)).1.flatten,q.1.2) <;> rfl

theorem widths_flatten {a g : ℕ} (X : State a g) : (widths X).flatten = tally X.totalWidth := by
  rw [← recover_tally (widths X).flatten]
  simp only [widths,List.length_flatten,List.map_ofFn,Function.comp_def,tally_length,List.sum_ofFn,PairSimulation.TerminalPrefix.width_sum]

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

attribute [local irreducible] BlockProgram.script OnlineWorkspace.table source scale entryMemory

/-- The two binary candidates and unary volume suffice for a uniform
polynomial-time tape program. Each successful readout includes the
bounded binary payload, its graph columns, and its descriptor history. -/
theorem shared_program :
    ∃ (banks : LogQuery → Banks) (eval : SharedQuery → Option SharedData), Poly banks ∧ Poly eval ∧
    ∀ volume : Tally,
      let s := index (4*stepSize B) volume.length
      let u := stepSize B*s
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let m := entryMemory B (3*u) u n s w
      let P := OnlineWorkspace.program (BlockProgram.script B).plan (fun _ : Fin 11 => (0 : Word w))
      (∀ outer inner, eval ((volume,outer),inner) = (replay P (n+24) (some 0) m outer).bind
        (fun rs => withBanks banks (((volume,outer),inner),writes (CallProgram.storeEvents [] (eventLog rs))))) ∧
      (∀ {a g : ℕ} (Y : State a g) (log : CallProgram.Stores w),
        count B s = PairSimulation.TerminalPrefix.arcCount Y → PairSimulation.TerminalPrefix.arcCount Y ≤ 2^w →
        Y.totalWidth ≤ volume.length → Y.totalWidth < 2^w → (lastDirectory B s w).ActualColumns Y (memory m log) →
        banks (volume,writes log) = (widths Y,inverse Y)) := by
  obtain ⟨banks,hb,read⟩ := banks_program B
  obtain ⟨run,hr,execute⟩ := descriptor_program B
  let eval (q : SharedQuery) := (run q.1).bind (fun log => withBanks banks (q,log))
  refine ⟨banks,eval,hb,bind_poly [] (Easy.fst.poly.compose hr) (withBanks_poly banks hb),?_⟩
  intro volume s u n w m P
  refine ⟨?_,read volume⟩
  intro outer inner
  change (run (volume,outer)).bind _ = _
  rw [execute]
  change ((replay P (n+24) (some 0) m outer).map _).bind _ = _
  cases replay P (n+24) (some 0) m outer <;> rfl

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
