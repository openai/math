import OAI.Computability.MultitapeWeakETH.ReplayProgram
import OAI.Computability.MultitapeWeakETH.DescriptorReplay
import OAI.Computability.MultitapeWeakETH.GridProgram

/-! # The sparse formula descriptor program on the variable-count decision tapes -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Carry Staff Strip VPVNP Compression CompressorRecords BurstRAM
open DyadicBudget
noncomputable section

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)

private abbrev regime : Regime Tally := ⟨size,send,Dom.base _⟩

private theorem clocks :
    let s (q : Tally) := index (4*stepSize B) q.length
    let n (q : Tally) := scale B (s q)
    Realizes regime s ∧ Realizes regime (fun q => n q+24) ∧ Realizes regime (fun q => CursorBounds.wordBits 1 (n q)) := by
  intro s n
  let b := 4*stepSize B
  have ix : Realizes regime s := CNFNetwork.SyntaxProgram.index_program b
  have un := (Realizes.fix (stepSize B)).times ix
  have number : Figure regime n := (Figure.natural 2).repeated ((Realizes.fix 16).times un)
  have volume : Dom regime.scale (fun q => q.length) := (Dom.base _).mono fun q => (duration q).le
  have sizeN : Dom regime.scale n := by
    refine ((((Dom.const _ (2^b)).mul (volume.add (Dom.const _ 1))).pow 4)).mono ?_
    intro q
    by_cases h : 1 < q.length
    · exact (scale_polynomial B h).trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_succ _)) _)
    have small : q.length=0 ∨ q.length=1 := by omega
    rcases small with e|e <;> simp [n,s,e,index,scale] <;> apply Nat.succ_le_of_lt <;> positivity
  have W := ((Realizes.fix 1).times number.short_log).plus (Realizes.fix 10)
  refine ⟨ix,(number.pay sizeN).plus (Realizes.fix 24),?_⟩
  convert (((W.times W).times W).times W) using 1
  funext q
  dsimp only [CursorBounds.wordBits,CursorBounds.addressBits,BurstRAM.addressWidth]
  ring

abbrev Candidate := Tally × Bits.Word

attribute [local irreducible] BlockProgram.script OnlineWorkspace.table entryMemory scale

/-- A single polynomial-time binary tape program returns the written words
of the final descriptor memory from a unary volume and a binary history.
It rejects exactly the candidates rejected by the native scheduler. -/
theorem descriptor_program :
    ∃ evaluate : Candidate → Option WriteBytes, Poly evaluate ∧ ∀ q,
      let s := index (4*stepSize B) q.1.length
      let u := stepSize B*s
      let n := scale B s
      let w := CursorBounds.wordBits 1 n
      let P := OnlineWorkspace.program (BlockProgram.script B).plan (fun _ : Fin 11 => (0 : Word w))
      let m := entryMemory B (3*u) u n s w
      evaluate q = (replay P (n+24) (some 0) m q.2).map
        (fun rs => writes (CallProgram.storeEvents [] (eventLog rs))) := by
  let s (q : Candidate) := index (4*stepSize B) q.1.length
  let n (q : Candidate) := scale B (s q)
  let w (q : Candidate) := CursorBounds.wordBits 1 (n q)
  let m (q : Candidate) := entryMemory B (3*(stepSize B*s q)) (stepSize B*s q) (n q) (s q) (w q)
  let T := OnlineWorkspace.table (BlockProgram.script B).plan
  obtain ⟨ix,fuel,width⟩ := clocks B
  obtain ⟨read,hr,spec⟩ := descriptor_memory_program B
  obtain ⟨eval,poly,valid⟩ := CallProgram.compile T read hr (fun q : Candidate => tally (s q)) w
    (fun q => n q+24) Prod.snd m (Easy.fst.poly.compose ix) (Easy.fst.poly.compose width)
    (Easy.fst.poly.compose fuel) Easy.snd.poly (fun q => spec (s q))
  exact ⟨eval,poly,valid⟩

/-- Reading a word from a returned binary write log denotes the native
post-memory, including repeated writes to the same address. -/
def readLog {w : ℕ} (base : Memory w) (log : WriteBytes) : Memory w :=
  log.foldr (fun p m i => if i = Bits.value p.1 then Fin.ofNat _ (Bits.value p.2) else m i) base

theorem readLog_writes {w : ℕ} (base : Memory w) (log : CallProgram.Stores w) :
    readLog base (writes log) = memory base log := by
  induction log with
  | nil => rfl
  | cons p ls ih =>
    obtain ⟨a,v⟩ := p
    change (fun i => if i=Bits.value (wordBits a) then Fin.ofNat _ (Bits.value (wordBits v)) else readLog base (writes ls) i) = _
    simp only [value_native,ih,Fin.ofNat_eq_cast,Fin.cast_val_eq_self]
    rfl

/-- Summing the outputs of a physical replay program preserves the multiplicity
of terminal memories, including coinciding memories on distinct histories. -/
theorem program_sum {w : ℕ} {Q R V : Type} [CommSemiring R] [AddCommMonoid V]
    {a g b n : ℕ} {X : State a g} {E : StateExecution R b n X} [Fintype E.Choices]
    (P : BurstRAM.Program w Q) (fuel : ℕ) (st : Option (Word w)) (m : Memory w)
    (eval : Bits.Word → Option WriteBytes)
    (spec : ∀ bits, eval bits = (replay P fuel st m bits).map
      (fun rs => writes (CallProgram.storeEvents [] (eventLog rs))))
    (trace : BranchSegments.ExecutionTrace P fuel E st m) (L : ℕ)
    (cost : ∀ z, (pathCode (trace.cut.part z).bits).length ≤ L) (value : Memory w → V) :
    ReaderEnumeration.treeSum (fun bits => (eval bits).elim 0 (fun log => value (readLog m log))) L [] =
      ∑ z, value (trace.cut.part z).memory := by
  rw [← replay_sum P fuel st m trace L cost value]
  congr 1
  funext bits
  rw [spec]
  cases replay P fuel st m bits with
  | none => rfl
  | some rs =>
    simp only [Option.map_some,Option.elim_some,readLog_writes,CallProgram.memory_storeEvents]
    rfl

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
