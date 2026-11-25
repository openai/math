import OAI.Computability.BorderVNP.CellLoopBound

/-! # Emitting fixed instructions and indexed reads on the reversed bytecode stack

The fixed case consumes the instruction bits in their original order. For a
computed read offset, the generator privately decodes its binary magnitude,
then emits the instruction tag, the unary offset, and the terminating zero.
Neither emitter traverses any bytecode accumulated before the call.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape RationalHitting.StackLanguage

private def reverseOnto {K : Type} (src dst : K) : Fragment K :=
  Fragment.plain (Structured.lower (reverse src dst))

private theorem reverseOnto_run {K : Type} [DecidableEq K] {src dst : K} (hd : src ≠ dst)
    (s : Stacks K) :
    ∃ t ≤ 4*(s src).length+2, (reverseOnto src dst).Runs t s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst)) := by
  obtain ⟨t, ht, hr⟩ := Structured.run (eval_reverse hd s)
  exact ⟨t, by omega, Fragment.runs_plain hr⟩

/-- Copy an entire literal instruction from the row to the reversed output stream. -/
def fixedLeaf : Fragment IO := reverseOnto .row .out

/-- The time for a literal instruction depends only on the number of bits emitted. -/
theorem fixedLeaf_run (bits env out : List Bool) :
    ∃ t ≤ 4*bits.length+2, fixedLeaf.Runs t (io bits env out) (io [] env (bits.reverse ++ out)) := by
  obtain ⟨t, ht, hr⟩ := reverseOnto_run (src := IO.row) (dst := IO.out) (by decide) (io bits env out)
  refine ⟨t, ht, ?_⟩
  unfold fixedLeaf
  convert hr using 1
  funext j
  cases j <;> simp [io]

private abbrev Ports := IO ⊕ Unit
private abbrev rowPort : Ports := .inl .row
private abbrev outPort : Ports := .inl .out
private abbrev countPort : Ports := .inr ()

private def state (r e o c : List Bool) : Stacks Ports :=
  Sum.elim (io r e o) fun _ => c

private theorem setRow (r e o c x : List Bool) :
    Function.update (state r e o c) rowPort x = state x e o c := by
  funext i
  rcases i with j | ⟨⟩
  · cases j <;> simp [state, io, rowPort]
  · simp [state, rowPort]

private theorem setCount (r e o c x : List Bool) :
    Function.update (state r e o c) countPort x = state r e o x := by
  funext i
  rcases i with j | ⟨⟩ <;> simp [state, countPort]

private theorem setOut (r e o c x : List Bool) :
    Function.update (state r e o c) outPort x = state r e x c := by
  funext i
  rcases i with j | ⟨⟩
  · cases j <;> simp [state, io, outPort]
  · simp [state, outPort]

private def pushOut (b : Bool) : Fragment Ports :=
  Fragment.plain (.ofRoutine (Routine.push outPort b))

private theorem pushOut_run (b : Bool) (r e o c : List Bool) :
    (pushOut b).Runs 1 (state r e o c) (state r e (b::o) c) := by
  have h := Routine.runs_push outPort b (state r e o c)
  rw [setOut] at h
  exact Fragment.runs_plain h

private def readHeader : Fragment Ports :=
  (pushOut true).seq ((pushOut true).seq (pushOut false))

private theorem readHeader_run (r e o c : List Bool) :
    readHeader.Runs 3 (state r e o c) (state r e (false::true::true::o) c) :=
  Fragment.runs_seq _ _ (pushOut_run true ..) (Fragment.runs_seq _ _ (pushOut_run true ..) (pushOut_run false ..))

private def emitRead : Fragment IO :=
  ((loopBound rowPort countPort).seq (readHeader.seq ((reverseOnto countPort outPort).seq (pushOut false)))).hide

private theorem emitRead_run (k : ℕ) (e o : List Bool) :
    ∃ t ≤ (7*k+8)*k.bits.length+4*k+9, emitRead.Runs t (io k.bits e o)
      (io [] e ((Op.read k).bits.reverse ++ o)) := by
  obtain ⟨a, ha, hdecode⟩ := loopBound_run (src := rowPort) (dst := countPort) (by decide)
    (state k.bits e o []) k rfl rfl
  rw [setRow, setCount] at hdecode
  let tag := false :: true :: true :: o
  obtain ⟨b, hb, htransfer⟩ := reverseOnto_run (src := countPort) (dst := outPort) (by decide)
    (state [] e tag (List.replicate k true))
  rw [setCount, setOut] at htransfer
  change b ≤ 4*(List.replicate k true).length+2 at hb
  rw [List.length_replicate] at hb
  change (reverseOnto countPort outPort).Runs b _ (state [] e ((List.replicate k true).reverse ++ tag) []) at htransfer
  rw [List.reverse_replicate] at htransfer
  have hlast := pushOut_run false [] e (List.replicate k true ++ tag) []
  have eqBits : false :: (List.replicate k true ++ tag) = (Op.read k).bits.reverse ++ o := by
    simp [Op.bits, tag, List.append_assoc]
  rw [eqBits] at hlast
  refine ⟨a+(3+(b+1)), by omega, Fragment.runs_hide ?_⟩
  exact Fragment.runs_seq _ _ hdecode (Fragment.runs_seq _ _ (readHeader_run ..)
    (Fragment.runs_seq _ _ htransfer hlast))

/-- Evaluate the address from the row and emit one unary-offset read instruction. -/
def readLeaf (evaluator : Fragment IO) : Fragment IO := evaluator.seq emitRead

/-- An indexed read pays for evaluating the address, decoding it to unary and
emitting that many markers. Its enclosing environment is preserved. -/
theorem readLeaf_run (evaluator : Fragment IO) (payload env out : List Bool) (k : ℕ) {te : ℕ}
    (he : evaluator.Runs te (io payload env out) (io k.bits env out)) :
    ∃ t ≤ te+(7*k+8)*k.bits.length+4*k+9, (readLeaf evaluator).Runs t
      (io payload env out) (io [] env ((Op.read k).bits.reverse ++ out)) := by
  obtain ⟨b, hb, hr⟩ := emitRead_run k env out
  exact ⟨te+b, by omega, Fragment.runs_seq _ _ he hr⟩

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
