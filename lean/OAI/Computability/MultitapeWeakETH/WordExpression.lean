import OAI.Computability.MultitapeWeakETH.TerminalColumns
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe

/-! # Interpreting descriptor address expressions directly on bit tapes -/

namespace OAI.Computability.MultitapeWeakETH.WordExpression

open IntegerMultiplication Code Carry Staff Strip VPVNP RAMTape BurstRAM PrivateRAM
open StackInterpreter CompressorRecords PhaseRecipe
noncomputable section

abbrev Operands := Bits.Word × Bits.Word
private abbrev regime (X : Type) [Codec X] : Regime X := ⟨size,send,Dom.base _⟩

/-- The fixed kernel's clock depends on the width of the first operand. -/
private def ticks (q : Operands) := 40*(q.1.length+1)^2

private theorem ticks_poly : Poly (fun q => tally (ticks q)) := by
  have w : Realizes (regime Operands) (fun q => q.1.length) := by
    change Poly (fun q : Operands => tally q.1.length)
    convert (Easy.ruler (Easy.fst (X:=Bits.Word) (Y:=Bits.Word))).poly using 1
    funext q
    rw [← ruler_length q.1,recover_tally]
  let n := w.plus (Realizes.fix 1)
  change Realizes (regime Operands) ticks
  change Realizes (regime Operands) (fun q => 40*((q.1.length+1)^2))
  simpa only [pow_two] using (Realizes.fix 40).times (n.times n)

/-- Simulate any of the ten fixed-width arithmetic and bitwise opcodes, including
the native conventions for zero division and shifts beyond the word width. -/
theorem binary_program (op : BinaryOp) :
    ∃ operate : Operands → Bits.Word, Poly operate ∧ ∀ {w : ℕ} (a b : Word w),
      operate (wordBits a,wordBits b) = wordBits (op.eval a b) := by
  let K := TapeWord.wordKernel op
  let bank (q : Operands) := pack (TapeWord.operandStacks K.lhs K.rhs q.1 q.2)
  have bp : Poly bank := by
    apply pack_poly
    intro i
    by_cases h : i=K.lhs
    · simpa only [TapeWord.operandStacks,h,ite_true] using (Easy.fst (X:=Bits.Word) (Y:=Bits.Word)).poly
    · by_cases h' : i=K.rhs
      · simpa only [TapeWord.operandStacks,ite_eq_right h,ite_eq_left h'] using (Easy.snd (X:=Bits.Word) (Y:=Bits.Word)).poly
      · simpa only [TapeWord.operandStacks,ite_eq_right h,ite_eq_right h'] using (Code.Poly.const (X:=Operands) ([] : Bits.Word))
  let start (q : Operands) : Snapshot K.Q := (⟨K.entry⟩,bank q)
  have sp : Poly start := (Code.Poly.const (Label.mk K.entry)).pair bp
  let result (q : Operands) := run K.code (tally (ticks q),start q)
  have rp : Poly result := (ticks_poly.pair sp).compose (run_poly K.code)
  refine ⟨fun q => get K.out (result q).2,rp.sndCompose.compose (get_easy K.out).poly,?_⟩
  intro w a b
  obtain ⟨j,exit,t,hj,exec,halt,out,_⟩ := K.run a b
  have ok := run_at_halt exec halt (ticks (wordBits a,wordBits b)) (by simpa only [ticks,length_wordBits] using hj)
  change get K.out (run K.code _).2 = _
  rw [ok,get_pack,out]

private theorem literal (n : ℕ) : Poly (fun bs : Bits.Word => Bits.short bs.length n) := by
  have w : Realizes (regime Bits.Word) List.length := by
    change Poly (fun bs : Bits.Word => tally bs.length)
    convert (Easy.ruler (Easy.identity (X:=Bits.Word))).poly using 1
    funext bs
    rw [← ruler_length bs,recover_tally]
    rfl
  exact (Figure.natural n).write w

/-- Compile a fixed recipe from the public words, state pointer and an addressable
memory on tapes. Correctness is pointwise, so the memory may depend on the input. -/
theorem expression_program {X : Type} [Codec X] (e : Expr)
    (pub : Fin 5 → X → Bits.Word) (state : X → Bits.Word) (read : X × Bits.Word → Bits.Word)
    (pp : ∀ i, Poly (pub i)) (sp : Poly state) (rp : Poly read) :
    ∃ eval : X → Bits.Word, Poly eval ∧ ∀ (x : X) {w : ℕ}
      (p : Fin 5 → Word w) (s : Word w) (m : Memory w),
      (∀ i, pub i x = wordBits (p i)) → state x = wordBits s →
      (∀ addr : Word w, read (x,wordBits addr) = wordBits (m addr.val)) →
      eval x = wordBits (e.eval p s m) := by
  induction e with
  | lit n =>
    refine ⟨_,sp.compose (literal n),?_⟩
    intro x w p s m _ hs _
    rw [hs,length_wordBits]
    apply Bits.word_inject
    · simp
    · simp [NativeGrid.value_native,Expr.eval]
  | publicWord i => exact ⟨pub i,pp i,fun x _ _ _ _ h _ _ => h i⟩
  | state => exact ⟨state,sp,fun _ _ _ _ _ _ h _ => h⟩
  | load e ih =>
    obtain ⟨v,cost,ev⟩ := ih
    refine ⟨_,(Poly.identity.pair cost).compose rp,?_⟩
    intro x w p s m hp hs hr
    exact (congrArg (fun z => read (x,z)) (ev x p s m hp hs hr)).trans (hr _)
  | binary op a b ih jh =>
    obtain ⟨v,vc,ev⟩ := ih
    obtain ⟨u,uc,eu⟩ := jh
    obtain ⟨operate,cc,ec⟩ := binary_program op
    refine ⟨_,(vc.pair uc).compose cc,?_⟩
    intro x w p s m hp hs hr
    rw [ev x p s m hp hs hr,eu x p s m hp hs hr,ec]
    rfl

end
end OAI.Computability.MultitapeWeakETH.WordExpression
