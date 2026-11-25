import OAI.Computability.BorderVNP.CellBranchPrimitives
import OAI.Computability.BorderVNP.CellExpressionCall

/-! # Fixed private dispatcher for a dynamically encoded equality branch

The branch record stores one binary address expression followed by a framed
true child and a raw false child. The machine runs its expression evaluator
once, discards the unchosen child, then invokes the same child interpreter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape RationalHitting.StackLanguage CellSparse

/-- A natural-number equality test represented by a single nonnegative expression. -/
def difference (a b : NatExpr) : NatExpr := .add (.sub a b) (.sub b a)

/-- The canonical binary result is the empty word exactly on equality. -/
theorem difference_bits_empty (a b : NatExpr) (env : List ℕ) :
    ((difference a b).eval env).bits = [] ↔ a.eval env = b.eval env := by
  constructor
  · intro h
    have hzero := wordValue_bits ((difference a b).eval env)
    rw [h] at hzero
    change 0 = a.eval env - b.eval env + (b.eval env - a.eval env) at hzero
    omega
  · intro h
    change (a.eval env - b.eval env + (b.eval env - a.eval env)).bits = []
    rw [h, Nat.sub_self]
    rfl

/-- The equality expression adds two layers to the larger syntax depth. -/
theorem depth_difference (a b : NatExpr) :
    Address.depth (difference a b) = max (Address.depth a) (Address.depth b) + 2 := by
  simp [difference, Address.depth, max_comm]

/-- Its binary digit cost is bounded by those of the two evaluated operands. -/
theorem difference_bits_length (a b : NatExpr) (env : List ℕ) :
    ((difference a b).eval env).bits.length ≤ (a.eval env).bits.length + (b.eval env).bits.length := by
  by_cases h : a.eval env ≤ b.eval env
  · have hv : (difference a b).eval env ≤ b.eval env := by simp only [difference, NatExpr.eval]; omega
    exact (nat_bits_mono hv).trans (Nat.le_add_left ..)
  · have hv : (difference a b).eval env ≤ a.eval env := by simp only [difference, NatExpr.eval]; omega
    exact (nat_bits_mono hv).trans (Nat.le_add_right ..)

/-- Word framing of the condition, the true child, and the remaining false child. -/
def branchPayload (cond yes no : List Bool) := codeWord cond ++ (codeWord yes ++ no)

namespace Branch

private abbrev Ports := IO ⊕ Unit
private abbrev row : Ports := .inl .row
private abbrev temp : Ports := .inr ()

/-- Call a child with the temporary stack as its row and the caller's environment and output. -/
private def tempPorts : IO → Ports
  | .row => temp
  | .env => .inl .env
  | .out => .inl .out

private theorem tempPorts_injective : Function.Injective tempPorts := by
  intro a b h
  cases a <;> cases b <;> simp_all [tempPorts, temp]

/-- The visible registers plus the single private word. -/
private def work (stream env out tmp : List Bool) : Stacks Ports := Sum.elim (io stream env out) fun _ => tmp

private theorem setRow (s e o t x : List Bool) :
    Function.update (work s e o t) row x = work x e o t := by
  funext i
  rcases i with i | ⟨⟩
  · cases i <;> simp [work, row, io]
  · simp [work, row]

private theorem setTemp (s e o t x : List Bool) :
    Function.update (work s e o t) temp x = work s e o x := by
  funext i
  rcases i with i | ⟨⟩ <;> simp [work, temp]

private theorem mount_temp (f : Fragment IO) {n : ℕ} {i e o r e' o' : List Bool}
    (hf : f.Runs n (io i e o) (io r e' o')) (s : List Bool) :
    (f.mount tempPorts).Runs n (work s e o i) (work s e' o' r) := by
  apply f.runs_mount tempPorts_injective hf
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · rintro (k | ⟨⟩) hk
    · cases k with
      | row => rfl
      | env => exact (hk .env rfl).elim
      | out => exact (hk .out rfl).elim
    · exact (hk .row rfl).elim

private theorem mount_row (f : Fragment IO) {n : ℕ} {i e o r e' o' : List Bool}
    (hf : f.Runs n (io i e o) (io r e' o')) (tmp : List Bool) :
    (f.mount (Sum.inl : IO → Ports)).Runs n (work i e o tmp) (work r e' o' tmp) := by
  apply f.runs_mount Sum.inl_injective hf
  · exact fun _ => rfl
  · exact fun _ => rfl
  · rintro (k | ⟨⟩) hk
    · exact (hk k rfl).elim
    · rfl

private theorem split_work (w rest e o : List Bool) :
    ∃ t ≤ 2*(7*w.length+10), (Fragment.split row temp).Runs t
      (work (codeWord w ++ rest) e o []) (work rest e o w) := by
  obtain ⟨t, ht, hr⟩ := Fragment.split_run (src := row) (dst := temp) (by decide)
    (work (codeWord w ++ rest) e o []) w rest rfl rfl
  exact ⟨t, ht, by simpa only [setRow, setTemp] using hr⟩

/-- Run the true child on the extracted temporary word, clearing the false child first. -/
private def onEqual (child : Fragment IO) : Fragment Ports :=
  (Fragment.split row temp).seq ((Fragment.clearStack row).seq (child.mount tempPorts))

/-- Skip the framed true child, then run the false child directly on the remaining public row. -/
private def onDifferent (child : Fragment IO) : Fragment Ports :=
  (Fragment.clearStack temp).seq ((Fragment.split row temp).seq
    ((Fragment.clearStack temp).seq (child.mount Sum.inl)))

/-- A fixed routine running one encoded equality branch with the supplied finite
expression evaluator and recursive child routine. -/
def dispatch (evaluator child : Fragment IO) : Fragment IO :=
  ((Fragment.split row temp).seq ((evaluator.mount tempPorts).seq
    (Fragment.ifEmpty temp (onEqual child) (onDifferent child)))).hide

/-- The additional operations scan the two child words, the condition and its binary value
only a bounded number of times. Exactly one child runtime is charged. -/
def overhead (cond yes no value : List Bool) : ℕ :=
  20*(cond.length + yes.length + no.length + value.length + 3)

private theorem equal_run (child : Fragment IO) {n : ℕ} (yes no env out out' : List Bool)
    (h : child.Runs n (io yes env out) (io [] env out')) :
    ∃ t ≤ n + 2*(7*yes.length+10) + 4*no.length+2,
      (onEqual child).Runs t (work (codeWord yes ++ no) env out []) (work [] env out' []) := by
  obtain ⟨a, ha, split⟩ := split_work yes no env out
  obtain ⟨b, hb, clear⟩ := Fragment.clearStack_run row (work no env out yes)
  rw [setRow] at clear
  change b ≤ 4*no.length+2 at hb
  exact ⟨a+(b+n), by omega, Fragment.runs_seq _ _ split
    (Fragment.runs_seq _ _ clear (mount_temp child h []))⟩

private theorem different_run (child : Fragment IO) {n : ℕ} (yes no val env out out' : List Bool)
    (h : child.Runs n (io no env out) (io [] env out')) :
    ∃ t ≤ n + 4*val.length + 2*(7*yes.length+10) + 4*yes.length+4,
      (onDifferent child).Runs t (work (codeWord yes ++ no) env out val) (work [] env out' []) := by
  obtain ⟨a, ha, clear₁⟩ := Fragment.clearStack_run temp (work (codeWord yes ++ no) env out val)
  rw [setTemp] at clear₁
  change a ≤ 4*val.length+2 at ha
  obtain ⟨b, hb, split⟩ := split_work yes no env out
  obtain ⟨c, hc, clear₂⟩ := Fragment.clearStack_run temp (work no env out yes)
  rw [setTemp] at clear₂
  change c ≤ 4*yes.length+2 at hc
  exact ⟨a+(b+(c+n)), by omega, Fragment.runs_seq _ _ clear₁ (Fragment.runs_seq _ _ split
    (Fragment.runs_seq _ _ clear₂ (mount_row child h [])))⟩

/-- The dispatcher evaluates the condition once and runs precisely the selected
child. Its private word is empty at both ends of the call. -/
theorem dispatch_run (evaluator child : Fragment IO) (cond yes no value env out out' : List Bool)
    {te tc : ℕ} (he : evaluator.Runs te (io cond env out) (io value env out))
    (hc : child.Runs tc (io (if value = [] then yes else no) env out) (io [] env out')) :
    ∃ t ≤ te+tc+overhead cond yes no value, (dispatch evaluator child).Runs t
      (io (branchPayload cond yes no) env out) (io [] env out') := by
  obtain ⟨a, ha, split⟩ := split_work cond (codeWord yes ++ no) env out
  have ev := mount_temp evaluator he (codeWord yes ++ no)
  let w := work (codeWord yes ++ no) env out value
  let f := Fragment.ifEmpty temp (onEqual child) (onDifferent child)
  have finish : ∃ t ≤ tc+2*(7*yes.length+10)+4*no.length+4*value.length+4*yes.length+6,
      f.Runs t w (work [] env out' []) := by
    by_cases hv : value = []
    · subst value
      obtain ⟨t, ht, hr⟩ := equal_run child yes no env out out' (by simpa using hc)
      exact ⟨t+1, by simp; omega, Fragment.ifEmpty_empty (k := temp) (by rfl) hr⟩
    · obtain ⟨t, ht, hr⟩ := different_run child yes no value env out out' (by simpa [hv] using hc)
      exact ⟨t+2, by omega, Fragment.ifEmpty_nonempty (k := temp) hv hr⟩
  obtain ⟨b, hb, ret⟩ := finish
  refine ⟨a+(te+b), ?_, Fragment.runs_hide (Fragment.runs_seq _ _ split (Fragment.runs_seq _ _ ev ret))⟩
  unfold overhead
  omega

/-- The actual compact address encoding gives the branch semantics of
`CellSparse.Stmt.ifEq` on every lexical loop environment. -/
theorem dispatch_equalities (evaluator child : Fragment IO) (d : ℕ) (a b : NatExpr) (env : List ℕ)
    (yes no out out' : List Bool) {te tc : ℕ}
    (he : evaluator.Runs te (io (Coding.code (Address.pack d (difference a b))) (Coding.code env) out)
      (io ((difference a b).eval env).bits (Coding.code env) out))
    (hc : child.Runs tc (io (if a.eval env = b.eval env then yes else no) (Coding.code env) out)
      (io [] (Coding.code env) out')) :
    ∃ t ≤ te+tc+overhead (Coding.code (Address.pack d (difference a b))) yes no
      ((difference a b).eval env).bits, (dispatch evaluator child).Runs t
      (io (branchPayload (Coding.code (Address.pack d (difference a b))) yes no) (Coding.code env) out)
      (io [] (Coding.code env) out') := by
  apply dispatch_run _ _ _ _ _ _ _ _ _ he
  simpa only [difference_bits_empty] using hc

/-- Evaluate a bounded-depth comparison with the installed arithmetic procedure.
The sole recursive premise is the run of the selected child on its original environment. -/
theorem eval_dispatch (d : ℕ) (child : Fragment IO) (a b : NatExpr) (env : List ℕ)
    (yes no out out' : List Bool) {tc : ℕ} (hd : max (Address.depth a) (Address.depth b)+2 ≤ d)
    (hc : child.Runs tc (io (if a.eval env = b.eval env then yes else no) (Coding.code env) out)
      (io [] (Coding.code env) out')) :
    ∃ t ≤ (evalClock d).eval ((Coding.code (Address.pack d (difference a b),env)).length+1) + tc +
      overhead (Coding.code (Address.pack d (difference a b))) yes no ((difference a b).eval env).bits,
      (dispatch (eval d) child).Runs t
        (io (branchPayload (Coding.code (Address.pack d (difference a b))) yes no) (Coding.code env) out)
        (io [] (Coding.code env) out') := by
  obtain ⟨e, he, run⟩ := eval_run d (difference a b) env out (depth_difference a b ▸ hd)
  obtain ⟨t, ht, ret⟩ := dispatch_equalities (eval d) child d a b env yes no out out' run hc
  exact ⟨t, ht.trans (Nat.add_le_add_right (Nat.add_le_add_right he tc) _), ret⟩

end Branch
end CellMacro.Generator

end BorderVNP
end Computability
end OAI
