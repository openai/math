import OAI.Computability.BorderVNP.CellSparseExterior
import OAI.Computability.BorderVNP.CellPacketBinaryCount
import OAI.Computability.BorderVNP.CellPrivateProcedure

/-! # Fixed private stack instructions for restoring omitted external zeros -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Private

open CellSparse.Packet.Native ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord)
open private value_bits from OAI.Computability.BorderVNP.CellPacketBinaryCount

private def emptyCounters : Fin 3 → List Bool := fun _ => []

private abbrev ready (src out : List Bool) := bank src out emptyCounters

private theorem replaceInput (src out xs : List Bool) (ct : Fin 3 → List Bool) :
    Function.update (bank src out ct) .input xs = bank xs out ct := by
  funext r; cases r <;> rfl

private theorem replaceOutput (src out xs : List Bool) (ct : Fin 3 → List Bool) :
    Function.update (bank src out ct) .output xs = bank src xs ct := by
  funext r; cases r <;> rfl

private def readWord (dst : Register) : Program Register :=
  .seq (.push .input true) (readScalarCode dst (fun b => [b]))

private theorem readWord_run (dst : Register) (hi : dst ≠ .input) (hc : dst ≠ .control)
    (word rest acc : List Bool) (ct : Fin 3 → List Bool) :
    ∃ c ≤ 7*(word.length+1)+1, ExactQuantumFactoring.BitStackProgram.Runs (readWord dst) (bank (codeWord word++rest) acc ct)
      (Function.update (bank rest acc ct) dst (word.reverse++bank rest acc ct dst)) c := by
  let start := bank (codeWord word++rest) acc ct
  have first := ExactQuantumFactoring.BitStackProgram.Runs.push start Register.input true
  change ExactQuantumFactoring.BitStackProgram.Runs _ _ (Function.update start .input (true::(codeWord word++rest))) 1 at first
  rw [replaceInput] at first
  obtain ⟨t,ht,run⟩ := readScalarCode_runs (bank (true::(codeWord word++rest)) acc ct) dst hi hc
    (fun b => [b]) word rest rfl rfl
  rw [replaceInput] at run
  have same : bank (true::(codeWord word++rest)) acc ct dst = bank rest acc ct dst := by
    cases dst <;> simp_all [bank]
  have singleton (xs : List Bool) : (xs.flatMap (fun b => [b])) = xs := by
    induction xs with | nil => rfl | cons b xs ih => simp [ih]
  rw [singleton,same] at run
  exact ⟨t+1,by simpa using Nat.add_le_add_right ht 1,ExactQuantumFactoring.BitStackProgram.Runs.seq first run⟩

private def zeros : Program Register := .loop (.counter 0) (.push .output false) (.push .output false)

private theorem zeros_run (n : ℕ) (src acc : List Bool) :
    ExactQuantumFactoring.BitStackProgram.Runs zeros (bank src acc (Function.update emptyCounters 0 (List.replicate n true)))
      (ready src (List.replicate n false++acc)) (2*n+1) := by
  induction n generalizing acc with
  | zero =>
    simpa only [zeros,Nat.mul_zero,Nat.zero_add,List.replicate_zero,List.nil_append,show Function.update emptyCounters 0 []=emptyCounters from
      Function.update_eq_self ..] using (ExactQuantumFactoring.BitStackProgram.Runs.loop_nil (p:=.push Register.output false) (q:=.push Register.output false)
      (show ready src acc (.counter 0)=[] from rfl))
  | succ n ih =>
    let ct := Function.update emptyCounters 0 (List.replicate n true)
    let start := bank src acc (Function.update emptyCounters 0 (List.replicate (n+1) true))
    have hs : start (.counter 0)=true::List.replicate n true := by simp [start,bank,List.replicate_succ]
    have ht : Function.update start (.counter 0) (List.replicate n true) = bank src acc ct := by
      funext r
      cases r <;> simp [start,bank,ct,Function.update]
      split <;> simp_all
    have pushed := ExactQuantumFactoring.BitStackProgram.Runs.push (bank src acc ct) Register.output false
    rw [show false::bank src acc ct .output=false::acc from rfl,replaceOutput] at pushed
    have next := ih (false::acc)
    have loop := ExactQuantumFactoring.BitStackProgram.Runs.loop_true (p:=.push Register.output false) hs (ht.symm ▸ pushed) next
    rw [show 2*(n+1)+1=2*n+1+1+1 by omega]
    simpa only [zeros,start,List.replicate_succ',List.append_assoc,List.singleton_append] using loop

/-- Consume the framed binary gap and append that many zero bits to the private
reversed dense bank. Its work may depend on the restored size. -/
def gap : Program Register := .seq (readWord .digits) (.seq (countCode 0) zeros)

theorem gap_run (n : ℕ) (rest acc : List Bool) :
    ∃ t ≤ 32*(n+1)^2, ExactQuantumFactoring.BitStackProgram.Runs gap (ready (codeWord n.bits++rest) acc)
      (ready rest (List.replicate n false++acc)) t := by
  obtain ⟨c,hc,read⟩ := readWord_run .digits (by decide) (by decide) n.bits rest acc emptyCounters
  simp only [bank,List.append_nil] at read
  obtain ⟨t,ht,ct⟩ := countCode_runs 0 n rest acc emptyCounters rfl
  have run := ExactQuantumFactoring.BitStackProgram.Runs.seq read (ExactQuantumFactoring.BitStackProgram.Runs.seq ct (zeros_run n rest acc))
  have size : n.bits.length ≤ n := (value_bits n).2
  exact ⟨_,by nlinarith only [hc,ht,size,Nat.zero_le (n^2)],run⟩

private def live : Program Register := .seq gap (readWord .output)
private def last : Program Register := .seq gap (reverseMove .input .output)

/-- Consume live fragments until the final trailing-zero marker. The remaining
raw report suffix is moved verbatim, and all temporary counters are cleared. -/
def scan : Program Register := .loop .input last live

/-- Actual private cost allowance, including the final raw-report move. -/
def cost (width : ℕ) (tail : List Bool) : ℕ → List Span → ℕ
  | pos,[] => 32*((width-pos)+1)^2+2*tail.length+3
  | pos,s::ss => 32*((s.start-pos)+1)^2+7*(s.bits.length+1)+2+cost width tail s.stop ss

/-- Exact returned stack for every legitimate sparse input. Each code word is
parsed in sequence. No private data or checked multiplicity is guessed here. -/
theorem scan_run (width : ℕ) (tail : List Bool) (ss : List Span) (pos : ℕ) (acc : List Bool) :
    ∃ t ≤ cost width tail pos ss, ExactQuantumFactoring.BitStackProgram.Runs scan (ready (encode width tail pos ss) acc)
      (ready [] ((expand width tail pos ss).reverse++acc)) t := by
  induction ss generalizing pos acc with
  | nil =>
    obtain ⟨c,hc,r⟩ := gap_run (width-pos) tail acc
    let acc' := List.replicate (width-pos) false++acc
    have rev := reverseMove_runs Register.input Register.output (by decide) (ready tail acc')
    change ExactQuantumFactoring.BitStackProgram.Runs _ _ (Function.update (Function.update (ready tail acc') .input []) .output (tail.reverse++acc'))
      (2*tail.length+1) at rev
    rw [replaceInput,replaceOutput] at rev
    have rlast := ExactQuantumFactoring.BitStackProgram.Runs.seq r rev
    let rest := codeWord (width-pos).bits++tail
    have popped : Function.update (ready (encode width tail pos []) acc) .input rest = ready rest acc := replaceInput ..
    have body : ExactQuantumFactoring.BitStackProgram.Runs last
        (Function.update (ready (encode width tail pos []) acc) .input rest) (ready [] (tail.reverse++acc')) (2*tail.length+1+c) := by
      rw [popped]; exact rlast
    have loop := ExactQuantumFactoring.BitStackProgram.Runs.loop_false (q:=live)
      (show ready (encode width tail pos []) acc .input=false::rest from rfl)
      body (ExactQuantumFactoring.BitStackProgram.Runs.loop_nil (show ready [] (tail.reverse++acc') .input=[] from rfl))
    refine ⟨1+(2*tail.length+1+c)+1,by dsimp only [cost]; omega,?_⟩
    simpa only [scan,last,expand,List.reverse_append,List.reverse_replicate,List.append_assoc,acc'] using loop
  | cons s ss ih =>
    let rem := encode width tail s.stop ss
    let a' := List.replicate (s.start-pos) false++acc
    obtain ⟨c,hc,r⟩ := gap_run (s.start-pos) (codeWord s.bits++rem) acc
    obtain ⟨u,hu,copy⟩ := readWord_run .output (by decide) (by decide) s.bits rem a' emptyCounters
    change ExactQuantumFactoring.BitStackProgram.Runs _ _ (Function.update (ready rem a') .output (s.bits.reverse++a')) u at copy
    rw [replaceOutput] at copy
    obtain ⟨v,hv,again⟩ := ih s.stop (s.bits.reverse++a')
    let rest := codeWord (s.start-pos).bits++(codeWord s.bits++rem)
    have popped : Function.update (ready (encode width tail pos (s::ss)) acc) .input rest = ready rest acc :=
      replaceInput ..
    have begin : ready (encode width tail pos (s::ss)) acc .input = true::rest := by simp [encode,rem,rest,List.append_assoc,ready,bank]
    have loop := ExactQuantumFactoring.BitStackProgram.Runs.loop_true (p:=last) begin (popped.symm ▸ ExactQuantumFactoring.BitStackProgram.Runs.seq r copy) again
    refine ⟨v+(u+c)+1,by dsimp only [cost]; omega,?_⟩
    simpa only [scan,live,expand,List.reverse_append,List.reverse_replicate,List.append_assoc,a'] using loop

end RoutingISA.SparseExterior.Private

end BorderVNP
end Computability
end OAI
