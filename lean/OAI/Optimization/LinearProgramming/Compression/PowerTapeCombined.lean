import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.Compression.PowerTapeRAM
import OAI.Optimization.LinearProgramming.Compression.PowerTapeBuild
import OAI.Optimization.LinearProgramming.Compression.ProxyRelocation

/-! One fixed RAM program converts literal signed bits to power instructions, multiplies
the selected rational powers, and returns an exact comparison with one. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

/-- Assemble the encoder followed by the relocated interpreter and ordered comparison. -/
def literalPowerCompareProgram : Program :=
  let enc := powerEncoderBlock.compile 0
  enc ++ powerTapeCompareProgram.map (rebaseInstr enc.length)

/-- Relocating the instruction addresses preserves the whole execution and every scalar invariant. -/
theorem relocate_power_execution {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (front prog : Program) {safe : (ℕ → K) → Prop} {s t : State K} {k : ℕ}
    (h : Execution prog (fun s => safe s.data) s k t) :
    Execution (front ++ prog.map (rebaseInstr front.length)) (fun s => safe s.data)
      (stateAt front.length s) k (stateAt front.length t) := by
  induction h with
  | done _ hs => exact .done _ hs
  | @next s u z k hs he rest ih =>
    refine .next hs ?_ ih
    cases hgo : s.output with
    | some tag => simp [step,hgo] at he
    | none =>
      cases hop : prog[s.pc]? with
      | none => simp [step,hgo,hop] at he
      | some op =>
        have hdo : execInstr op s = some u := by simpa [step,hgo,hop] using he
        have hget : (front ++ prog.map (rebaseInstr front.length))[front.length + s.pc]? =
            some (rebaseInstr front.length op) := by
          rw [List.getElem?_append_right (show front.length ≤ front.length + s.pc by omega)]
          simp [hop]
        change (match s.output, (front ++ prog.map (rebaseInstr front.length))[front.length+s.pc]? with
          | none, some i => execInstr i (stateAt front.length s)
          | _, _ => none) = _
        rw [hgo,hget]
        exact (exec_rebase front.length op s).trans (by rw [hdo]; rfl)

/-- Changing the safety predicate by an implication preserves all counted machine steps. -/
theorem weaken_power_execution {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p : Program} {P Q : State K → Prop} {s t : State K} {k : ℕ}
    (h : Execution p P s k t) (f : ∀ s, P s → Q s) : Execution p Q s k t := by
  induction h with
  | done s h => exact .done s (f s h)
  | next h he _ ih => exact .next (f _ h) he ih

private theorem encoded_start (ts : List PowerToken) (bases : List ℚ) :
    start (powerEncoderAddressInput ts) (powerTapeScalarInput bases) =
      (powerEncoderMemory ts (fun i => (powerTapeScalarInput bases)[i]?.getD 0)).atPC 0 := by
  change State.mk 0 _ _ _ = State.mk 0 _ _ _
  congr 1
  funext i
  match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _+8 => rfl

private theorem encoded_ready (ts : List PowerToken) (bases : List ℚ) (pc : ℕ) :
    (powerEncodedMemory ts (fun i => (powerTapeScalarInput bases)[i]?.getD 0)).atPC pc =
      stateAt pc (powerTapeEntry (ts.flatMap PowerToken.ops).length bases (encodedPowerTail ts)) := by
  change State.mk pc _ _ _ = State.mk (pc+0) _ _ _
  congr 1
  funext i
  match i with | 0 | 1 | 2 | 3 | _+4 => rfl

/-- The runtime includes writing each opcode into address memory, testing its tag, every
scalar arithmetic operation, and the final ordered comparison. -/
theorem literalPowerCompareProgram_correct {B : ℕ} {safe : PowerMem → Prop}
    (es : List ℤ) (bases : List ℚ) {out : PowerMem}
    (run : PowerRun safe (productOps es) (.initial bases) out)
    (bounds : ∀ m, safe m → ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B)
    (inputs : ∀ q ∈ bases, ratBits q ≤ B) :
    ∃ k ≤ 30*(es.map fun e => e.natAbs.size+2).sum+9, ∃ tr : Fin (k+1) → State ℚ,
      Trace literalPowerCompareProgram
        (start (powerEncoderAddressInput (signedBitTape es)) (powerTapeScalarInput bases)) k tr ∧
      (tr (Fin.last k)).data 2 = out.product ∧
      (tr (Fin.last k)).output = some (if out.product < 1 then 0 else if 1 < out.product then 2 else 1) ∧
      ∀ i, scalarBound B (tr i) := by
  let ts := signedBitTape es
  let d (i : ℕ) := (powerTapeScalarInput bases)[i]?.getD 0
  let front := powerEncoderBlock.compile 0
  have heq : ts.flatMap PowerToken.ops = productOps es := expand_signedBitTape es
  have codes (i : ℕ) (hi : i < (productOps es).length) :
      encodedPowerTail ts i = (productOps es)[i].code := by
    have hi' : i < (ts.flatMap PowerToken.ops).length := by simpa only [heq] using hi
    simpa only [heq] using encodedPowerTail_code ts i hi'
  obtain ⟨a,ha,s,loop,hpc,hopen,hprod,hunit,_,_⟩ :=
    powerTapeProgram_prefix_from_entry powerTapeCompareSuffix run bounds inputs (encodedPowerTail ts) codes
  obtain ⟨b,hb,u,suffix,htag,hvalue⟩ := powerTapeCompareSuffix_exec
    (P := fun data => ∀ j, ratBits (data j) ≤ B) s loop.safe_end hpc hopen hunit
  have rel := relocate_power_execution front powerTapeCompareProgram (safe := fun data => ∀ j, ratBits (data j) ≤ B)
    (loop.append suffix)
  have location : CodeAt literalPowerCompareProgram 0 (powerEncoderBlock.compile 0) :=
    ⟨[],powerTapeCompareProgram.map (rebaseInstr front.length),rfl,rfl⟩
  obtain ⟨c,hc,enc⟩ := powerEncoderBlock_correct ts d location
  have hw (i : ℕ) : ratBits (d i) ≤ B := by
    have hs := loop.safe_start i
    match i with | 0 | 1 | 2 | 3 | _+4 => exact hs
  have encSafe := weaken_power_execution enc (Q := scalarBound B) (fun s₀ hs₀ i => by
    rw [hs₀]
    exact hw i)
  have hr : Execution literalPowerCompareProgram (scalarBound B)
      ((powerEncodedMemory ts d).atPC (0+powerEncoderBlock.size)) (a+b)
      (stateAt front.length u) := by
    rw [encoded_ready,heq]
    rw [show scalarBound B = (fun z : State ℚ => ∀ j, ratBits (z.data j) ≤ B) from rfl]
    simpa [front, literalPowerCompareProgram] using rel
  have entire := encSafe.append hr
  obtain ⟨tr,htr,hend,hsafe⟩ := entire.to_trace
  have hsl := signedBitTape_length es
  change ts.length = _ at hsl
  have hcard : (productOps es).length ≤ 2*ts.length := by
    rw [← heq]
    exact powerTokens_opCount ts
  refine ⟨c+(a+b),by omega,tr,?_,?_,?_,hsafe⟩
  · simpa only [encoded_start] using htr
  · rw [hend]; exact hvalue.trans hprod
  · rw [hend]
    change u.output = _
    simpa only [hprod] using htag

/-- Specialization to a list of explicit rational bases and signed exponents. No
abstract execution relation is an assumption of this theorem. -/
theorem literalSignedProducts_compare (terms : List (ℚ × ℤ))
    (hnz : ∀ p ∈ terms, p.2 < 0 → p.1 ≠ 0) :
    let value := (terms.map fun p => p.1 ^ p.2).prod
    let es := terms.map Prod.snd
    let bases := terms.map Prod.fst
    ∃ k ≤ 30*(es.map fun e => e.natAbs.size+2).sum+9, ∃ tr : Fin (k+1) → State ℚ,
      Trace literalPowerCompareProgram
        (start (powerEncoderAddressInput (signedBitTape es)) (powerTapeScalarInput bases)) k tr ∧
      (tr (Fin.last k)).data 2 = value ∧
      (tr (Fin.last k)).output = some (if value < 1 then 0 else if 1 < value then 2 else 1) ∧
      ∀ i, scalarBound (3+(terms.map powerTermBudget).sum) (tr i) := by
  obtain ⟨out,run,hr,_⟩ := productOps_run terms hnz
  have hs := run.safe_start
  have h := literalPowerCompareProgram_correct (terms.map Prod.snd) (terms.map Prod.fst) run
    (fun _ hm => ⟨hm.1,hm.2.1,hm.2.2.1⟩) hs.2.2.2
  simpa only [hr] using h

end Compression
end LinearProgramming
end Optimization
end OAI
