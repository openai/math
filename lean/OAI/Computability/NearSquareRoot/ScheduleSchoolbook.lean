import OAI.Computability.NearSquareRoot.ScheduleSchoolStack
import OAI.Computability.NearSquareRoot.ScheduleSchoolRelease

/-!
# Polynomial-time, linear-space fallback for the common schedule

This candidate bounds the number of rounds even on lengths where the parameter
tests of the faster candidates fail. The count includes the initial parse,
each schoolbook pass, emission, and the final physical copy to the output tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication

/-- A fixed physical machine for the first attempt in the schedule. -/
theorem schoolbook_machine :
    ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
      (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q)
      (m : TM.Rule A Q I) (C S : ℕ),
      Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧
      sep ≠ blank ∧ inp ≠ out ∧
      ∀ n : ℕ, 0 < n → ∀ x y : List Bool, x.length = n → y.length = n →
        let init := initialConfig start inp bit sep blank x y
        ∃ t finish z,
          Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
          TM.whole blank (z.map bit) (finish.tape out) ∧
          z.length = 2 * n ∧ bitValue z = bitValue x * bitValue y ∧
          t ≤ C * n ^ 2 ∧ VisitsAtMost m init t (S * n) := by
  classical
  obtain ⟨p, D, stack⟩ := schoolbook_stack
  let I := Prog.Ix p.area
  let A := Prog.Sym p.area
  let : Fintype I := Fintype.ofFinite I
  let bits : Bool → Option A := fun b => some (.inl (.bit b))
  let sep : Option A := some (.inl .sep)
  let m := SM.complete p.output p.rule
  let K := Fintype.card (Option I)
  refine ⟨Option A, Option (SM.PC A p.Control I), Option I, inferInstance, inferInstance,
    inferInstance, bits, sep, none, some p.output, none, some (.inl p.start), m,
    18 * D + 3, K * (8 * D + 5), ?_, ?_, by simp [sep], by simp, ?_⟩
  · intro a b h
    exact Code.Ltr.bit.inj (Sum.inl.inj (Option.some.inj h))
  · intro b
    refine ⟨fun h => ?_, by simp [bits]⟩
    have := Sum.inl.inj (Option.some.inj h)
    contradiction
  intro n hn x y hx hy
  obtain ⟨t, z, seg, cost, width, value⟩ := stack n x y hx hy
  obtain ⟨finish, run, halt, product, visited⟩ :=
    complete_run_space (k := p.output) seg.run (p.halt _) seg.height
  let time := 2*t + 1 + z.length
  let init := initialConfig (some (Sum.inl p.start : SM.PC A p.Control I)) (some p.output) bits sep none x y
  have load : (fun (j : Option I) => if j = some p.output
      then TM.Tape.loaded none (((operandStream x y).map Sum.inl).map some)
      else TM.Tape.loaded none []) = init.tape := by
    funext j
    by_cases hj : j = some p.output <;>
      simp [init, initialConfig, operandStream, bits, sep, hj, List.map_map, Function.comp_def]
  rw [p.done_output, List.length_map, List.length_map] at run visited
  rw [p.done_output] at product
  refine ⟨time, finish, z, ?_, halt, ?_, width, value, ?_, ?_⟩
  · rw [load] at run
    exact run
  · simpa [bits, List.map_map, Function.comp_def] using product
  · have hpow : (n+2)^2 ≤ (3*n)^2 := Nat.pow_le_pow_left (by omega) 2
    have hcost := cost.trans (Nat.mul_le_mul_left D hpow)
    have hlin : n ≤ n^2 := by nlinarith [Nat.mul_le_mul_left n hn]
    dsimp [time]
    rw [width]
    nlinarith
  · rw [load] at visited
    obtain ⟨cells, count, contains⟩ := visited
    refine ⟨cells, count.trans ?_, contains⟩
    change K * (4 * (D * (n+1)) + 5) ≤ K * (8 * D + 5) * n
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith [Nat.mul_le_mul_left D hn]

end Schoolbook

end NearSquareRoot
end Computability
end OAI
