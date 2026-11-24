import OAI.Computability.VPVNP.SliceArithmeticMultiplyInit
import OAI.Computability.VPVNP.SliceArithmeticCallOrder
import OAI.Computability.VPVNP.EvaluatorRadixSpace

/-!
# A reusable multiplication call on packed extension-field elements

The caller supplies two low-degree-first limb streams, a prime modulus, its
advised polynomial, the unary degree and a zero word giving the register width.
The subroutine consumes the query operand, overwrites the accumulator with the
product and clears its entire local workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyCall

open RAMTape BurstRAM HornerControl
open SliceArithmeticRound (packed packed_length)
open SliceArithmeticStreamRow (state)

/-- Execute packed field multiplication by setting up the workspace, reversing the query's limb
order, running Horner rounds, and returning the product. -/
def machine : FiniteRoutine Port :=
  ((«initialize».followedBy orderInput).followedBy (HornerControl.machine.onPorts Sum.inl)).followedBy reclaim

/-- Total bit-stack time, including port setup, digit ordering and final cleanup. -/
def callCap (e w : ℕ) : ℕ :=
  (14*(5*((e+1)*(w+1))+2)+1) + (e*(15*w+7)+1+(10*w+4)) +
    (e*(digitCap e w+1)+1) + ((e*w+1)+(5*(e*w)+2)+(13*((e+1)*(w+1)+1)+1))

theorem machine_runs {p e w : ℕ} [NeZero p] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c a b : Vector p e) :
    ∃ t ≤ callCap e w, machine.Runs t
      (clean (external p e w (packed w (List.ofFn c)) (packed w (List.ofFn a)) (packed w (List.ofFn b))))
      (clean (external p e w (packed w (List.ofFn c)) [] (packed w (List.ofFn (mul c a b))))) := by
  let cb := packed w (List.ofFn c)
  let ab := packed w (List.ofFn a)
  let bb := packed w (List.ofFn b)
  let yb := packed w (List.ofFn (mul c a b))
  have hc : cb.length = e*w := by simp [cb]
  have hb : bb.length = e*w := by simp [bb]
  have hy : yb.length = e*w := by simp [yb]
  obtain ⟨n₁, h₁, start⟩ := initialize_runs (p := p) cb ab bb hc hb
  have ordered := orderInput_runs (w := w) cb bb a
  obtain ⟨n₂, h₂, registers, main⟩ := HornerControl.machine_runs he hw c a b
  let io := external p e w cb [] bb
  let s₀ := state (initialRegisters p w) (streams (packed w (List.ofFn (zero p e))) [] [] []
    (extra cb bb e (packed w (List.ofFn a).reverse) e 0))
  let s₁ := state registers (streams yb [] [] [] (extra cb bb e [] 0 0))
  have installed : (HornerControl.machine.onPorts Sum.inl).Runs n₂ (workspace s₀ io) (workspace s₁ io) := by
    apply HornerControl.machine.runs_onPorts_framed Sum.inl_injective main (fun _ => rfl) (fun _ => rfl)
    rintro (i | i) hi
    · exact (hi i rfl).elim
    · rfl
  obtain ⟨n₃, h₃, finish⟩ := reclaim_runs (p := p) registers cb bb yb hc hb hy
  exact ⟨_, by unfold callCap; omega, ((start.followedBy ordered).followedBy installed).followedBy finish⟩

/-- A simple quadratic bound in both the number of limbs and their working width. -/
theorem callCap_le (e w : ℕ) : callCap e w ≤ 2000 * (e+1)^2 * (w+1)^2 := by
  unfold callCap digitCap
  ring_nf
  omega

/-- A prefix of the actual instruction execution uses only polynomial storage
on each of the finitely many ports of the multiplier. -/
theorem prefix_stack_length {p e w : ℕ} [NeZero p] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c a b : Vector p e) {n : ℕ} {q : Option machine.State} {s : Stacks Port}
    (run : StackRuns machine.body.standalone n (some machine.body.entry)
      (clean (external p e w (packed w (List.ofFn c)) (packed w (List.ofFn a)) (packed w (List.ofFn b)))) q s)
    (k : Port) : (s k).length ≤ (e+1)*(w+1) + 2000*(e+1)^2*(w+1)^2 := by
  obtain ⟨t, ht, hdone⟩ := machine_runs he hw c a b
  have hn := EvaluatorRadixDivision.ticks_le_at_return hdone (by rfl) run
  apply (EvaluatorRadixDivision.run_length run k).trans
  apply Nat.add_le_add _ (hn.trans (ht.trans (callCap_le e w)))
  rcases k with i | i
  · exact Nat.zero_le _
  · cases i <;> simp [clean, external] <;> nlinarith

end SliceArithmetic.MultiplyCall

end VPVNP
end Computability
end OAI
