import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepTicket
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank

/-! # A candidate-dependent reserve ruler for polynomial ticket compilation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code CommonRegisters GeneratorSyntax Space FixedCandidate EffectiveBoundedTask
open DigitPacking

open private fitsOperand from OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepTicket

variable {P : Type} [Primcodable P] {I : P → Type}

private theorem supplyTally (D : P → ℕ) (eff : Computable D) (u : ∀ p, I p → Tree) :
    Family (fun _ _ => 0) (fun p i => (u p i).count) u (fun p i => .fork (send (tally (D p))) (u p i)) := by
  let command p := (Task.prepare 0 (send (tally (D p)))).join (pack 0)
  have effective : Effective ltr (fun p => Task.prepare 0 (send (tally (D p)))) :=
    PhysicalWalshCompile.effective_tally_prepare.comp eff
  refine ⟨command,1,effective.join
    (effective_const ltr (pack 0)),by decide,fun p => ⟨⟨(RegisterWitness.prepare_within _).mpr (by decide),
      by change 0 < 1; decide⟩,?_⟩⟩
  have run : ∃ C : ℕ, ∀ i env, Fits.value env (command p) 0 (u p i)
      (Tree.fork (send (tally (D p))) (u p i)) (C*(0+1)) :=
    command_contract (command p) from Task.supply (send (tally (D p))) (u p)
  simpa only [Nat.add_zero] using EffectiveBoundedTask.Runs.of_time (t := fun _ : I p => 0) run

/-- One fixed polynomial program reads a unary parameter and the runtime ticket.
Only the parameter literal depends on the candidate; the program emitting it is computable.
Every candidate has a linear-in-operand output-size, time and workspace bound. -/
theorem prepareWithTally {X Y : Type} [Codec X] [Codec Y] (f : Tally × X → Y) (poly : Poly f)
    (D : P → ℕ) (eff : Computable D) (n : ∀ p, I p → ℕ) (hn : ∀ p i, 2 ≤ n p i)
    (input : ∀ p, I p → X) (short : ∀ p, Dom (fun i => addressBits (n p i)) (fun i => size (input p i))) :
    let data p (i : I p) := (tally (D p),input p i)
    (∃ A : P → ℕ, ∀ p i, size (f (data p i)) ≤ A p*(n p i+1)) ∧
      Family n n (fun p i => send (input p i)) (fun p i => send (f (data p i))) := by
  intro data
  let k p (i : I p) := addressBits (n p i)
  have joined p : Dom (k p) (fun i => size (data p i)) := by
    simpa only [data,size_prod] using
      (((Dom.const (k p) (size (tally (D p)))).add (short p)).add (Dom.const (k p) 1))
  choose A cap using fun p => fitsOperand (n p) (hn p) ((poly.length.map (data p)).sub (joined p))
  refine ⟨⟨A,cap⟩,?_⟩
  obtain ⟨b,hb,c,C,cmd⟩ := poly
  have core : Family n n (fun p i => send (data p i)) (fun p i => send (f (data p i))) := by
    apply Family.fixed_run c
    intro p
    obtain ⟨B,time⟩ := fitsOperand (n p) (hn p) ((hb.map (data p)).sub (joined p))
    obtain ⟨L,vol⟩ := fitsOperand (n p) (hn p) (joined p)
    have rr := EffectiveBoundedTask.Runs.of_time (c := c) (t := fun i : I p => b (data p i))
      (u := fun i => send (data p i)) (v := fun i => send (f (data p i))) ⟨C,fun i => cmd (data p i)⟩
    apply rr.bound (B+1) (L+B+1)
    · intro i
      have := time i
      change b (data p i) + 1 ≤ _
      rw [Nat.add_mul]; omega
    · intro i
      have := time i
      have := vol i
      change size (data p i) + b (data p i)+1 ≤ _
      simp only [Nat.add_mul,Nat.one_mul]
      omega
  have tag := supplyTally D eff (fun p i => send (input p i))
  obtain ⟨c',R,e,hR,h⟩ := tag
  apply Family.sequence (v := fun p i => send (data p i)) _ core
  refine ⟨c',R,e,hR,fun p => ⟨(h p).1,?_⟩⟩
  obtain ⟨L,vol⟩ := fitsOperand (n p) (hn p) (short p)
  apply (h p).2.bound 1 (L+1)
  · intro i
    simp
  · intro i
    have := vol i
    change size (input p i)+1 ≤ _
    rw [Nat.add_mul]
    omega

end FixedLayer

end NearSquareRoot
end Computability
end OAI
