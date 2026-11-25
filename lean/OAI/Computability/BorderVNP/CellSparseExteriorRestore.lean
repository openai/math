import OAI.Computability.BorderVNP.CellSparseExteriorPrivate

/-! # Private restoration at the original typed translator's input port -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Private

open CellSparse.Packet.Native CellMacro.Generator VPVNP.RAMTape ExactQuantumFactoring.BitStackProgram
open private ready emptyCounters from OAI.Computability.BorderVNP.CellSparseExteriorPrivate

private def port : Register → IO ⊕ Register
  | .input => .inl .env
  | k => .inr k

private theorem port_inj : Function.Injective port := by
  intro i j eq
  cases i <;> cases j <;> simp_all [port]

/-- The original `env` port holds the compact external suffix at entry and the
dense logical input at return. All other ports and private registers are framed. -/
def restore : Fragment IO where
  Scratch := Register
  body := (PrivateProcedure.lower (.seq scan (reverseMove .output .input))).onPorts port

/-- The physical native stack routine restores all true input bits, inserting zeros
only inside omitted gaps. All temporary stacks are empty when the ordinary typed
compiler starts reading the retained original directory. -/
theorem restore_run (width pos : ℕ) (tail : List Bool) (spans : List Span) (metadata old : List Bool) :
    ∃ t ≤ cost width tail pos spans+2*(expand width tail pos spans).length+1,
      restore.Runs t (io metadata (encode width tail pos spans) old) (io metadata (expand width tail pos spans) old) := by
  let dense := expand width tail pos spans
  obtain ⟨t,ht,scanRun⟩ := scan_run width tail spans pos []
  simp only [List.append_nil] at scanRun
  have rev := reverseMove_runs Register.output Register.input (by decide) (ready [] dense.reverse)
  change ExactQuantumFactoring.BitStackProgram.Runs _ _
    (Function.update (Function.update (ready [] dense.reverse) .output []) .input (dense.reverse.reverse++[])) (2*dense.reverse.length+1) at rev
  have state : Function.update (Function.update (ready [] dense.reverse) .output []) .input dense = ready dense [] := by
    funext i; cases i <;> rfl
  rw [List.reverse_reverse,List.append_nil,List.length_reverse,state] at rev
  have h := PrivateProcedure.lower_runs (ExactQuantumFactoring.BitStackProgram.Runs.seq scanRun rev)
  refine ⟨(2*dense.length+1)+t,by dsimp only [dense]; omega,?_⟩
  apply (PrivateProcedure.lower _).runs_onPorts_framed port_inj h
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · rintro (i|i) hi
    · cases i with
      | row | out => rfl
      | env => exact (hi .input rfl).elim
    · rfl

/-- The private clock is polynomial in the expanded local size. Positive-width
fragments ensure even a list of many tiny pieces fits the same local bound. -/
theorem restore_cost_le (width pos : ℕ) (tail : List Bool) (spans : List Span)
    (ordered : Ordered width pos spans) (positive : ∀ s ∈ spans, 0<s.bits.length) :
    cost width tail pos spans+2*(expand width tail pos spans).length+1 ≤ 100*(width+tail.length+1)^3 := by
  have calcCost {p : ℕ} (ss : List Span) (h : Ordered width p ss) (posBits : ∀ s ∈ ss, 0<s.bits.length) :
      cost width tail p ss ≤ 45*(width+1)^2*(width-p+1)+2*tail.length+3 := by
    induction ss generalizing p with
    | nil =>
      have le := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.sub_le width p) 1) 2
      have hi : 45*(width+1)^2 ≤ 45*(width+1)^2*(width-p+1) := Nat.le_mul_of_pos_right _ (by omega)
      dsimp [cost]; omega
    | cons s ss ih =>
      have start := h.1
      have stop := expand_length [] ss h.2
      simp only [List.length_nil,Nat.add_zero] at stop
      have used : s.stop ≤ width := by omega
      have t := ih h.2 (fun a ha => posBits a (List.mem_cons_of_mem _ ha))
      have length : s.bits.length ≤ width := by unfold Span.stop at used; omega
      have next : p < s.stop := by
        have := posBits s List.mem_cons_self
        unfold Span.stop; omega
      have step : width-s.stop+1+1 ≤ width-p+1 := by omega
      have slot := Nat.mul_le_mul_left (45*(width+1)^2) step
      rw [Nat.mul_succ] at slot
      have startWidth : s.start ≤ width := (Nat.le_add_right s.start s.bits.length).trans used
      have gap := Nat.pow_le_pow_left (Nat.add_le_add_right ((Nat.sub_le s.start p).trans startWidth) 1) 2
      have widthSq : width+1 ≤ (width+1)^2 := Nat.le_self_pow (by decide) _
      dsimp only [cost]
      omega
  have bound := calcCost spans ordered positive
  have len := expand_length tail spans ordered
  have cub := Nat.mul_le_mul_left (45*(width+1)^2) (Nat.add_le_add_right (Nat.sub_le width pos) 1)
  have mono := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_add_right width tail.length) 1) 3
  have size : width+tail.length+1 ≤ (width+tail.length+1)^3 := Nat.le_self_pow (by decide) _
  rw [show 45*(width+1)^2*(width+1)=45*(width+1)^3 from by ring] at cub
  omega

end RoutingISA.SparseExterior.Private

end BorderVNP
end Computability
end OAI
