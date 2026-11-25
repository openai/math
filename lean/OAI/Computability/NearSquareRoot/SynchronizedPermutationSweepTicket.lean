import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEmit
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepBranch
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSeed

/-! # Building a permutation-pass directory directly from its indexed Fourier ticket -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking FixedLayerTickets
open ShortFourier.BatchWord SynchronizedPermutationBudget
open PermDirectory (Query BatchTicket batchTicket)

private theorem fitsOperand {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i) {b : I → ℕ}
    (dom : Dom (fun i => addressBits (n i)) b) : ∃ A, ∀ i, b i ≤ A*(n i+1) := by
  obtain ⟨A,cap⟩ := setup_le_array dom
  refine ⟨A*192,fun i => ?_⟩
  have volume : 2^addressBits (n i) ≤ 192*(n i+1) :=
    (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans
      ((array_volume (hn i)).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
  exact (cap i).trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left A volume)

/-- Literal tree accepted by the directory interpreter at this ticket. -/
def passDirectory {H : Type} [Codec H] (key : Query × BatchTicket → H) (dir : Bool) (k s : ℕ) : Tree :=
  Task.forest (fun a => send (key ((dir,tally k,tally s),batchTicket a)))
    (order k ((CoprimeBox.box k).length/4))

/-- Polynomial header generation executes in linear time and workspace in the
operand size, before the first scan of the coefficient list. Its output-size
bound also applies to every unconsumed directory suffix. -/
theorem preparePermutationTicket {I H : Type} [Codec H] [Inhabited H]
    (key : Query × BatchTicket → H) (hp : Poly key) (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (dir : I → Bool) (s : (i : I) → Fin (directedPlan (dir i,tally (addressBits (n i)))).length) :
    let t i := phaseStageTicket (addressBits (n i)) (dir i) (s i).val (s i).isLt
    let d i := passDirectory key (dir i) (addressBits (n i)) (s i).val
    (∃ A : ℕ, ∀ i, (d i).count ≤ A*(n i+1)) ∧ BoundedTask n n (send ∘ t) d := by
  intro t d
  let k i := addressBits (n i)
  let generate (t : Ticket) := PermDirectory.emitted key (PermDirectory.ticketQuery t)
  have pg : Poly generate := PermDirectory.ticketQuery_easy.poly.compose (PermDirectory.emitted_poly key hp)
  have render (i : I) : send (generate (t i)) = d i := by
    change send (PermDirectory.emitted key (dir i,tally (k i),tally (s i).val)) = _
    rw [PermDirectory.emitted_eq,← Task.forest_send,Task.forest_map]
    rfl
  have short : Dom k (fun i => size (t i)) :=
    ⟨1,10000000000,fun i => by simpa only [pow_one] using phaseStageTicket_size (k i) (dir i) (s i).val (s i).isLt⟩
  obtain ⟨B,large⟩ := fitsOperand n hn ((pg.length.map t).sub short)
  have cap (i : I) : (d i).count ≤ B*(n i+1) := by rw [← render]; exact large i
  obtain ⟨b,hb,run⟩ := pg.on short
  obtain ⟨C,Cb⟩ := fitsOperand n hn hb
  obtain ⟨D,Dt⟩ := fitsOperand n hn short
  refine ⟨⟨B,cap⟩,?_⟩
  have prep := (BoundedTask.of_time run).bound (time' := n) (space' := n) (C+1) (D+C+1)
    (fun i => by have := Cb i; rw [Nat.add_mul]; omega) (fun i => by
      have ht := Dt i
      have hc := Cb i
      change size (t i) + b i + 1 ≤ _
      simp only [Nat.add_mul,Nat.one_mul]
      omega)
  exact prep.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) render

/-- Precompute both relocation tables and the switch-query plan for every half-stage
and batch from the ticket's width, direction and numbered row. -/
theorem prepareFullPermutationTicket (D : ℕ) {I : Type}
    (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (dir : I → Bool) (s : (i : I) → Fin (directedPlan (dir i,tally (addressBits (n i)))).length) :
    let t i := phaseStageTicket (addressBits (n i)) (dir i) (s i).val (s i).isLt
    let d i := passDirectory (Benes.PackedBatchHeader.fullHeader D) (dir i) (addressBits (n i)) (s i).val
    (∃ A : ℕ, ∀ i, (d i).count ≤ A*(n i+1)) ∧ BoundedTask n n (send ∘ t) d :=
  preparePermutationTicket _ (Benes.PackedBatchHeader.fullHeader_poly D) n hn dir s

end FixedLayer

end NearSquareRoot
end Computability
end OAI
