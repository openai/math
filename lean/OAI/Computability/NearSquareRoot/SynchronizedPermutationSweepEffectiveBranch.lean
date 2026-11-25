import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveHeader
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepBranch
import OAI.Computability.NearSquareRoot.FixedLayerEffectiveDispatch

/-! # Uniform compilation of the ticket-driven Fourier permutation branch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking FixedLayerTickets EffectiveBoundedTask
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram Matrix
open scoped Matrix

variable {P : Type} [Primcodable P] {I : P → Type}

private theorem linearFamily {X Y : Type} [Codec X] [Codec Y] (g : X → Y) (hg : Easy g)
    (v : ∀ p, I p → X) {t n : ∀ p, I p → ℕ} (K : ℕ) (hnt : ∀ p i, n p i ≤ t p i)
    (vol : ∀ p i, size (v p i) ≤ K*(n p i+1)) :
    Family t n (fun p i => send (v p i)) (fun p i => send (g (v p i))) :=
  Family.joint (linearTree g hg (fun z : Sigma I => v z.1 z.2) K
    (fun z => hnt z.1 z.2) (fun z => vol z.1 z.2))

/-- Park the unary operand length while the generated raw permutation consumes
its ticket, and restore that length to the returned array. Both framing programs
are fixed across the entire family. -/
theorem consumeTicketFamilyAt (n t space : ∀ p, I p → ℕ) (hn : ∀ p i, 2 ≤ n p i) (hnt : ∀ p i, n p i ≤ t p i)
    (room : ∀ p i, n p i ≤ space p i)
    (ticket : ∀ p, I p → Ticket) (K : ℕ) (hh : ∀ p i, size (ticket p i) ≤ K*(n p i+1))
    (x y : ∀ p (i : I p), FixedCandidate.Array (n p i))
    (raw : Family t space (fun p i => send (ticket p i,records (x p i))) (fun p i => send (records (y p i)))) :
    Family t space (fun p i => .fork (send (ticket p i)) (framed (x p i))) (fun p i => framed (y p i)) := by
  let pack (v : Ticket × Tally × List Dusk.Pair) := ((v.1,v.2.2),v.2.1)
  have prep := linearFamily pack (by unfold pack; fun_prop)
    (fun p i => (ticket p i,tally (n p i),records (x p i))) (K+75001) hnt (fun p i => by
      change (Tree.fork (send (ticket p i)) (framed (x p i))).count ≤ _
      have := framed_size (hn p i) (x p i)
      have cap := hh p i
      change (send (ticket p i)).count ≤ _ at cap
      simp only [Tree.count,Nat.add_mul]
      omega)
  obtain ⟨c,R,eff,hR,contracts⟩ := raw.left (fun p i => send (tally (n p i)))
  have core : Family t space
      (fun p i => .fork (send (ticket p i,records (x p i))) (send (tally (n p i))))
      (fun p i => .fork (send (records (y p i))) (send (tally (n p i)))) :=
    ⟨c,R,eff,hR,fun p => ⟨(contracts p).1,
      (contracts p).2.bound 1 4 (fun _ => by simp) (fun i => by
        have := room p i
        change space p i + size (tally (n p i))+1 ≤ _
        simp [size_tally]
        omega)⟩⟩
  let swap (v : List Dusk.Pair × Tally) := (v.2,v.1)
  have finish := linearFamily swap (by unfold swap; fun_prop)
    (fun p i => (records (y p i),tally (n p i))) 75000 hnt (fun p i => by
      have cap := framed_size (hn p i) (y p i)
      change size (tally (n p i),records (y p i)) ≤ _ at cap
      simpa only [size_prod,Nat.add_comm] using cap)
  have prep' := prep.mono (fun _ _ => le_rfl) room
  have finish' := finish.mono (fun _ _ => le_rfl) room
  exact (prep'.sequence core).sequence finish'

/-- The linear-space specialization for a successful candidate. -/
theorem consumeTicketFamily (n t : ∀ p, I p → ℕ) (hn : ∀ p i, 2 ≤ n p i) (hnt : ∀ p i, n p i ≤ t p i)
    (ticket : ∀ p, I p → Ticket) (K : ℕ) (hh : ∀ p i, size (ticket p i) ≤ K*(n p i+1))
    (x y : ∀ p (i : I p), FixedCandidate.Array (n p i))
    (raw : Family t n (fun p i => send (ticket p i,records (x p i))) (fun p i => send (records (y p i)))) :
    Family t n (fun p i => .fork (send (ticket p i)) (framed (x p i))) (fun p i => framed (y p i)) :=
  consumeTicketFamilyAt n t n hn hnt (fun _ _ => le_rfl) ticket K hh x y raw

set_option maxHeartbeats 1800000 in
/-- Register-bounded command families on raw ticket/record input supply the
permutation opcode of the Fourier dispatcher with its exact numerical action. -/
theorem effectivePermutationFromTicketsAt (n : ∀ p, I p → ℕ) (h : ∀ p i, Directory (n p i))
    (dir : ∀ p, I p → Bool) (hd : ∀ p i, 4 ≤ (box (n p i)).length)
    (arena clock : P → ℕ → ℕ) (hn : ∀ p i, 2 ≤ n p i) (ht : ∀ p i, n p i ≤ clock p (n p i))
    (room : ∀ p i, n p i ≤ arena p (n p i)) :
    let J p := {e : RowInput (n p) (h p) (dir p) // HasKind (n p) (h p) (dir p) .permutation e}
    let ix p (e : J p) := e.val.instanceIndex
    let row p (e : J p) := (directedPlan (rowKey (n p) (dir p) (ix p e)))[e.val.position.val]
    let out p (e : J p) := permutedRow (h p (ix p e)) (hd p (ix p e)) (row p e) e.val.payload
    Family (fun p (e : J p) => clock p (n p (ix p e))) (fun p e => arena p (n p (ix p e)))
      (fun p e => send (e.val.ticket (n p) (h p) (dir p), records e.val.payload))
      (fun p e => send (records (out p e))) →
    EffectiveImplementsAt n h dir hd arena clock .permutation := by
  intro J ix row out raw
  refine ⟨out,?_,?_⟩
  · apply consumeTicketFamilyAt _ _ _ (fun p e => hn p (ix p e)) (fun p e => ht p (ix p e))
      (fun p e => room p (ix p e))
      (fun p e => e.val.ticket (n p) (h p) (dir p)) 1920000000000 _ (fun p e => e.val.payload) out raw
    intro p e
    rw [RowInput.ticket,header_at]
    have hv := array_volume (hn p (ix p e))
    have hw : addressBits (n p (ix p e))+1 ≤ 192*n p (ix p e) :=
      (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans hv
    have cap := phaseStageTicket_size (addressBits (n p (ix p e))) (dir p (ix p e))
      e.val.position.val e.val.position.isLt
    change size (phaseStageTicket (addressBits (n p (ix p e))) (dir p (ix p e))
      e.val.position.val e.val.position.isLt) ≤ _
    omega
  · intro p e
    have tag : (row p e).2.1 = kindCode .permutation := by
      simpa only [HasKind, RowInput.ticket, header_at] using e.property
    let _ := BoxFin.modulus_neZero (h p (ix p e))
    let M := boxRow (physicalLayout (h p (ix p e))) (hd p (ix p e)) (row p e)
    have exactOut : recordArray (out p e ∘ index (h p (ix p e))) =
        WithLp.toLp 2 (M *ᵥ (fun z => recordArray (e.val.payload ∘ index (h p (ix p e))) z)) :=
      permutedRow_exact (h p (ix p e)) (hd p (ix p e)) (dir p (ix p e)) e.val.position tag e.val.payload
    change ‖recordArray (out p e ∘ index (h p (ix p e))) - WithLp.toLp 2 (M *ᵥ _)‖ ≤ _
    rw [exactOut,sub_self,norm_zero]
    positivity

set_option maxHeartbeats 1800000 in
/-- The permutation opcode in a linear workspace. -/
theorem effectivePermutationFromTickets (n : ∀ p, I p → ℕ) (h : ∀ p i, Directory (n p i))
    (dir : ∀ p, I p → Bool) (hd : ∀ p i, 4 ≤ (box (n p i)).length)
    (clock : P → ℕ → ℕ) (hn : ∀ p i, 2 ≤ n p i) (ht : ∀ p i, n p i ≤ clock p (n p i)) :
    let J p := {e : RowInput (n p) (h p) (dir p) // HasKind (n p) (h p) (dir p) .permutation e}
    let ix p (e : J p) := e.val.instanceIndex
    let row p (e : J p) := (directedPlan (rowKey (n p) (dir p) (ix p e)))[e.val.position.val]
    let out p (e : J p) := permutedRow (h p (ix p e)) (hd p (ix p e)) (row p e) e.val.payload
    Family (fun p (e : J p) => clock p (n p (ix p e))) (fun p e => n p (ix p e))
      (fun p e => send (e.val.ticket (n p) (h p) (dir p), records e.val.payload))
      (fun p e => send (records (out p e))) →
    EffectiveImplements n h dir hd clock .permutation :=
  effectivePermutationFromTicketsAt n h dir hd (fun _ m => m) clock hn ht (fun _ _ => le_rfl)

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
