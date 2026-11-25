import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepRow
import OAI.Computability.NearSquareRoot.FixedLayerDispatch

/-! # Exact permutation branch of the framed Fourier interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1800000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint Space DigitPacking FixedLayerTickets
open ShortFourier.BatchWord SynchronizedLayers SynchronizedLayers.ScheduleProgram Matrix
open scoped Matrix

/-- The literal output record at a tape address reads its source from the
generated block table, for both normal and adjoint schedule tickets. -/
def permutedRow {n : ℕ} (h : Directory n) (hd : 4 ≤ (box n).length) (r : PermDirectory.Directed)
    (v : FixedCandidate.Array n) : FixedCandidate.Array n :=
  letI := BoxFin.modulus_neZero h
  v ∘ BoxFin.permutationSource h hd (PermDirectory.localSource h r)

/-- Pulling the reordered records back to the padded residue axes gives exactly
the corresponding chronological Fourier matrix applied to the original records. -/
theorem permutedRow_exact {n : ℕ} (h : Directory n) (hd : 4 ≤ (box n).length)
    (dir : Bool) (s : Fin (directedPlan (dir,tally (addressBits n))).length)
    (tag : (directedPlan (dir,tally (addressBits n)))[s.val].2.1 = kindCode .permutation)
    (v : FixedCandidate.Array n) :
    letI := BoxFin.modulus_neZero h
    let r := (directedPlan (dir,tally (addressBits n)))[s.val]
    let M := boxRow (physicalLayout h) hd r
    recordArray (permutedRow h hd r v ∘ index h) =
      WithLp.toLp 2 (M *ᵥ (fun z => recordArray (v ∘ index h) z)) := by
  let _ := BoxFin.modulus_neZero h
  let r := (directedPlan (dir,tally (addressBits n)))[s.val]
  let out := permutedRow h hd r v
  have exactRow := PermDirectory.flat_permutationRow_apply h hd dir s tag (recordArray v)
  have zero : ‖recordArray out - recordArray out‖ ≤ (0 : ℝ) := by simp
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (transferRow (index h) (boxRow (physicalLayout h) hd r)
    v out (recordArray out) exactRow zero))

/-- Leave the unary operand length parked during a raw record permutation.
The ticket is consumed by the call; the frame is restored at return. -/
private theorem consumeTicket {I : Type} (n t : I → ℕ) (hn : ∀ i, 2 ≤ n i) (hnt : ∀ i, n i ≤ t i)
    (ticket : I → Ticket) (K : ℕ) (hh : ∀ i, size (ticket i) ≤ K*(n i+1))
    (x y : (i : I) → FixedCandidate.Array (n i))
    (raw : BoundedTask t n (fun i => send (ticket i,records (x i))) (fun i => send (records (y i)))) :
    BoundedTask t n (fun i => .fork (send (ticket i)) (framed (x i))) (fun i => framed (y i)) := by
  let pack (v : Ticket × Tally × List Dusk.Pair) := ((v.1,v.2.2),v.2.1)
  have prep := linearTree pack (by unfold pack; fun_prop)
    (fun i => (ticket i,tally (n i),records (x i))) (K+75001) hnt (fun i => by
      change (Tree.fork (send (ticket i)) (framed (x i))).count ≤ _
      have := framed_size (hn i) (x i)
      have cap := hh i
      change (send (ticket i)).count ≤ _ at cap
      simp only [Tree.count,Nat.add_mul]
      omega)
  have core := (raw.left (fun i => send (tally (n i)))).bound (time' := t) (space' := n) 1 4
    (fun _ => by simp) (fun i => by change n i + size (tally (n i))+1 ≤ _; simp [size_tally]; omega)
  let swap (v : List Dusk.Pair × Tally) := (v.2,v.1)
  have finish := linearTree swap (by unfold swap; fun_prop)
    (fun i => (records (y i),tally (n i))) 75000 hnt (fun i => by
      have cap := framed_size (hn i) (y i)
      change size (tally (n i),records (y i)) ≤ _ at cap
      simpa only [size_prod,Nat.add_comm] using cap)
  exact sequence (sequence prep core) finish

variable {I : Type} (n : I → ℕ) (h : ∀ i, Directory (n i)) (dir : I → Bool)
  (hd : ∀ i, 4 ≤ (box (n i)).length)

/-- The physical branch contract reduces to a raw ticket-plus-list call. Framing
and the exact matrix error calculation hold for all admissible input arrays. -/
theorem permutationFromTickets (clock : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (ht : ∀ i, n i ≤ clock (n i)) :
    let J := {e : RowInput n h dir // HasKind n h dir .permutation e}
    let ix (e : J) := e.val.instanceIndex
    let row (e : J) := (directedPlan (rowKey n dir (ix e)))[e.val.position.val]
    let out (e : J) := permutedRow (h (ix e)) (hd (ix e)) (row e) e.val.payload
    BoundedTask (fun e : J => clock (n (ix e))) (fun e => n (ix e))
      (fun e => send (e.val.ticket n h dir, records e.val.payload)) (fun e => send (records (out e))) →
    Implements n h dir hd clock .permutation := by
  intro J ix row out raw
  refine ⟨out,?_,?_⟩
  · apply consumeTicket _ _ (fun e => hn (ix e)) (fun e => ht (ix e)) (fun e => e.val.ticket n h dir)
      1920000000000 _ (fun e => e.val.payload) out raw
    intro e
    rw [RowInput.ticket,header_at]
    have hv := array_volume (hn (ix e))
    have hw : addressBits (n (ix e))+1 ≤ 192*n (ix e) :=
      (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans hv
    have cap := phaseStageTicket_size (addressBits (n (ix e))) (dir (ix e)) e.val.position.val e.val.position.isLt
    change size (phaseStageTicket (addressBits (n (ix e))) (dir (ix e)) e.val.position.val e.val.position.isLt) ≤ _
    omega
  · intro e
    have tag : (row e).2.1 = kindCode .permutation := by
      simpa only [HasKind, RowInput.ticket, header_at] using e.property
    have he := permutedRow_exact (h (ix e)) (hd (ix e)) (dir (ix e)) e.val.position tag e.val.payload
    let _ := BoxFin.modulus_neZero (h (ix e))
    let M := boxRow (physicalLayout (h (ix e))) (hd (ix e)) (row e)
    have exactOut : recordArray (out e ∘ index (h (ix e))) =
        WithLp.toLp 2 (M *ᵥ (fun z => recordArray (e.val.payload ∘ index (h (ix e))) z)) := he
    change ‖recordArray (out e ∘ index (h (ix e))) - WithLp.toLp 2 (M *ᵥ _)‖ ≤ _
    rw [exactOut,sub_self,norm_zero]
    positivity

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
