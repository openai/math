import OAI.Computability.NearSquareRoot.CRTControlledSizes
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetShape

/-! # Space and stage count for the global block-permutation slots

There are no external controls in a synchronized Fourier permutation slot.
Each batch budgets the actual other bits of its blocks, two guard chunks with
one leading spacer each, and disjoint high and low reserves for row headers
and packed payloads. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open Filter Controlled

/-- Seven physical axes of width at most twenty ceiling logarithms fit in this many
bits. The same integer also dominates the required guard width. -/
def width (k : ℕ) := 140 * (1 + Nat.clog 2 (k+1))

def capacity (k : ℕ) := blocksPerBatch k 1 (width k)

def batches (d k : ℕ) := batchCount d k 1 (width k)

def passes (d k : ℕ) := stageSchedule (batches d k) (2*width k)

/-- The blocks assigned to a single division-based batch. -/
def members {d : ℕ} (k a : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i => i.val / capacity k = a

def controlBits {d : ℕ} (w : Fin d → ℕ) (k a : ℕ) : ℕ :=
  ∑ i ∈ members k a, (w i-1)

theorem guard_le_width (k : ℕ) : guardWidth k ≤ width k := by
  unfold guardWidth width
  omega

theorem members_card {d k : ℕ} (ha : 0 < capacity k) (a : ℕ) :
    (members (d := d) k a).card ≤ capacity k := by
  let address := batchAddress (d := d) (j := 1) (g := width k) ha
  have inject : Set.InjOn (fun i : Fin d => (address i).2) ↑(members (d := d) k a) := by
    intro i hi j hj h
    have left (v : Fin d) (hv : v ∈ members k a) : (address v).1.val = a := (Finset.mem_filter.mp hv).2
    apply address.injective
    exact Prod.ext (Fin.ext ((left i hi).trans (left j hj).symm)) h
  simpa only [capacity,Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_card_of_injOn (fun i : Fin d => (address i).2)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _) inject

theorem controlBits_le {d k : ℕ} (w : Fin d → ℕ) (bound : ∀ i, w i ≤ width k) (a : ℕ) :
    controlBits w k a ≤ (members (d := d) k a).card * width k := by
  calc
    _ ≤ ∑ _i ∈ members (d := d) k a, width k :=
      Finset.sum_le_sum fun i _ => (Nat.sub_le ..).trans (bound i)
    _ = _ := by simp

/-- A fixed pair of reserve degrees is chosen after obtaining the physical
subroutine's polynomial bounds. The resulting capacity grows with `k`. -/
theorem eventually_room (low high : ℕ) :
    ∀ᶠ k : ℕ in atTop, 8*width k ≤ k ∧ payloadBits low k + payloadBits high k ≤ k/4 := by
  filter_upwards [eventually_batch_reserves 1 low high, eventually_clog_fits (16*140),
    eventually_ge_atTop (1:ℕ)] with k h g hk
  have one : 1 ≤ Nat.clog 2 (k+1) := by
    by_contra! he
    have u := Nat.le_pow_clog (b := 2) (by decide) (k+1)
    rw [show Nat.clog 2 (k+1)=0 by omega, Nat.pow_zero] at u
    omega
  exact ⟨by unfold width; omega, h.2.trans (by omega)⟩

theorem capacity_pos {k : ℕ} (room : 8*width k ≤ k) : 0 < capacity k := by
  apply Nat.div_pos _ (by unfold width; positivity)
  simpa only [Nat.mul_one] using room

theorem batch_index_lt {d k : ℕ} (hc : 0 < capacity k) (i : Fin d) :
    i.val / capacity k < batches d k :=
  ((batchAddress (d := d) (j := 1) (g := width k) hc i).1).isLt

/-- This bound applies to the full uncompressed address, including the padding
in an uneven final batch. Each active block contributes its non-target bits. -/
theorem batch_fits {d k low high : ℕ} (w : Fin d → ℕ) (hw : ∀ i, w i ≤ width k)
    (room : 8*width k ≤ k) (res : low+high ≤ k/4) (a : ℕ) :
    let b := (members (d := d) k a).card
    high + controlBits w k a + (b+1)*guardWidth k + (b+1)*guardWidth k + low ≤ k := by
  let b := (members (d := d) k a).card
  have n := members_card (d := d) (capacity_pos room) a
  have h := batch_space_with_heads (j := 1) (g := width k) (e := 0) (r := low+high)
    (b := b) (by decide) (by simp) n (by simpa using room) (by simpa using res)
  have controls := controlBits_le w hw a
  have chunks := Nat.mul_le_mul_left (b+1) (guard_le_width k)
  dsimp only
  change high + controlBits w k a + (b+1)*guardWidth k + (b+1)*guardWidth k + low ≤ k
  change controlBits w k a ≤ b * width k at controls
  omega

theorem pass_count {k d : ℕ} (hd : d ≤ k) (room : 8*width k ≤ k) :
    (passes d k).length ≤ (32*140^2)*(1+Nat.clog 2 (k+1))^2 := by
  have count := batch_count_le (j := 1) (g := width k) (by decide) (by unfold width; positivity) hd
    (by simpa using room)
  rw [passes,stageSchedule_length]
  calc
    _ ≤ (2*width k)*(16*1*width k) := Nat.mul_le_mul_left _ count
    _ = _ := by unfold width; ring

/-- The scheduled microstages realize all block permutations, including their
unequal-width identity padding. The box's full local address is the input type. -/
theorem routes {d k : ℕ} (w : Fin d → ℕ) (hw : ∀ i, w i ≤ width k)
    (room : 8*width k ≤ k) (perm : (i : Fin d) → Equiv.Perm (Benes.Word (w i)))
    (data : (i : Fin d) → Benes.Word (w i)) :
    (passes d k).foldl
      (restrictedStage (fun i : Fin d => i.val / capacity k) w (fun i (_ : Unit) => perm i) ()) data =
      fun i => perm i (data i) :=
  stageSchedule_routes _ _ _ _ data _ _ (fun i => batch_index_lt (capacity_pos room) i)
    (fun i => (Nat.sub_le ..).trans (Nat.mul_le_mul_left 2 (hw i)))

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
