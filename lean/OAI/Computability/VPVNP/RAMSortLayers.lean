import OAI.Computability.VPVNP.RAMSortNetwork
import OAI.Computability.VPVNP.RAMSortRouting

/-!
# Addressed layers of the bitonic sorting network

Lemma 10.1 uses one XOR mask at every site of a layer. The layer definitions
below act on records indexed by natural numbers. Their restrictions to aligned
finite blocks agree with the recursive bitonic network. In particular the
result at each index of a finite array is independent of all records outside it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {α : Type*}

/-- Read an aligned block of `2^k` records from the global array. -/
def block (k site : ℕ) (x : ℕ → α) : Wires k α := fun i ↦ x (site * 2 ^ k + i)

private theorem leftBase (k site : ℕ) : (2 * site) * 2 ^ k = site * 2 ^ (k + 1) := by
  rw [Nat.pow_succ]
  ac_rfl

private theorem rightBase (k site : ℕ) :
    (2 * site + 1) * 2 ^ k = site * 2 ^ (k + 1) + 2 ^ k := by
  rw [Nat.add_mul, Nat.one_mul, leftBase]

@[simp] theorem lo_block (k site : ℕ) (x : ℕ → α) :
    lo (block (k + 1) site x) = block k (2 * site) x := by
  funext i
  simp [lo, block, leftBase]

@[simp] theorem hi_block (k site : ℕ) (x : ℕ → α) :
    hi (block (k + 1) site x) = block k (2 * site + 1) x := by
  funext i
  simp only [hi, block, rightBase]
  congr 1
  omega

variable [LinearOrder α]

/-- A layer with stride `2^j`. The direction function is shared by the
positions of each block being merged. -/
def comparatorLayer (j : ℕ) (direction : ℕ → Bool) (x : ℕ → α) (i : ℕ) : α :=
  let p := partner j i
  if i < p then lower (direction i) (x i) (x p) else upper (direction i) (x p) (x i)

/-- Strides in a phase are applied from `2^(k-1)` down to one. -/
def runStrides : ℕ → (ℕ → Bool) → (ℕ → α) → (ℕ → α)
  | 0, _, x => x
  | k + 1, direction, x => runStrides k direction (comparatorLayer k direction x)

private theorem stride_left (k site : ℕ) (direction : ℕ → Bool) (x : ℕ → α)
    (up : Bool) (hd : ∀ i < 2 ^ (k + 1), direction (site * 2 ^ (k + 1) + i) = up) :
    block k (2 * site) (comparatorLayer k direction x) =
      fun i ↦ lower up (lo (block (k + 1) site x) i) (hi (block (k + 1) site x) i) := by
  funext i
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
  have hpos : i.val < 2 ^ (k + 1) := by rw [hpow]; omega
  simp only [block, lo, hi, leftBase, comparatorLayer]
  rw [partner_local site hpos (Nat.lt_succ_self k), partner_lo i.isLt, hd i hpos]
  rw [ite_eq_left (by have := Nat.two_pow_pos k; omega)]

private theorem stride_right (k site : ℕ) (direction : ℕ → Bool) (x : ℕ → α)
    (up : Bool) (hd : ∀ i < 2 ^ (k + 1), direction (site * 2 ^ (k + 1) + i) = up) :
    block k (2 * site + 1) (comparatorLayer k direction x) =
      fun i ↦ upper up (lo (block (k + 1) site x) i) (hi (block (k + 1) site x) i) := by
  funext i
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
  have hpos : i.val + 2 ^ k < 2 ^ (k + 1) := by rw [hpow]; omega
  simp only [block, lo, hi, rightBase, comparatorLayer]
  rw [show site * 2 ^ (k + 1) + 2 ^ k + i.val = site * 2 ^ (k + 1) + (i.val + 2 ^ k) by omega,
    partner_local site hpos (Nat.lt_succ_self k), partner_hi i.isLt, hd _ hpos,
    ite_eq_right (by omega)]

/-- A phase of addressed layers acts on every aligned block exactly as
`merge`, when that block has the indicated common direction. -/
theorem block_runStrides (k site : ℕ) (direction : ℕ → Bool) (x : ℕ → α) (up : Bool)
    (hd : ∀ i < 2 ^ k, direction (site * 2 ^ k + i) = up) :
    block k site (runStrides k direction x) = merge k up (block k site x) := by
  induction k generalizing site x with
  | zero => rfl
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
    apply eq_of_halves
    · simp only [runStrides, lo_block, merge, lo_join]
      rw [ih, stride_left k site direction x up hd]
      · simp only [lo_block]
      intro i hi
      rw [leftBase]
      apply hd
      omega
    · simp only [runStrides, hi_block, merge, hi_join]
      rw [ih, stride_right k site direction x up hd]
      · simp only [hi_block]
      intro i hi
      rw [rightBase, Nat.add_assoc]
      apply hd
      omega

/-- Even-numbered blocks in phase `a` are ascending. -/
def phaseDirection (a i : ℕ) : Bool := decide ((i / 2 ^ a) % 2 = 0)

@[simp] theorem phaseDirection_block (a site : ℕ) {i : ℕ} (hi : i < 2 ^ a) :
    phaseDirection a (site * 2 ^ a + i) = decide (site % 2 = 0) := by
  simp [phaseDirection, Nat.mul_comm site, Nat.mul_add_div (Nat.two_pow_pos a), Nat.div_eq_of_lt hi]

/-- Execute phases one through `a`, choosing the comparator directions
from the global block numbers. -/
def runPhases : ℕ → (ℕ → α) → (ℕ → α)
  | 0, x => x
  | a + 1, x => runStrides (a + 1) (phaseDirection (a + 1)) (runPhases a x)

/-- Every phase produces a recursively sorted block, ascending for even
block numbers and descending for odd ones. -/
theorem block_runPhases (a site : ℕ) (x : ℕ → α) :
    block a site (runPhases a x) = sort a (decide (site % 2 = 0)) (block a site x) := by
  induction a generalizing site with
  | zero => rfl
  | succ a ih =>
    rw [runPhases, block_runStrides _ _ _ _ _ (fun _ h ↦ phaseDirection_block _ _ h), sort]
    congr 1
    apply eq_of_halves <;> simp [ih]

/-- Run the network on a specified array width, with the requested direction
for its final merge. Earlier phases use their ordinary alternating directions. -/
def runSort : ℕ → Bool → (ℕ → α) → (ℕ → α)
  | 0, _, x => x
  | a + 1, up, x => runStrides (a + 1) (fun _ ↦ up) (runPhases a x)

/-- Restricting the globally addressed execution to the first finite block
recovers Batcher's network in either requested direction. -/
theorem block_runSort (a : ℕ) (up : Bool) (x : ℕ → α) :
    block a 0 (runSort a up x) = sort a up (block a 0 x) := by
  cases a with
  | zero => rfl
  | succ a =>
    rw [runSort, block_runStrides _ _ _ _ _ (fun _ _ ↦ rfl), sort]
    congr 1
    apply eq_of_halves <;> simp [block_runPhases]

end RAMSort

end VPVNP
end Computability
end OAI
