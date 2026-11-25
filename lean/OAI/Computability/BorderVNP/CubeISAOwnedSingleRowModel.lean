import OAI.Computability.BorderVNP.CubeScatterSingletonRun
import OAI.Computability.BorderVNP.CubeISAOwnedSingleFrame

/-! # Exact source cursors and memory of a physical singleton row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM DiagonalResidueRAM

/-- A row of singleton trials fixes one ordered symbol pair and visits all remaining label digits.
Each pair that shares a coordinate has its own interval of singleton bits. -/
structure SingleRowData (n d len : ℕ) where
  /-- Coordinate at which the two symbols are fixed. -/
  axis : Fin (n+1)
  /-- Source symbol at the grouping coordinate. -/
  left : Fin d
  /-- Destination symbol at the grouping coordinate. -/
  right : Fin d
  /-- Absolute start of the global singleton reservation. -/
  bank : ℕ
  /-- Next selector address at entry. Singleton visits leave this cursor in place. -/
  selector : ℕ
  /-- Next address in the shared crossing stream at entry. -/
  crossing : ℕ
  /-- Prescribed bits at actual ordered endpoint labels. -/
  value : Label (n+1) d × Label (n+1) d → Fin len → Bool

namespace SingleRowData

variable {n d len w : ℕ} (D : SingleRowData n d len)

/-- A candidate is active precisely when the reconstructed endpoint labels share a coordinate. -/
abbrev selected (t : Fin (singlePairTrials n d)) := singleTrialValid D.axis D.left D.right t

/-- Actual endpoint labels of a candidate. -/
def pair (t : Fin (singlePairTrials n d)) : Label (n+1) d × Label (n+1) d :=
  (singleOrderedPairs D.axis D.left D.right t).val

/-- Consecutive bits at one endpoint pair, in the native ordinal order. -/
def bits (t : Fin (singlePairTrials n d)) := List.ofFn (D.value (D.pair t))

/-- Source mode of each singleton slot is determined by group equality. -/
def positions (t : Fin (singlePairTrials n d)) :=
  singlePositions (decide (D.left = D.right)) (D.bits t)

/-- Label codes returned by the physical candidate preparation. -/
def codes (t : Fin (singlePairTrials n d)) : ℕ × ℕ :=
  ((finFunctionFinEquiv (D.pair t).1).val,(finFunctionFinEquiv (D.pair t).2).val)

/-- Address of this candidate's interval in the complete ordered label-pair reservation. -/
def address (t : Fin (singlePairTrials n d)) :=
  singleBase D.bank (d^(n+1)) len (D.codes t).1 (D.codes t).2

/-- Number of shared crossing words consumed at a selected pair. -/
def crossWords := if D.left = D.right then 0 else len

/-- Crossing cursor and full memory after the first `k` trials of this ordered symbol row. -/
def before (m : Memory w) : ℕ → ℕ × Memory w
  | 0 => (D.crossing,m)
  | k+1 =>
    let prev := before m k
    if ht : k < singlePairTrials n d then
      let t := (⟨k,ht⟩ : Fin (singlePairTrials n d))
      if D.selected t then (prev.1+D.crossWords,image (D.positions t) (D.address t) prev.2)
      else prev
    else prev

/-- The step at a selected row index advances the shared stream by its width and performs
the actual local or copied stores. -/
theorem before_visit (m : Memory w) (t : Fin (singlePairTrials n d)) (h : D.selected t) :
    D.before m (t.val+1) = ((D.before m t.val).1+D.crossWords,
      image (D.positions t) (D.address t) (D.before m t.val).2) := by
  simp only [before,t.isLt,dite_true,Fin.eta,h,ite_true]

/-- A rejected candidate performs no stores and consumes no crossing word. -/
theorem before_skip (m : Memory w) (t : Fin (singlePairTrials n d)) (h : ¬D.selected t) :
    D.before m (t.val+1) = D.before m t.val := by
  simp only [before,t.isLt,dite_true,Fin.eta,h,ite_false]

/-- Initial routed input and address separation for all selected families. -/
def PreparedRow (src : Set ℕ) (m : Memory w) : Prop :=
  ∀ t, D.selected t → Prepared src (D.positions t)
    ⟨D.selector,(D.before m t.val).1,D.address t⟩ m

/-- Every prefix of the native stores preserves the routed input and the frame data in
the source region, including prefixes ending at rejected digit trials. -/
theorem before_source {src : Set ℕ} (m : Memory w) (prepared : D.PreparedRow src m) (k : ℕ) :
    ∀ j ∈ src, (D.before m k).2 j = m j := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    intro j hj
    by_cases hk : k < singlePairTrials n d
    · let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
      by_cases yes : D.selected t
      · rw [D.before_visit m t yes]
        have ready := prepared_congr _ _ _ _ ih (prepared t yes)
        exact (ready.image_source hj).trans (ih j hj)
      · rw [D.before_skip m t yes]
        exact ih j hj
    · simpa only [before,hk,dite_false] using ih j hj

/-- The two label codes, their paired key and the exclusive end of their interval fit in the
full label-square allocation. This covers zero-length singleton intervals too. -/
theorem fits {limit : ℕ} (t : Fin (singlePairTrials n d))
    (keys : d^(n+1)*d^(n+1) ≤ limit) (allocation : D.bank+d^(n+1)*d^(n+1)*len < limit) :
    (D.codes t).1 < limit ∧ (D.codes t).2 < limit ∧
      (D.codes t).1*d^(n+1)+(D.codes t).2 < limit ∧ D.address t+len < limit := by
  let A := d^(n+1)
  let a := finFunctionFinEquiv (D.pair t).1
  let b := finFunctionFinEquiv (D.pair t).2
  have pos : 0 < A := pow_pos (Nat.zero_lt_of_lt D.left.isLt) _
  have key : a.val*A+b.val < A*A := by
    have hh := (finProdFinEquiv (a,b)).isLt
    change b.val+A*a.val < A*A at hh
    simpa only [Nat.add_comm,Nat.mul_comm] using hh
  have scale : A ≤ A*A := Nat.le_mul_of_pos_right A pos
  have last : (a.val*A+b.val+1)*len ≤ A*A*len := Nat.mul_le_mul_right len key
  change a.val < limit ∧ b.val < limit ∧ a.val*A+b.val < limit ∧ D.bank+(a.val*A+b.val)*len+len < limit
  change D.bank + A*A*len < limit at allocation
  rw [Nat.add_mul,Nat.one_mul] at last
  exact ⟨a.isLt.trans_le (scale.trans keys),b.isLt.trans_le (scale.trans keys),key.trans_le keys,by omega⟩

end SingleRowData

end Cube.Scatter

end BorderVNP
end Computability
end OAI
