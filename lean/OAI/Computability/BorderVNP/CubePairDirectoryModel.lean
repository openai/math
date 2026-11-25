import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Numeric fields of the ordered label-pair directory

The cube rank uses digits in radix `d²` and the orientation uses the first
coordinate. The remaining comparison bits form the vertex ordinal. All label
digits are read least significant first.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PairDirectory

open Finset RoutingISA

/-- Symbol at coordinate `i` of the packed product label. -/
def digit (d x i : ℕ) := x / d^i % d

/-- Rank of the increasing pair of symbols at one coordinate. -/
def pairDigit (d u v i : ℕ) := min (digit d u i) (digit d v i)*d + max (digit d u i) (digit d v i)

/-- One bit recording whether the source symbol is the larger symbol. -/
def flip (d u v i : ℕ) := (decide (digit d v i < digit d u i)).toNat

/-- Rank of the prefix of the sorted symbol pairs. -/
def cubeRank (d u v k : ℕ) := ∑ i ∈ range k, pairDigit d u v i * (d*d)^i

/-- Binary ordinal of the vertex on coordinates beyond the first. -/
def vertexNo (d u v k : ℕ) := ∑ i ∈ range k, if i=0 then 0 else flip d u v i*2^(i-1)

/-- Orientation of the nonempty prefix. -/
def orientation (d u v k : ℕ) := if k=0 then 0 else flip d u v 0

/-- The prefix is a packet precisely if its two labels differ at every scanned symbol. -/
def kind (d u v : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => if digit d u i = digit d v i then 0 else kind d u v i

/-- The numeric kind discriminates full pairs from retained singletons. -/
theorem kind_one_iff (d u v k : ℕ) : kind d u v k = 1 ↔ ∀ i < k, digit d u i ≠ digit d v i := by
  induction k with
  | zero => simp [kind]
  | succ k ih => rw [kind, Nat.forall_lt_succ_right, ← ih]; split <;> simp_all

/-- Bank ordinal of block zero of this oriented packet. -/
def firstPacketIndex (d u v k blocks : ℕ) := (cubeRank d u v k*2 + orientation d u v k)*blocks

/-- The pair rank is a genuine radix-`d²` digit. -/
theorem pairDigit_lt (d u v i : ℕ) (hd : 0 < d) : pairDigit d u v i < d*d := by
  have hu : digit d u i < d := Nat.mod_lt _ hd
  have hv : digit d v i < d := Nat.mod_lt _ hd
  have hlo : min (digit d u i) (digit d v i) + 1 ≤ d := (min_le_left ..).trans_lt hu
  have hhi : max (digit d u i) (digit d v i) < d := max_lt hu hv
  have h := Nat.mul_le_mul_right d hlo
  rw [Nat.succ_mul] at h
  unfold pairDigit
  omega

/-- The accumulated prefix fits the corresponding radix power. -/
theorem cubeRank_lt (d u v k : ℕ) (hd : 0 < d) : cubeRank d u v k < (d*d)^k := by
  induction k with
  | zero => simp [cubeRank]
  | succ k ih =>
    have h := Nat.mul_le_mul_left ((d*d)^k) (Nat.succ_le_of_lt (pairDigit_lt d u v k hd))
    rw [Nat.mul_succ] at h
    simp only [cubeRank, Finset.sum_range_succ, pow_succ]
    change cubeRank d u v k + _ < _
    rw [Nat.mul_comm (pairDigit d u v k)]
    omega

/-- The accumulated vertex ordinal fits in the binary digit bound. -/
theorem vertexNo_lt (d u v k : ℕ) : vertexNo d u v k < 2^k := by
  induction k with
  | zero => simp [vertexNo]
  | succ k ih =>
    have hb : flip d u v k ≤ 1 := Bool.toNat_le _
    have hp : 2^(k-1) ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    have hm := Nat.mul_le_mul_right (2^(k-1)) hb
    simp only [Nat.one_mul] at hm
    simp only [vertexNo, Finset.sum_range_succ, pow_succ]
    change vertexNo d u v k + _ < _
    split <;> omega

/-- Layout loaded from the common frame and declaration header. -/
structure Layout where
  /-- Native frame base. -/
  frame : ℕ
  /-- Declaration-header address from frame word 63. -/
  header : ℕ
  /-- Symbol count per coordinate. -/
  d : ℕ
  /-- Number of product coordinates. -/
  axes : ℕ
  /-- Blocks in each ordered pair. -/
  blocks : ℕ
  /-- First word of the three-field directory. -/
  table : ℕ

/-- Number of product labels. -/
def Layout.Z (l : Layout) := l.d^l.axes

/-- Number of ordered label pairs. -/
def Layout.count (l : Layout) := l.Z*l.Z

/-- Register ABI for the outer pair loop. Register 9 is its counter. -/
def Layout.param (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => l.d | 4 => l.axes | 5 => l.Z
  | 6 => l.blocks | 7 => l.table | 8 => l.count | 10 => l.d*l.d | _ => 0

/-- Registers fixed throughout both counted loops. -/
def Layout.Ready (l : Layout) (z : NatState) := ∀ j : Reg, j.val ≤ 10 → j.val ≠ 9 → z.reg j = l.param j.val

/-- Runtime capacities for the actual addresses and ordinary numeric intermediates. -/
structure Layout.Fits (l : Layout) (w : ℕ) : Prop where
  positive : 0 < l.d
  axes : l.axes < 2^w
  radix : l.d*l.d < 2^w
  vertices : 2^l.axes < 2^w
  /-- Includes the unscaled oriented ordinal even if the number of blocks is zero. -/
  packets : 2*l.count*(l.blocks+1) < 2^w
  directory : l.table + 3*l.count < 2^w
  frame : l.frame+91 < 2^w
  header : l.header+7 < 2^w

/-- The radix-square width and the ordered-pair table have identical capacity. -/
theorem Layout.radixPower (l : Layout) : (l.d*l.d)^l.axes = l.count := by rw [mul_pow]; rfl

/-- Directory field at an absolute linear index. -/
def Layout.entry (l : Layout) (q f : ℕ) : ℕ :=
  let u := q/l.Z
  let v := q%l.Z
  match f with
  | 0 => kind l.d u v l.axes
  | 1 => firstPacketIndex l.d u v l.axes l.blocks
  | _ => vertexNo l.d u v l.axes

/-- Prefix image of the actual directory in shared word memory. -/
structure Image (l : Layout) (orig : ℕ → ℕ) (q : ℕ) (mem : ℕ → ℕ) : Prop where
  fields : ∀ i < q, ∀ f < 3, mem (l.table+3*i+f) = l.entry i f
  outside : ∀ a, (a < l.table ∨ l.table+3*q ≤ a) → mem a = orig a

end Cube.PairDirectory

end BorderVNP
end Computability
end OAI
