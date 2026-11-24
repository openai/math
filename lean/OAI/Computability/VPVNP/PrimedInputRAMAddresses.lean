import OAI.Computability.VPVNP.PrimedInputRAMTranscript
import OAI.Computability.VPVNP.RAMSortCostLayout

/-!
# Computing the scratch read from a raw incident bit position

The pair counter in Section 11 enumerates input bits by position. A local
offset in the sorting region determines an exchange number and a direction.
At most `d` triangular-prefix comparisons recover the site's XOR mask.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open RAMLayout RAMSort

private def triangular (k : ℕ) : IndexExpr :=
  .div (.mul (.arg k) (.add (.arg k) (.arg 1))) (.arg 2)

private theorem triangular_eq (k : ℕ) : (triangular k).eval = layerCount k := by
  simp only [triangular, IndexExpr.eval, layerCount, Nat.choose_two_right]
  rw [Nat.add_sub_cancel, Nat.mul_comm k]

/-- Look for the phase containing the given exchange ordinal. Each iteration
evaluates a triangular prefix and compares it with the ordinal. In the
identified phase two subtractions give the XOR bit. -/
def layerBitLoop : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | k + 1, i =>
    let prefixSize := triangular k
    if i < prefixSize.eval then
      let r := layerBitLoop k i
      (r.1, r.2 + prefixSize.work + 1)
    else (k - (i - prefixSize.eval), prefixSize.work + 3)

theorem layerBitLoop_spec {d : ℕ} (i : Fin (layerCount d)) :
    (layerBitLoop d i.val).1 = (layerAt d i).siteBit := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    by_cases h : i.val < layerCount d
    · simpa [layerBitLoop, triangular_eq, layerAt, h, Layer.siteBit] using ih ⟨i.val, h⟩
    · simp [layerBitLoop, triangular_eq, layerAt, h, Layer.siteBit]

theorem layerBitLoop_ordinal {d : ℕ} (l : Layer d) :
    (layerBitLoop d l.ordinal.val).1 = l.siteBit := by
  rw [layerBitLoop_spec]
  exact congrArg Layer.siteBit ((layerEquiv d).left_inv l)

theorem layerBitLoop_work (d i : ℕ) : (layerBitLoop d i).2 ≤ 6 * d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [layerBitLoop]
    split <;> simp only [triangular, IndexExpr.work] <;> omega

private def sortWidth (H w : ℕ) : IndexExpr :=
  .mul (.mul (.mul (.arg 4) (.arg H)) (.arg 5)) (.arg w)

private def chunkIndex (H w k : ℕ) : IndexExpr :=
  .div (.sub (.arg k) (.mul (.arg 16) (.arg w))) (sortWidth H w)

/-- Compute a source row and offset from the public site and local position.
The work counter charges arithmetic and comparisons. The final read, when
there is one, is a separate single external probe. -/
def rawSource (d H w v k : ℕ) : Option (ℕ × ℕ) × ℕ :=
  let first := IndexExpr.mul (.arg 8) (.arg w)
  let base := IndexExpr.mul (.arg 16) (.arg w)
  let sites := IndexExpr.shl (.arg 1) (.arg d)
  if k < first.eval then
    (if v + 1 < sites.eval then some (v, k) else none, first.work + sites.work + 3)
  else if k < base.eval then
    (if 0 < v then some (v - 1, k - first.eval) else none, first.work + base.work + 5)
  else
    let q := chunkIndex H w k
    let side := IndexExpr.mod q (.arg 2)
    let comparisons := first.work + base.work + side.work + 3
    if side.eval = 0 then (some (v, k), comparisons)
    else
      let ordinal := IndexExpr.div q (.arg 2)
      let bit := layerBitLoop d ordinal.eval
      let sender := IndexExpr.xor (.arg v) (.shl (.arg 1) (.arg bit.1))
      let sendOffset := IndexExpr.sub (.arg k) (sortWidth H w)
      (some (sender.eval, sendOffset.eval), comparisons + ordinal.work + bit.2 + sender.work + sendOffset.work)

private theorem sortWidth_eval (H w : ℕ) : (sortWidth H w).eval = blockBits H w := rfl

private theorem chunkIndex_offset {d H w : ℕ} (l : Layer d) (dir : Fin 2) (j : Fin (blockBits H w)) :
    (chunkIndex H w (offset d H w (.inr (l, dir, j))).val).eval = 2 * l.ordinal.val + dir.val := by
  have hp : 0 < blockBits H w := Nat.zero_lt_of_lt j.isLt
  rw [offset_sort]
  simp only [chunkIndex, IndexExpr.eval, sortWidth_eval]
  have h : 16 * w + l.ordinal.val * (2 * blockBits H w) + dir.val * blockBits H w + j.val - 16 * w =
      blockBits H w * (2 * l.ordinal.val + dir.val) + j.val := by
    rw [show 16 * w + l.ordinal.val * (2 * blockBits H w) + dir.val * blockBits H w + j.val =
      16 * w + (blockBits H w * (2 * l.ordinal.val + dir.val) + j.val) by ring, Nat.add_sub_cancel_left]
  rw [h, Nat.mul_add_div hp, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

/-- At every actual incident port the linear-address algorithm gives the
same source as the typed endpoint calculation, including both end clamps. -/
theorem rawSource_offset {d H w : ℕ} (v : Fin (2 ^ d)) (p : Slot d H w) :
    (rawSource d H w v.val (offset d H w p).val).1 =
      (sourcePort (v, p)).map (fun y ↦ (y.1.val, (offset d H w y.2).val)) := by
  rcases p with ⟨dir, j⟩ | ⟨l, dir, j⟩
  · fin_cases dir
    · have hj := j.isLt
      by_cases hv : v.val + 1 < 2 ^ d <;>
        simp [rawSource, offset_successor, IndexExpr.eval, Nat.shiftLeft_eq, sourcePort, hj, hv]
    · have hj := j.isLt
      have h₁ : ¬ 8 * w + j.val < 8 * w := by omega
      have h₂ : 8 * w + j.val < 16 * w := by omega
      by_cases hv : 0 < v.val <;>
        simp [rawSource, offset_successor, IndexExpr.eval, h₁, h₂, sourcePort, hv]
  · let k := (offset d H w (.inr (l, dir, j))).val
    have hk := offset_sort l dir j (d := d)
    change k = _ at hk
    have h₁ : ¬ k < 8 * w := by omega
    have h₂ : ¬ k < 16 * w := by omega
    have hq : (chunkIndex H w k).eval = 2 * l.ordinal.val + dir.val := chunkIndex_offset l dir j
    change (rawSource d H w v.val k).1 = _
    by_cases hd : dir = 0
    · subst dir
      change (chunkIndex H w k).eval = 2 * l.ordinal.val + 0 at hq
      simp [rawSource, IndexExpr.eval, h₁, h₂, hq, sourcePort]
      rfl
    · have hdir : dir = 1 := by
        apply Fin.ext
        have hn : dir.val ≠ 0 := fun h ↦ hd (Fin.ext h)
        have := dir.isLt
        change dir.val = 1
        omega
      subst dir
      change (chunkIndex H w k).eval = 2 * l.ordinal.val + 1 at hq
      have hdiv : (2 * l.ordinal.val + 1) / 2 = l.ordinal.val := by omega
      have hmod : (2 * l.ordinal.val + 1) % 2 = 1 := by omega
      have hsend : k - blockBits H w = (offset d H w (.inr (l, 0, j))).val := by
        rw [offset_sort]
        simp at hk ⊢
        omega
      simp [rawSource, IndexExpr.eval, h₁, h₂, hq, hmod, hdiv, layerBitLoop_ordinal,
        Nat.shiftLeft_eq, sortWidth_eval, sourcePort, hsend, Layer.partner, partner]

/-- Correctness for an enumerated linear input position, without an input
slot supplied by the caller. -/
theorem rawSource_at {d H w : ℕ} (v : Fin (2 ^ d)) (k : Fin (width d H w)) :
    (rawSource d H w v.val k.val).1 =
      (sourcePort (v, (offset d H w).symm k)).map (fun y ↦ (y.1.val, (offset d H w y.2).val)) := by
  simpa only [Equiv.apply_symm_apply] using rawSource_offset v ((offset d H w).symm k)

/-- The enumerator makes a binary choice precisely when this source lookup
returns the input position itself. -/
theorem rawSource_eq_self_iff {d H w : ℕ} (v : Fin (2 ^ d)) (k : Fin (width d H w)) :
    (rawSource d H w v.val k.val).1 = some (v.val, k.val) ↔
      designated (v, (offset d H w).symm k) = true := by
  let x : Endpoint d H w := (v, (offset d H w).symm k)
  rw [rawSource_at, ← sourcePort_eq_self_iff]
  change (sourcePort x).map _ = some _ ↔ sourcePort x = some x
  cases hs : sourcePort x with
  | none => simp
  | some y =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro he
      apply Prod.ext
      · exact Fin.ext (congrArg Prod.fst he)
      · apply (offset d H w).injective
        change offset d H w y.2 = offset d H w ((offset d H w).symm k)
        rw [Equiv.apply_symm_apply]
        exact Fin.ext (congrArg Prod.snd he)
    · rintro rfl
      simp [x]

/-- A raw offset lookup uses at most a linear number of word operations in
the site-address width, irrespective of any scratch or message value. -/
theorem rawSource_work (d H w v k : ℕ) : (rawSource d H w v k).2 ≤ 6 * d + 32 := by
  have hb := layerBitLoop_work d ((chunkIndex H w k).eval / 2)
  by_cases h₁ : k < 8 * w
  · simp only [rawSource, IndexExpr.eval, h₁, ite_true, IndexExpr.work]
    omega
  by_cases h₂ : k < 16 * w
  · simp only [rawSource, IndexExpr.eval, h₁, ite_false, h₂, ite_true, IndexExpr.work]
    omega
  by_cases h₃ : (chunkIndex H w k).eval % 2 = 0
  · simp only [rawSource, IndexExpr.eval, h₁, h₂, ite_false, h₃, ite_true]
    change 12 ≤ _
    omega
  · simp only [rawSource, IndexExpr.eval, h₁, h₂, h₃, ite_false]
    change 12 + 7 + (layerBitLoop d ((chunkIndex H w k).eval / 2)).2 + 2 + 4 ≤ _
    omega

end PrimedInputRAM

end VPVNP
end Computability
end OAI
