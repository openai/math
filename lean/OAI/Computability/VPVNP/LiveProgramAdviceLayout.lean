import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LiveEvaluatorAdvicePrepared

/-!
# The live program's concrete advice allocations

The length, prefix and order stages use the public expressions installed in
the linked program. A single upper bound on the end of the order map puts
all their public addresses, lengths and scheduled cursors in range.
The physical header length bounds the distributed source interval, and the
prefix capacity bounds the number of packed prefix words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open BurstRAM (Word)
open LiveEvaluatorAdviceBanks (PreparedLayout)

/-- Evaluate a bank of public geometry expressions and encode each result as a word of the
geometry's width. -/
def bank {k : ℕ} (g : Geometry) (xs : Fin k → PublicExpr) : Fin k → Word g.w :=
  fun i => Fin.ofNat (2^g.w) ((xs i).eval g)

/-- The actual three operand rows meet every address, count and disjointness
hypothesis of the four-stage native advice initializer. -/
theorem preparedLayout (c : Constants) (g : Geometry) (raw : List Bool)
    (hw : 4 ≤ g.w) (hlimit : (Layout.shadow c).eval g < 2^g.w)
    (hadvice : g.w + c.prefixCapacity.eval g + c.labels.eval g * Nat.clog 2 (c.labels.eval g) ≤
      c.lengths.advice.eval g)
    (hraw : raw.length ≤ c.prefixCapacity.eval g) :
    PreparedLayout (bank g (StageOperands.lengthPack c)) (bank g (StageOperands.adviceFrames c))
      (bank g (StageOperands.orderPack c)) raw (c.labels.eval g) (Nat.clog 2 (c.labels.eval g)) := by
  let src := (HeaderLayout.advice c.lengths Layout.header).eval g
  let frame := (Layout.adviceFrames c).eval g
  let packed := (Layout.packedPrefix c).eval g
  let ord := (Layout.orderMap c).eval g
  let t := c.labels.eval g
  let o := Nat.clog 2 t
  let C := c.prefixCapacity.eval g
  let W := 2^g.w
  change g.w + C + t*o ≤ c.lengths.advice.eval g at hadvice
  change raw.length ≤ C at hraw
  have hH : src + c.lengths.advice.eval g ≤ (HeaderLayout.limit c.lengths Layout.header).eval g := by
    simp only [HeaderLayout.limit, HeaderLayout.config, HeaderLayout.exponent, HeaderLayout.exterior,
      eval_add, src]
    omega
  have hF : (HeaderLayout.limit c.lengths Layout.header).eval g ≤ frame := by
    simp only [frame, Layout.adviceFrames, Layout.transitionScratch, Layout.newState, Layout.oldState,
      Layout.counter, Layout.descriptor, eval_add]
    omega
  have hsource : src + g.w + C + t*o ≤ frame := by omega
  have hP : packed = frame+24 := rfl
  have hO : ord = packed+C := rfl
  change ord + t < W at hlimit
  have hord : o ≤ g.w := Nat.clog_le_of_le_pow (by change t ≤ W; omega)
  let q := raw.length ⌈/⌉ g.w
  have hwpos : 0 < g.w := by omega
  have hq : q ≤ raw.length := (ceilDiv_le_iff_le_mul hwpos).mpr
    (Nat.le_mul_of_pos_left _ hwpos)
  have hqmul : q*g.w ≤ raw.length+g.w := by
    change ((raw.length+g.w-1)/g.w)*g.w ≤ _
    exact (Nat.div_mul_le_self ..).trans (Nat.sub_le ..)
  have hcur : q*(g.w+1) < W := by rw [Nat.mul_add, Nat.mul_one]; omega
  have oCur : t*(o+1) < W := by rw [Nat.mul_add, Nat.mul_one]; omega
  have val (x : ℕ) (h : x < W) : (Fin.ofNat (2^g.w) x).val = x := Nat.mod_eq_of_lt h
  let lp := bank g (StageOperands.lengthPack c)
  let fp := bank g (StageOperands.adviceFrames c)
  let op := bank g (StageOperands.orderPack c)
  have f0 : (fp 0).val = src := val (src) (by omega)
  have f1 : (fp 1).val = C := val (C) (by omega)
  have f2 : (fp 2).val = g.w := val (g.w) (by omega)
  have f3 : (fp 3).val = frame := val (frame) (by omega)
  have f4 : (fp 4).val = packed := val (packed) (by omega)
  have l1 : (lp 1).val = frame+22 := val (frame+22) (by omega)
  have l2 : (lp 2).val = g.w := f2
  have l4 : (lp 4).val = 1 := val (1) (by omega)
  have o0 : (op 0).val = src+g.w+C := val (src+g.w+C) (by omega)
  have o1 : (op 1).val = ord := val (ord) (by omega)
  have o2 : (op 2).val = o := val (o) (by omega)
  have o3 : (op 3).val = t*o := val (t*o) (by omega)
  have o4 : (op 4).val = t := val (t) (by omega)
  change PreparedLayout lp fp op raw t o
  refine ⟨hw,f2,by omega,rfl,by omega,l2,l2,l4,by omega,rfl,o2,hord,o3,o4,by omega,by omega,?_,
    by omega,hcur,oCur⟩
  change (fp 4).val + q ≤ (op 1).val
  omega

end LiveProgram.Advice

end VPVNP
end Computability
end OAI
