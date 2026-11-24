import OAI.Computability.VPVNP.PrimedInputRAMOpcodeFields
import OAI.Computability.VPVNP.PrimedInputRAMPortCode
import Mathlib.Tactic.Ring

/-!
# Converting a transcript sender into the physical scratch address

The routing block returns either an absent port or a sender's site and offset.
The final arithmetic block computes its row-major scratch address. It marks
a bit as owned exactly when the current site and offset both match the sender.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Registers carried through the routing block, below its workspace. -/
structure PortResultRegisters (rs : Regs w 48) (base n r P g v k : ℕ) : Prop where
  zero : (rs 0).val = 0
  one : (rs 1).val = 1
  three : (rs 3).val = 3
  rowWidth : (rs 6).val = n
  sites : (rs 7).val = 2^r
  siteBits : (rs 8).val = r
  baseAddr : (rs 11).val = base
  prefixWidth : (rs 12).val = P
  group : (rs 22).val = g
  site : (rs 23).val = v
  offset : (rs 25).val = k

private theorem regCast {x : Word w} {v : ℕ} (h : x.val = v) : x = (v : Word w) := by
  rw [← h, Fin.cast_val_eq_self]

/-- No copy source yields a clamped zero. A live copy source uses at most 14
private instructions, including the two comparisons for its owner flag. -/
theorem once_portResult (pub : Pub → Word w) (state : Word w) (bit : Bool)
    (rs : Regs w 48) (m : Memory w) {base n r H P g v k : ℕ}
    (h : PortResultRegisters rs base n r P g v k)
    (hs : PortCode.result rs = (rawSource r H w v k).1) :
    ∃ t ≤ 14, Flow.once pub state bit portResult rs m = some (List.replicate t .tick,
      fieldResult rs (dispatchPort base n r H w P g v k).1, m) := by
  have present : rs 32 = rs 0 ↔ (rs 32).val = 0 := by rw [Fin.ext_iff, h.zero]
  rw [dispatchPort, ← hs]
  by_cases hz : (rs 32).val = 0
  · refine ⟨4, by decide, ?_⟩
    simp only [PortCode.result, portResult, Flow.once, present, hz, ↓reduceIte]
    rfl
  · have addr :
        (rs 22 * rs 7 + rs 33) * rs 6 + rs 11 + rs 12 + rs 8 + rs 3 + rs 1 + rs 34 =
          (rectangleAddress base n r g (rs 33).val (P+r+4+(rs 34).val) : Word w) := by
      simp only [rectangleAddress, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Fin.cast_val_eq_self, regCast h.group, regCast h.sites, regCast h.rowWidth,
        regCast h.baseAddr, regCast h.prefixWidth, regCast h.siteBits, regCast h.three,
        regCast h.one]
      ring
    have siteEq : (rs 33).val = v ↔ rs 23 = rs 33 := by rw [Fin.ext_iff, h.site, eq_comm]
    have offsetEq : (rs 34).val = k ↔ rs 25 = rs 34 := by rw [Fin.ext_iff, h.offset, eq_comm]
    by_cases hv : rs 23 = rs 33
    · refine ⟨14, by decide, ?_⟩
      by_cases hk : rs 25 = rs 34 <;>
        simp [PortCode.result, portResult, hz, present, Flow.once, sequence, bin, set, line,
          Op.effect, BinaryOp.eval, Function.update_idem, fieldResult, siteEq, offsetEq, hv, hk,
          encodeBit, addr] <;> rfl
    · refine ⟨13, by decide, ?_⟩
      simp [PortCode.result, portResult, hz, present, Flow.once, sequence, bin, set, line,
        Op.effect, BinaryOp.eval, Function.update_idem, fieldResult, siteEq, hv, encodeBit, addr]
      rfl

/-- Executing the physical block realizes the source and owner returned by
the scalar port dispatcher and preserves all other registers and memory. -/
theorem exec_portResult (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)
    {base n r H P g v k : ℕ} (h : PortResultRegisters rs base n r P g v k)
    (hs : PortCode.result rs = (rawSource r H w v k).1) :
    ∃ t ≤ 14, Flow.Exec pub state portResult rs m (List.replicate t .tick)
      (fieldResult rs (dispatchPort base n r H w P g v k).1) m := by
  obtain ⟨t, ht, he⟩ := once_portResult pub state false rs m h hs
  exact ⟨t, ht, (Flow.once_sound pub state false _ rs m he).1⟩

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
