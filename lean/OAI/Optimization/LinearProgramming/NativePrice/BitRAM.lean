import OAI.Optimization.LinearProgramming.NativePrice.Tape
import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout

/-! Convert the actual BitRAM exchange-window invariant to a scalar-bit tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM OracleSpec

theorem scalarPacket_iff_wordAt {K : Type*} [AddMonoidWithOne K]
    (m : Memory K) (c : ℕ) (w : Word) : BitRAM.ScalarPacket m c w ↔ WordAt m c w := by
  have cv (b : Bool) : (BitRAM.bitScalar b : K)=(b.toNat:K) := by
    cases b <;> simp [BitRAM.bitScalar]
  simp only [BitRAM.ScalarPacket,WordAt,cv]

end NativePrice
end LinearProgramming
end Optimization
end OAI
