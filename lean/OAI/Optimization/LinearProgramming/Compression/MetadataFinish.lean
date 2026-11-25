import OAI.Optimization.LinearProgramming.Compression.MetadataStart
import OAI.Optimization.LinearProgramming.BitRAM.NativeMetadataEffect

/-! Link an appended wire with the configured bit-machine entry, without touching its numerical cache. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

open RAM OracleSpec BitRAM

variable {K : Type*} [Zero K] [One K]

theorem Started.finish {s a t : Memory K} {word : Word} (h : Started s a) (ef : Effect a t word) :
    MetadataEffect s t word := by
  constructor
  · change ScalarPacket t (s.index 47) word
    simpa only [h.cursor] using ef.packet
  · change t.index 49=word.length
    rw [ef.length,h.length,Nat.zero_add]
  · intro i lo hi hn
    change i≠49 at hn
    exact (ef.frame i hn (by omega) (by omega) (by omega)).trans (h.frame i hn (by omega) (by omega) (by omega))
  · intro i lo even
    exact (ef.frame i (by omega) (by omega) (by omega) (by omega)).trans
      (h.frame i (by omega) (by omega) (by omega) (by omega))
  · intro i hi outside
    change i<s.index 47 ∨ s.index 47+word.length ≤ i at outside
    exact (ef.outside i (by simpa only [h.cursor] using outside)).trans (h.data i hi)

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
