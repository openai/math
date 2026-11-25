import OAI.Optimization.LinearProgramming.BitRAM.NativeMetadataEffect
import OAI.Optimization.LinearProgramming.BitRAM.ConfiguredEntry

/-! Install a native-generated metadata packet directly into the initial configuration
of a fixed bit program. The external arithmetic caller supplies only its native registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
open RAM RAM.Block RAM.Tape OracleSpec

def installControlInput (p : BitProgram) (encoder : Block) : Block := .seq encoder (configuredEntry p)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- An encoder's actual native run is followed in the same RAM by stack allocation and
input installation. Its output word never needs to be provided as a public scalar input. -/
theorem installControlInput_correct {p : BitProgram} {encoder : Block} {m u : Memory K}
    {P : K→Prop} {k : Nat} {w : Word} (written : Eval (Good P) encoder m k u)
    (effect : MetadataEffect m u w) (zero : P 0) (base : 3 ≤ m.index recvBaseReg) :
    ∃ t, Eval (Good P) (installControlInput p encoder) m (k+(18*w.length+p.stackCount+12)) t ∧
      Rep p (p.initial w) t ∧ MetadataEffect m t w := by
  have port := effect.headers recvBaseReg (by decide) (by decide) (by decide)
  have inWord : ScalarPacket u (u.index recvBaseReg) w := by rw [port]; exact effect.packet
  obtain ⟨t,read,rep,header,data,even⟩ := configuredEntry_complete_frame p w u written.safe_end zero
    (by rw [port]; exact base) effect.length inWord
  refine ⟨t,written.seq read,rep,⟨?_,(header _ (by decide) (by decide)).trans effect.length,
    fun i low high ne => (header i low high).trans (effect.headers i low high ne),
    fun i low ev => (even i low ev).trans (effect.even i low ev),?_⟩⟩
  · exact effect.packet.congr (fun _ _ => data _ (by omega) (by omega))
  · intro i low away
    exact (data i (by omega) (by omega)).trans (effect.data i low away)

end BitRAM
end LinearProgramming
end Optimization
end OAI
