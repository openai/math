import OAI.Computability.VPVNP.PairShrinkHiddenGuess
import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-! # Exact branch stream, reads and clock for a native hidden-field scan -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {W : ℕ}

private theorem field_cost (g : Args W) (m : Memory W) (ptr : ℕ) (e : Row) :
    (fieldEvents g m ptr e).length = 22+6*e.2.length ∧
      countProbes (fieldEvents g m ptr e) = 3 ∧ choiceBits (fieldEvents g m ptr e) = e.2 := by
  let id := m (ptr : Word W).val
  have hdr := ShrinkHiddenWidth.cost m (ptr : Word W)
    (ShrinkHiddenWidth.rowBase g.termBase g.termStride id)
    (ShrinkHiddenWidth.coordinate (g.layout.toNat : Word W) id)
  change (g.header m (ptr : Word W)).length = 18 ∧ countProbes (g.header m (ptr : Word W)) = 3 ∧
    choiceBits (g.header m (ptr : Word W)) = [] at hdr
  obtain ⟨len, probes, bits⟩ := hdr
  have hf := PrivateFields.events_work (w := W) .guess e.2
  simp [fieldEvents, len, countProbes_append, probes, hf, countProbes, choiceBits,
    PrimedInputRAM.Flow.choiceBits_append, bits, PrivateFields.events_bits]
  omega

private theorem loop_cost (g : Args W) (m : Memory W) (ptr : ℕ) (es : List Row) :
    (loopEvents g m ptr es).length = 1+25*es.length+6*(stream es).length ∧
      countProbes (loopEvents g m ptr es) = 3*es.length ∧ choiceBits (loopEvents g m ptr es) = stream es := by
  induction es generalizing ptr with
  | nil => simp [loopEvents, countProbes, choiceBits, stream]
  | cons e es ih =>
    obtain ⟨hlen, hpr, hbs⟩ := ih (ptr+1)
    obtain ⟨len, probes, bits⟩ := field_cost g m ptr e
    simp only [stream] at hlen hbs
    simp only [loopEvents, List.length_append, List.length_cons, List.length_nil, hlen, len,
      countProbes_append, countProbes, probes, hpr, PrimedInputRAM.Flow.choiceBits_append, choiceBits,
      bits, hbs, stream, List.flatMap_cons, List.append_nil, Nat.mul_add]
    exact ⟨by omega, by omega, trivial⟩

/-- The only external probes are one count word and three words per field.
Each independently guessed bit is present exactly once in the native trace. -/
theorem cost (g : Args W) (m : Memory W) (es : List Row) :
    (events g m es).length = 7+25*es.length+6*(stream es).length ∧
      countProbes (events g m es) = 1+3*es.length ∧ choiceBits (events g m es) = stream es := by
  obtain ⟨hlen,hpr,hbs⟩ := loop_cost g m g.row es
  simp only [events, List.length_append, countProbes_append, PrimedInputRAM.Flow.choiceBits_append, hlen,hpr,hbs]
  simp [setupEvents, countProbes, choiceBits]
  omega

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
