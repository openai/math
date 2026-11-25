import OAI.Hierarchy.ProtocolRAMCalendarBootChoices
import OAI.Hierarchy.TaggedWireHeaderLocal

namespace OAI
/-! # The exposed tag rows and the private counters in the actual CPU header -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.Boot
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native WireTelescope.CalendarTape
open scoped Classical Fin.CommRing
variable {z d k jobs : ℕ}
local notation "W" => wordBits z d copies
variable (v : Fin jobs→Market z d k) (size : ℕ)

def tagRows (tags : Fin (2^z)→Word W) (fixed : Tape z d) : Tape z d :=
  fun x=>if hx : x<2^z then tags ⟨x,hx⟩ else fixed x

/-- Boot forwards every root tag, even for an arbitrary binary row assignment. -/
theorem header_root_word (layout : Layout v size) (words : Tape z d) (i : Fin (2^z)) :
    header v size words i.val=words i.val := by
  have small:=i.isLt.trans_le (root_extent (z:=z) (d:=d))
  have outside (j : Fin jobs) : ¬ProtocolRAMStaticSlabs.Inside (fun t=>low (v t)) (fun t=>high (v t)) j i.val :=
    fun hit=>(small.trans_le (layout.afterHeap j)).not_ge hit.1
  rw [header,inputTape_root _ i.isLt,controller,ProtocolRAMStaticSlabs.outside _ _ outside]
  simp [Computability.VPVNP.RAMMemory.initialMemory,small.trans_le layout.subdivision]

theorem header_tagRows (layout : Layout v size) (tags : Fin (2^z)→Word W) (fixed : Tape z d) :
    header v size (tagRows tags fixed)=tagRows tags (header v size fixed) := by
  funext x
  by_cases hx : x<2^z
  · exact (header_root_word v size layout (tagRows tags fixed) ⟨x,hx⟩).trans
      (by simp [tagRows,hx])
  · rw [show tagRows tags (header v size fixed) x=header v size fixed x by simp [tagRows,hx]]
    exact header_cell v size _ _ x (by simp [tagRows,hx])

theorem header_slots {X : Type} {slot : Event→Slot X} (L : WordSlots slot W) (es : List Event) (raw : Tagged.Bits (bits slot es))
    (fixed : Tape z d)
    (pages : ∀e∈es,∀x,L.inside e x→heapEnd z d copies≤x ∧ x<size ∧
      ∀i,¬ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i x) :
    header v size (L.header es raw fixed)=L.header es raw (header v size fixed) := by
  apply L.header_local (header v size) (header_cell v size) es raw fixed
  intro mem e he x inside
  obtain ⟨above,small,unused⟩:=pages e he x inside
  rw [header,inputTape_above _ above,controller,ProtocolRAMStaticSlabs.outside _ _ unused]
  simp [Computability.VPVNP.RAMMemory.initialMemory,small]

end Hierarchy.ProtocolRAM.Calendar.Boot
end

end OAI
