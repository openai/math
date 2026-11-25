import OAI.Hierarchy.DescentTerminalMaskedProgram
import OAI.Hierarchy.DescentTerminalCompiledAdmission

namespace OAI
/-! # Protected seed, shelf and counted words in the native slotted and masked prefix -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open DescentTerminalVertexFields DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
variable {w b:ℕ} (S:Shape) (L:Layout) (F:MaskedShelf b) (m:Memory w) {a:ℕ}

theorem maskEvents_planned (slot : a<slotBase S L) (page : a<L.directory.texture.base)
    (event : a<L.emit.leaf.event.base) : maskEvents S L F m a=planned S L m a := by
  rw [maskEvents,issued,DescentTerminalChipRuntime.image_low _ _ _ _ event,afterMask,maskedMem,
    DescentTerminalChipRuntime.image_low _ _ _ _ page,slot_before S L m slot,planned,
    DescentTerminalChipRuntime.image_low _ _ _ _ event]

theorem maskEvents_counted (room : Room S L w) (frozen : Frozen L a) (slot : a<slotBase S L)
    (page : a<L.directory.texture.base) : maskEvents S L F m a=counted S L m a :=
  (maskEvents_planned S L F m slot page frozen.pages).trans (counted_preserved S L m room frozen)

theorem maskEvents_original (room : Room S L w) (safe : Protected L a) (slot : a<slotBase S L)
    (page : a<L.directory.texture.base) : maskEvents S L F m a=m a :=
  (maskEvents_planned S L F m slot page safe.print.pages).trans (planned_preserved S L m room safe)

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
