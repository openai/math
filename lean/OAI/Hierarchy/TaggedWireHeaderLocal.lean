import OAI.Hierarchy.ProtocolRAMAdviceLocal
import OAI.Hierarchy.TaggedWireHeaderRestore

namespace OAI
/-! # Commuting fixed public ROM loading with chronological private bits -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.WordSlots
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
variable {X : Type} {W : ℕ} {slot : Event→Slot X} (L : WordSlots slot W)

theorem header_local (U : Memory W→Memory W) (loc : AdviceLocal U) (es : List Event)
    (raw : Bits (bits slot es)) (m : Memory W)
    (untouched : ∀mem : Memory W,∀e∈es,∀x,L.inside e x→U mem x=mem x) :
    U (L.header es raw m)=L.header es raw (U m) := by
  induction es with
  | nil=>rfl
  | cons e es ih=>
    let a : Bits (slot e).bits:=fun j=>raw (Fin.castAdd (bits slot es) j)
    let b : Bits (bits slot es):=fun j=>raw (Fin.natAdd (slot e).bits j)
    change U (L.install e a (L.header es b m))=L.install e a (L.header es b (U m))
    have tails : U (L.header es b m)=L.header es b (U m):=
      ih b (fun mem t ht x hx=>untouched mem t (List.mem_cons_of_mem _ ht) x hx)
    funext x
    by_cases hit:L.inside e x
    · rw [untouched _ e (List.mem_cons_self ..) x hit]
      exact L.install_on e a _ _ x hit
    · rw [L.install_off e a _ x hit]
      exact (loc _ _ x (L.install_off e a _ x hit)).trans (congrFun tails x)

end Hierarchy.WireTelescope.CalendarTape.WordSlots
end

end OAI
