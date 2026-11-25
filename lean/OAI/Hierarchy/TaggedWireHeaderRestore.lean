import OAI.Hierarchy.TaggedWireTapeMemory

namespace OAI
/-! # Every assignment of private word pages comes from its literal binary header -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.WordSlots
open ProtocolRAM ProtocolRAM.Calendar Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical
variable {X : Type} {W : ℕ} {slot : Event→Slot X} (L : WordSlots slot W)

def inside (e : Event) (u : ℕ) := L.base e≤u ∧ u<L.base e+L.cells e

theorem install_off (e : Event) (v : Bits (slot e).bits) (m : Memory W) (u : ℕ) (off : ¬L.inside e u) :
    L.install e v m u=m u := by
  unfold inside at off
  simp only [install,fillSegment,ite_eq_right off]

theorem install_on (e : Event) (v : Bits (slot e).bits) (m m' : Memory W) (u : ℕ) (here : L.inside e u) :
    L.install e v m u=L.install e v m' u := by
  unfold inside at here
  simp only [install,fillSegment,ite_eq_left here]

theorem install_read (e : Event) (m : Memory W) : L.install e (L.read e m) m=m := by
  have data : (fun i=>L.read e m (Fin.cast (L.width e).symm i))=
      arrayBits (L.cells e) W (fun j=>m (L.base e+j.val)) := by funext i;rfl
  funext u
  by_cases h:L.inside e u
  · unfold inside at h
    have lt : u-L.base e<L.cells e := by omega
    simp only [install,fillSegment,ite_eq_left h,data,Equiv.symm_apply_apply,dite_eq_left lt,
      Nat.add_sub_of_le h.1]
  · exact L.install_off _ _ _ _ h

theorem header_at (es : List Event) (source baseline : Memory W) (u : ℕ) :
    L.header es (L.static es source) baseline u=
      if ∃e∈es,L.inside e u then source u else baseline u := by
  induction es with
  | nil=>simp [header]
  | cons e es ih=>
    change L.install e _ (L.header es _ baseline) u=_
    simp only [static,Fin.addCases_left,Fin.addCases_right]
    by_cases here:L.inside e u
    · rw [L.install_on _ _ _ source u here, L.install_read,ite_eq_left ⟨e,List.mem_cons_self ..,here⟩]
    · rw [L.install_off _ _ _ u here,ih]
      simp [here]

theorem header_restore (es : List Event) (source baseline : Memory W)
    (off : ∀u,(¬∃e∈es,L.inside e u)→source u=baseline u) :
    L.header es (L.static es source) baseline=source := by
  funext u
  rw [L.header_at]
  split
  · rfl
  · exact (off _ (by assumption)).symm

end Hierarchy.WireTelescope.CalendarTape.WordSlots

end
end OAI
