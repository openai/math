import OAI.Hierarchy.TaggedWireHeaderRestore
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # A header pin is wired to its original chronological selector bit -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.WordSlots
open ProtocolRAM ProtocolRAM.Calendar Tagged Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical
variable {X : Type} {W : ℕ} {slot : Event→Slot X} (L : WordSlots slot W)

def cellBit (e : Event) (a : ℕ) (here : L.inside e a) (j : Fin W) : Fin (slot e).bits :=
  Fin.cast (L.width e).symm (finProdFinEquiv (⟨a-L.base e,by obtain ⟨_,_⟩:=here;omega⟩,j))

/-- An earlier event in the source list writes last. The formula therefore works
also for overlapping word pages and for zero-bit feed events. -/
def headerBit : (es : List Event) → ℕ → Fin W → Option (Fin (bits slot es))
  | [],_,_=>none
  | e::es,a,j=>
    if here : L.inside e a then some (Fin.castAdd (bits slot es) (L.cellBit e a here j))
    else (headerBit es a j).map (Fin.natAdd (slot e).bits)

theorem cellBit_read (e : Event) (a : ℕ) (here : L.inside e a) (j : Fin W)
    (b : Bits (slot e).bits) (m : Memory W) :
    ((L.install e b m a).val.testBit j.val)=b (L.cellBit e a here j) := by
  have k : a-L.base e<L.cells e:=by obtain ⟨_,_⟩:=here;omega
  let q : Fin (L.cells e):=⟨a-L.base e,k⟩
  have address : L.base e+q.val=a:=Nat.add_sub_of_le here.1
  have read:=congrFun (L.read_install e b m) (L.cellBit e a here j)
  change arrayBits (L.cells e) W (fun i=>L.install e b m (L.base e+i.val))
      (finProdFinEquiv (q,j))=b (L.cellBit e a here j) at read
  simpa only [arrayBits_at,address,←Computability.VPVNP.LiveHeader.testBit_wordBits] using read

theorem headerBit_read (es : List Event) (a : ℕ) (j : Fin W) (b : Bits (bits slot es)) (m : Memory W) :
    ((L.header es b m a).val.testBit j.val)=((L.headerBit es a j).map b).getD ((m a).val.testBit j.val) := by
  induction es with
  | nil=>rfl
  | cons e es ih=>
    let front:=fun i=>b (Fin.castAdd (bits slot es) i)
    let rest:=fun i=>b (Fin.natAdd (slot e).bits i)
    by_cases here : L.inside e a
    · rw [headerBit, dite_eq_left here]
      change (L.install e front (L.header es rest m) a).val.testBit j.val =
        front (L.cellBit e a here j)
      exact L.cellBit_read e a here j front (L.header es rest m)
    · change ((L.install e front (L.header es rest m) a).val.testBit j.val)=_
      rw [L.install_off _ _ _ _ here,ih rest]
      simp only [headerBit,dite_eq_right here]
      cases L.headerBit es a j <;> rfl

end Hierarchy.WireTelescope.CalendarTape.WordSlots

end
end OAI
