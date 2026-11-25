import OAI.Hierarchy.ProtocolRAMCalendarMesh
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # Original calendar choices, their encodings and reachable prefixes -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM.Calendar Tagged
open scoped Classical
variable {X : Type}

structure Slot (X : Type) where
  bits : ℕ
  choice : X→Type
  [finite : ∀x,Fintype (choice x)]
  word : ∀x,choice x ↪ Bits bits
  next : ∀x,choice x→X
attribute [instance] Slot.finite

/-- A feed writes no private word, while still performing the required stock transition. -/
def feed (change : X→X) : Slot X where
  bits := 0
  choice := fun _=>Unit
  word _ := ⟨fun _=>Fin.elim0,fun _ _ _=>Subsingleton.elim ..⟩
  next x _ := change x

variable (slot : Event→Slot X)

def bits : List Event→ℕ
  | []=>0
  | e::es=>(slot e).bits+bits es

def Path : List Event→X→Type
  | [],_=>Unit
  | e::es,x=>Σ c:(slot e).choice x, Path es ((slot e).next x c)

variable (events : List Event) (x₀ : X)

/-- Retains the original selected branch at each previous event. Disjoint
histories may produce the same memory or the same width vector. -/
inductive Prefix : List Event→X→Type
  | start : Prefix events x₀
  | advance {e : Event} {tail : List Event} {x : X} (old : Prefix (e::tail) x)
      (choice : (slot e).choice x) : Prefix tail ((slot e).next x choice)

/-- Finite future event lists can be completed if each reached event offers a choice. -/
theorem Prefix.nonempty_path
    (canStep : ∀ {e tail x}, Prefix slot events x₀ (e::tail) x → Nonempty ((slot e).choice x))
    {tail : List Event} {x : X} (h : Prefix slot events x₀ tail x) : Nonempty (Path slot tail x) := by
  induction tail generalizing x with
  | nil => exact ⟨()⟩
  | cons e tail ih =>
    obtain ⟨c⟩ := canStep h
    obtain ⟨p⟩ := ih (Prefix.advance h c)
    exact ⟨⟨c,p⟩⟩

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
