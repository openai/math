import OAI.Hierarchy.TaggedWirePathCore

namespace OAI
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM.Calendar Tagged
open scoped Classical
variable {X : Type}
variable (slot : Event→Slot X)

instance finitePath : ∀ es x,Fintype (Path slot es x)
  | [],_=>inferInstanceAs (Fintype Unit)
  | e::es,x=>
    letI : ∀c:(slot e).choice x,Fintype (Path slot es ((slot e).next x c)) := fun _c=>finitePath es _
    inferInstanceAs (Fintype (Σ c:(slot e).choice x,Path slot es ((slot e).next x c)))

def terminal : (es : List Event) → (x : X) → Path slot es x → X
  | [],x,_=>x
  | e::es,x,a=>terminal es ((slot e).next x a.1) a.2

private theorem join_injective {A : Type} {B : A → Type} {m n : ℕ}
    (head : A ↪ Bits m) (tail : (a : A) → B a ↪ Bits n) :
    Function.Injective (fun p : Sigma B => (Fin.addCases (head p.1) (tail p.1 p.2) : Bits (m+n))) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ eqn
  change (Fin.addCases (head a) (tail a u) : Bits (m+n)) = Fin.addCases (head b) (tail b v) at eqn
  have same : a = b := head.injective (funext fun j => by
    simpa only [Fin.addCases_left] using congrFun eqn (Fin.castAdd n j))
  subst b
  have sameTail : u = v := (tail a).injective (funext fun j => by
    simpa only [Fin.addCases_right] using congrFun eqn (Fin.natAdd m j))
  subst v
  rfl

private def joinWords {A : Type} {B : A → Type} {m n : ℕ}
    (head : A ↪ Bits m) (tail : (a : A) → B a ↪ Bits n) : Sigma B ↪ Bits (m+n) where
  toFun p := Fin.addCases (head p.1) (tail p.1 p.2)
  inj' := join_injective head tail

def encode : (es : List Event) → (x : X) → Path slot es x ↪ Bits (bits slot es)
  | [],_ => (⟨fun _ => Fin.elim0, fun _ _ _ => Subsingleton.elim ..⟩ : Unit ↪ Bits 0)
  | e::es,x => joinWords ((slot e).word x) (fun c => encode es ((slot e).next x c))

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
