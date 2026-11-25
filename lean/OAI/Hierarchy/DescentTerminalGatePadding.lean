import OAI.Hierarchy.DescentTerminalBinFormat

namespace OAI
/-! Padding a finite family of terminal bin controls with the empty route. -/
namespace Hierarchy.DescentTerminalScalarPadded
open DescentTerminalBinReaddress
noncomputable section
variable {K cap W q : ℕ}

def pad {n m : ℕ} {A : Type} (f : Fin n→A) (zero : A) (i : Fin m) :=
  if live : i.val<n then f ⟨_,live⟩ else zero
@[simp] theorem pad_front {n m : ℕ} {A : Type} (fit : n ≤ m) (f : Fin n→A) (zero : A) (i : Fin n) :
    pad f zero (i.castLE fit)=f i := by simp [pad,i.isLt]

def emptyGate (W q : ℕ) := DescentTerminalBinFormat.encode (fun _ : Slot W q=>none)
def gates (ctl : Fin K→Tagged.Row (DescentTerminalBinFormat.controlBits W q)) :
    Fin cap→Tagged.Row (DescentTerminalBinFormat.controlBits W q) := pad ctl (emptyGate W q)

end
end Hierarchy.DescentTerminalScalarPadded

end OAI
