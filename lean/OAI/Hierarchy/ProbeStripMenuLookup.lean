import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # One-indexed native lookup for the original finite strip menu -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {sites N w : ℕ} [Nonempty (Fin sites)] {edge : E→Chord sites} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ}

def entry (m : Probe.FixedMenu F edge req box ε tree N) (packet : Expr)
    (f : m.index → ℕ) : Expr :=
  chooseField (Fintype.card m.index) 1 (fun i => .lit (f ((Fintype.equivFin m.index).symm i))) packet

theorem entry_read (m : Probe.FixedMenu F edge req box ε tree N) (packet : Expr)
    (f : m.index → ℕ) (i : m.index) (mem : Memory w) (r : Word w)
    (room : 1+Fintype.card m.index ≤ 2^w)
    (hit : (packet.eval mem r).val=(Fintype.equivFin m.index i).val+1) :
    (entry m packet f).eval mem r = (f i : Word w) := by
  rw [entry,eval_chooseField _ _ _ _ _ _ (Fintype.equivFin m.index i) room
    (by simpa only [Nat.add_comm] using hit)]
  simp [Expr.eval]

end Hierarchy.ProtocolRAM.StripDirectory

namespace Hierarchy.ProtocolRAM.CatalystArchive
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {sites N w : ℕ} [Nonempty (Fin sites)] {edge : E→Chord sites} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ}

/-- A frozen word numbers its menu entries from one. An out-of-range
word selects the zero expression at the end of the native lookup. -/
def menuIndex (J : Type*) [Fintype J] (code : ℕ) : Option J :=
  if h : 0<code ∧ code≤Fintype.card J then
    some ((Fintype.equivFin J).symm ⟨code-1,by omega⟩) else none

theorem menuIndex_code {J : Type*} [Fintype J] (i : J) :
    menuIndex J ((Fintype.equivFin J i).val+1)=some i := by
  have range := (Fintype.equivFin J i).isLt
  simp [menuIndex,range]

theorem entry_word (menu : Probe.FixedMenu F edge req box ε tree N) (key : Expr)
    (f : menu.index→ℕ) (m : Memory w) (row : Word w) (room : 1+Fintype.card menu.index≤2^w)
    (positive : 0<(key.eval m row).val) :
    (StripDirectory.entry menu key f).eval m row =
      ((menuIndex menu.index (key.eval m row).val).elim 0 f : ℕ) := by
  let code := (key.eval m row).val
  have cp : 0<code := positive
  by_cases bound : code≤Fintype.card menu.index
  · let j : Fin (Fintype.card menu.index) := ⟨code-1,by omega⟩
    let i := (Fintype.equivFin menu.index).symm j
    have hit : (key.eval m row).val=(Fintype.equivFin menu.index i).val+1 := by
      change code=_
      simp only [i,Equiv.apply_symm_apply,j]
      omega
    rw [StripDirectory.entry_read menu key f i m row room hit,hit,menuIndex_code]
    rfl
  · have none : menuIndex menu.index (key.eval m row).val=none := by
      change menuIndex menu.index code=none
      exact dite_eq_right (fun h=>bound h.2)
    rw [none]
    apply eval_chooseField_outside _ _ _ _ _ _ room
    change 1+Fintype.card menu.index≤code
    omega

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
