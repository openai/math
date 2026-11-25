import OAI.Hierarchy.DescentPackedPrivateSum
import OAI.Hierarchy.DescentPrivateExponentRAM

namespace OAI
/-! # Grouped terminal private names are counted in packed words on the actual emitter -/

namespace Hierarchy.DescentPackedTerminalExponent
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSIMDLookup DescentPackedPrivateSum
open scoped Fin.CommRing BigOperators Classical
noncomputable section

variable {w : ℕ} (L : Layout) (O : DescentPrivateExponentRAM.Banks)

def program (w n M p : ℕ) := (L.program w 1 n M).seq (O.program w p)

def image (n M p : ℕ) (m : Memory w) : Memory w :=
  let prior:=L.image 1 n M m
  O.result p (prior O.usedWords).val prior

theorem run (n M p : ℕ) (m : Memory w) (space : L.Room w 1 n M) (last : O.Room w) :
    (program L O w n M p).Exec m (image L O n M p m) (Layout.billed 1 n M+O.steps p) := by
  let prior:=L.image 1 n M m
  have scale : (O.program w p).Exec prior (image L O n M p m) (O.steps p) :=
    O.run p (prior O.usedWords).val prior last (by simp)
  intro P R C mach pc reg pub exit rom advice cfg raw enter equal
  exact Procedure.Exec.then (L.run m space) scale mach pc reg pub exit rom advice cfg raw enter equal

theorem tariff (w n A p : ℕ) (ha : 0<A) (wide : 2*A≤w) :
    (Layout.billed 1 n (lanes w A)+O.steps p)*w ≤
      40*(w+w+4*n*A)+(56+4*ProtocolRAMPortScale.bitWidth p)*w ∧ 2^(A*lanes w A)≤2^(w/2) := by
  obtain ⟨work,rom⟩:=Layout.tariff w 1 n A ha wide
  refine ⟨?_,rom⟩
  rw [Nat.add_mul,DescentPrivateExponentRAM.steps_eq]
  exact Nat.add_le_add_right (by simpa using work) _

end
end Hierarchy.DescentPackedTerminalExponent

end OAI
