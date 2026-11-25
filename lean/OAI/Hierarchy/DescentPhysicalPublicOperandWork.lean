import OAI.Hierarchy.DescentPhysicalPublicOperandInputs
import OAI.Hierarchy.DescentResetControlRegisters

namespace OAI
/-! # Expression work of every public operand column, including acquired packet fields -/
namespace Hierarchy
open ProtocolRAM DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
namespace DescentResetPublicOperandBook.Ports

variable (P : Ports)

theorem work_bounded (t : ℕ) (active : P.active.work≤t) (regs : ∀j,(P.registers j).work≤t)
    (aux : ∀j,(P.aux j).work≤25) (x : ℕ) (control : Port) : (P.expr x control).work≤ max t 80 :=by
  have cast (i : Fin 3) (e : Expr) :
      (P.casts.expr P.castBase i e).work≤e.work+16 :=by
    unfold DescentOperandPublicCasts.Plan.expr DescentOperandInputCast.expr
    rw [DescentPackedZip.work]
    have z : (Expr.lit 0).work≤5:=by decide
    omega
  cases control with
  | active=>exact active.trans (Nat.le_max_left ..)
  | register j=>exact (regs j).trans (Nat.le_max_left ..)
  | empty=>exact (by decide : (Expr.lit 0).work≤80).trans (Nat.le_max_right ..)
  | aux j=>exact ((cast 2 _).trans ((Nat.add_le_add_right (aux j) 16).trans (by decide))).trans (Nat.le_max_right t 80)
  | coordinate j lo=>
    simp only [expr]
    split
    next h=>
      have short : (P.coordinates.src P.coordinateBase P.saved j ⟨x,h.1⟩ ⟨lo,h.2⟩).work≤40:=of_decide_eq_true rfl
      exact ((cast 1 _).trans ((Nat.add_le_add_right short 16).trans (by decide))).trans (Nat.le_max_right t 80)
    next=>exact (by decide : (Expr.lit 0).work≤80).trans (Nat.le_max_right ..)
  | packet f j=>
    simp only [expr]
    split
    next h=>
      have short:=(P.packets.lane P.packetBase f).src_work ⟨j,h.1⟩ ⟨x,h.2⟩
      exact ((cast 0 _).trans ((Nat.add_le_add_right short 16).trans (by decide))).trans (Nat.le_max_right t 80)
    next=>exact (by decide : (Expr.lit 0).work≤80).trans (Nat.le_max_right ..)
end DescentResetPublicOperandBook.Ports

namespace DescentDatedAddressBook.PhysicalReset.OperandMenu
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (m : OperandMenu z roots)

theorem publicInput_work (sh : a.StencilShape) (start : ℕ) (count hub : Bank) (g Y : ℕ)
    (live : Expr) (reg : Fin 4→Expr) (t : ℕ) (lw : live.work≤t) (rw : ∀i,(reg i).work≤t)
    (x : ℕ) (j : Fin a.successor.setup.fallbackInputs) :
    (m.publicInput sh start count hub g Y live reg x j).work≤ max t 80 :=by
  apply DescentResetPublicOperandBook.Ports.work_bounded _ t lw rw
  intro i
  exact le_of_eq (DescentResetHaloBroadcast.amount ..)

theorem named_public_input_work (sh : a.StencilShape) (start : ℕ) (count hub : Bank) (g Y : ℕ)
    (ctrl : DescentResetControlRegisters.Chart) (floor cap : ℕ) (inverse depth levels : Bank)
    (x : ℕ) (j : Fin a.successor.setup.fallbackInputs) :
    (m.publicInput sh start count hub g Y (ctrl.live floor x)
      (ctrl.ports floor cap x inverse depth levels) x j).work≤250 :=by
  apply m.publicInput_work sh start count hub g Y _ _ 250
  · exact of_decide_eq_true rfl
  · intro i
    fin_cases i <;> exact of_decide_eq_true rfl

end DescentDatedAddressBook.PhysicalReset.OperandMenu
end
end Hierarchy

end OAI
