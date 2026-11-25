import OAI.ThreeFlat.RAM.TickTerminalHardware

namespace OAI
/-! # Fixed architecture and terminal width of selected-root replay -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open private addressTemplate from OAI.ThreeFlat.RAM.TickTerminalRootPrice
open private dimensions sizes_at native_dimensions sizes shapeOfSizes from OAI.ThreeFlat.RAM.TickTerminalHardware

attribute [local irreducible] many sizes shapeOfSizes
set_option backward.isDefEq.respectTransparency true

private theorem match_sizes {W V : ℕ} (A B : Arena) (same : sizes W A=sizes V B) :
    dimensions (many W A) = dimensions (many V B) := by
  have bridge := congrArg shapeOfSizes same
  exact (native_dimensions W A).trans (bridge.trans (native_dimensions V B).symm)

private theorem same_fields {W V : ℕ} (p : Procedure W) (q : Procedure V)
    (l r s : ℕ) (h : dimensions p=dimensions q) (L : q.labels=l) (R : q.registers=r) (S : q.slots=s) :
    p.labels=l ∧ p.registers=r ∧ p.slots=s :=
  ⟨(congrArg Prod.fst h).trans L,(congrArg (fun t=>t.2.1) h).trans R,
    (congrArg (fun t=>t.2.2) h).trans S⟩

attribute [local irreducible] dimensions

private structure HardwareReceipt where
  labels : ℕ
  registers : ℕ
  slots : ℕ
  measured : ∀ W A,(many W A).labels=labels ∧ (many W A).registers=registers ∧ (many W A).slots=slots

private def reading (width : ℕ) (board : Arena) : HardwareReceipt where
  labels := (many width board).labels
  registers := (many width board).registers
  slots := (many width board).slots
  measured := fun W A =>
    same_fields (many W A) (many width board) _ _ _
      (@match_sizes W width A board ((sizes_at W A).trans (sizes_at width board).symm)) rfl rfl rfl

/-- Seal the measured certificate so that taking a scalar projection does not
normalize the entire reference ROM during kernel conversion. -/
private opaque reference : HardwareReceipt := reading 1 addressTemplate

/-- The fixed hardware counts are the three projections of the measured native procedure. -/
def rootLabels : ℕ := reference.labels
def rootRegisters : ℕ := reference.registers
def rootSlots : ℕ := reference.slots

theorem many_shape (W : ℕ) (A : Arena) :
    (many W A).labels=rootLabels ∧ (many W A).registers=rootRegisters ∧ (many W A).slots=rootSlots :=
  reference.measured W A

end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open HistoryTerminalTape
open scoped BigOperators

theorem words_eq (T : Root) (raw : ℕ→ℕ) :
    TickTerminalPrimitive.words T raw=T.ext+(∑ i : Fin T.halves,(half T raw i.val).width)+4*T.rows := by
  let a (i : ℕ) := if i=0 then T.ext else (half T raw (i-1)).width
  have tab : (List.range' 0 (T.halves+1)).map a=List.ofFn (fun i : Fin (T.halves+1)=>a i.val) := by
    apply List.ext_getElem
    · simp
    · intro j h h'
      simp only [List.getElem_map,List.getElem_range',List.getElem_ofFn,Nat.one_mul,Nat.zero_add]
  change ((List.range' 0 (T.halves+1)).map a).sum+_=_
  rw [tab,List.sum_ofFn,Fin.sum_univ_succ]
  simp [a]

/-- The numerical root charge includes all final incident wires and inherited endpoint
pairs. The number of half-ports is bounded by the fixed degree even at width zero. -/
theorem charge_covers (T : Root) (raw : ℕ→ℕ) {degreeCap pairs amount rowFactor : ℕ}
    (degree : T.halves≤degreeCap) (endpoints : T.ext≤2*pairs)
    (floor : 1+(∑ i : Fin T.halves,(half T raw i.val).width)+pairs≤amount)
    (rows : T.rows≤rowFactor*amount) :
    1+T.halves+TickTerminalPrimitive.words T raw≤(degreeCap+4*rowFactor+3)*amount := by
  rw [words_eq]
  have unit : 1≤amount := by omega
  have sites : degreeCap≤degreeCap*amount := by simpa using Nat.mul_le_mul_left degreeCap unit
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
  omega


end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
