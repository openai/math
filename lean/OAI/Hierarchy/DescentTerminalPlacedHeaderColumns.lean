import Mathlib.Tactic.FinCases
import OAI.Hierarchy.DescentTerminalHeaderEmit
import OAI.Hierarchy.DescentTerminalRouteSources
import OAI.Hierarchy.DescentTerminalScalarLiterals

namespace OAI
/-! # The twelve physical bank operands of each of the two terminal header scans -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalEmitter.Compact
open DescentTerminalRowArena DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Fixed) (O : Output)

/-- The lane and the two field lookups are replaced by the actual allocator parity
and by the two measured prefix banks in `AddressPlan.inputs`. -/
def operand (j : ℕ) : Bank :=
  match j%12 with
  | 0 => s.half
  | 1 => s.lane
  | 2 => O.active
  | 3 | 6 | 7 => s.identity
  | 5 => O.mode
  | 9 => O.source
  | _ => s.zero

def columns (other : Columns) (j : Fin 43) : Compact.Column :=
  if j.val<24 then .attained (operand s O j.val) else other j

def placed (cfg : DescentTerminalCompiledPrefix.Shape) (other : Input) (blank : ℕ) : Input :=
  { other with
    sources := columns s O other.sources
    indexEvents := cfg.terminal.rows
    formatEvents := cfg.terminal.rows
    blank := blank }

def Uses (col : Columns) : Prop := ∀ j : Fin 43, j.val<24 → col j=.attained (operand s O j.val)

theorem placed_uses (cfg : DescentTerminalCompiledPrefix.Shape) (J : Input) (blank : ℕ) :
    Uses s O (placed s O cfg J blank).sources := by
  intro j hj
  exact ite_eq_left hj

theorem routed {col : Columns} (h : Uses s O col) (T : RouteSources.Tables) (A : Arena) :
    Uses s O (T.columns A col) := by
  intro j hj
  have same : T.columns A col j = col j := by
    fin_cases j <;> first | rfl | (exfalso; revert hj; decide)
  exact same.trans (h j hj)

theorem scalar {col : Columns} (h : Uses s O col) (q t H N A p v W B pool : ℕ) :
    Uses s O (ScalarLiterals.columns q t H N A p v W B pool col) := by
  intro j hj
  have same : ScalarLiterals.columns q t H N A p v W B pool col j = col j := by
    fin_cases j <;> first | rfl | (exfalso; revert hj; decide)
  exact same.trans (h j hj)

variable (cfg : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ)
/-- The physical lane lookup is the row allocator's parity table. -/
def fixed : Fixed := {s with lane:=Allocation.parity (rowArena cfg I base).start}

theorem operands (prior : Uses s O I.sources) (fmt : Bool) :
    Allocation.legs (inputs cfg I base) fmt =
      wires (fixed s cfg I base) O
        (if fmt then (bodyPlane cfg I base).header.control else (bodyPlane cfg I base).header.index)
        (if fmt then (publicHeader cfg I base).control else (publicHeader cfg I base).index) := by
  have hv (j : Fin 43) (hj : j.val<24) :
      Compact.view (pageEnd cfg I base) I.sources j = operand s O j.val := by
    simp only [Compact.view,prior j hj]
  cases fmt <;>
    simp (config := {decide := true}) [Allocation.legs,inputs,wires,fixed,hv,operand]

/-- Equality of the entire native header, including the sink, read shift, source,
and event count. There is one paid event for every row. -/
theorem issuer (prior : Uses s O I.sources) (ni : I.indexEvents=cfg.terminal.rows)
    (nf : I.formatEvents=cfg.terminal.rows) (fmt : Bool) :
    (if fmt then (emitter cfg I base).formats else (emitter cfg I base).indices) =
      let dest := if fmt then (emitter cfg I base).formats else (emitter cfg I base).indices
      DescentTerminalHeaderDraft.header cfg.terminal.rows (fixed s cfg I base) O
        (if fmt then (bodyPlane cfg I base).header.control else (bodyPlane cfg I base).header.index)
        (if fmt then (publicHeader cfg I base).control else (publicHeader cfg I base).index)
        dest.output dest.src (if fmt then 0 else cfg.terminal.plane.rawRows+2)
        (if fmt then I.blank else 0) := by
  cases fmt <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,emitter,Allocation.layout,Allocation.header,
      DescentTerminalHeaderDraft.header,operands s O cfg I base prior,ni,nf]

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
