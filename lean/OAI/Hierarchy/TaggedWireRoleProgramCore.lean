import OAI.Hierarchy.ProbePositiveSiteExpr
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Four native columns for the signed endpoints of a turn -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ReportSockets ProtocolRAM Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {w : ℕ}
/-- The old virtual-commodity roles and fixed free-edge roles arrive with
public identifiers. Paid stage sockets already carry a physical group and
port; their native role-code lookup uses that same location. -/
structure Socket where
  positive : Expr
  ordinal : Expr
  group : Expr
  slot : Expr

structure Chart where
  publicBase : ℕ
  roleBase : ℕ
  offBase : ℕ
  publicCount : ℕ
  groups : ℕ
  slots : ℕ

def choose (v : Socket) (yes no : Expr) : Expr := .branch .eq v.positive (.lit 0) no yes

def socketCode (L : Chart) (v : Socket) := choose v
  (RoleROM.expr L.roleBase (L.groups*L.slots) (RoleROM.positiveKey L.offBase L.groups v.group v.slot))
  (RoleROM.expr L.publicBase L.publicCount v.ordinal)

def socketSite (L : Chart) (v : Socket) := choose v
  (SiteROM.siteExpr L.offBase L.groups L.slots v.group v.slot)
  (RoleROM.expr (L.publicBase+L.publicCount) L.publicCount v.ordinal)

def tagged (bin : Bool) (r : Expr) : Expr := .op .add (.op .add r r) (.lit bin.toNat)

def sortedRead (first second : Expr) (right : Bool) (leftValue rightValue : Expr) : Expr :=
  .branch .lt first second (if right then rightValue else leftValue) (if right then leftValue else rightValue)

def field (L : Chart) (slots : Bool→Socket) (reported : Bool) : Fin 4→Expr :=
  let l:=slots false
  let r:=slots true
  let a:=socketSite L l
  let b:=socketSite L r
  let pick := fun s x y=>sortedRead a b s x y
  ![pick false a b,pick true a b,tagged reported (pick false (socketCode L l) (socketCode L r)),
    tagged reported (pick true (socketCode L l) (socketCode L r))]

def volume (L : Chart) (v : Bool→Socket) (out : Bool) :=
  ((List.ofFn (field L v out)).map Expr.work).sum

def passes (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) :=
  columns n base (List.ofFn (field L v out))

def native (w base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) := ProtocolRAM.program w (passes base n L v out)
def ticks (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) := clock (passes base n L v out)

theorem tick_bound (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) :
    ticks base n L v out ≤4+4*(4+n*(2*volume L v out+4)) := by
  simpa only [ticks,passes,List.length_ofFn] using columns_clock n base (volume L v out) (List.ofFn (field L v out))
    (fun e he=>List.le_sum_of_mem (List.mem_map_of_mem he))

theorem cheap (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) : CheapCode (native w base n L v out) := program_cheap w (passes base n L v out)

def state (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) (m : Memory w) := result (passes base n L v out) m

theorem run (base n : ℕ) (L : Chart) (v : Bool→Socket) (out : Bool) (m : Memory w)
    (fit : ∀j,(field L v out j).Fits w base) (room : base+4*n<2^w) :
    (native w base n L v out).Exec m (state base n L v out m) (ticks base n L v out) ∧
    (∀ (j : Fin 4) (i : Fin n),state base n L v out m (base+j.val*n+i.val)=(field L v out j).eval m (i.val:Word w)) ∧
    (∀a,a<base ∨ base+4*n≤a→state base n L v out m a=m a) := by
  let es := List.ofFn (field L v out)
  have safe (e : Expr) (he : e∈es) : e.Fits w base := by obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact fit j
  refine ⟨columns_exec es m (columns_safe es le_rfl safe (by simpa only [es,List.length_ofFn] using room)),?_,?_⟩
  · intro j i
    have idx : j.val<es.length := by simpa only [es,List.length_ofFn] using j.isLt
    have read:=columns_read es m le_rfl safe j.val idx i
    have sel : es[j.val]=field L v out j := List.getElem_ofFn (f:=field L v out) idx
    exact read.trans (congrArg (fun e : Expr=>e.eval m (i.val:Word w)) sel)
  · intro a sep;exact columns_frame es m (by simpa only [es,List.length_ofFn] using sep)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
end

end OAI
