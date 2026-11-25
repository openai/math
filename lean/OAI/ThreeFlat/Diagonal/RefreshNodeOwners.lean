import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.Diagonal.RefreshOwnership

namespace OAI
/-! # Child and parent arrays for the refreshing stage's coordinate transpose -/

namespace ThreeFlat.Diagonal.RefreshNodeOwners

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalPinsExpr RAM.PhysicalProcedure
variable {W : ℕ}

def field (current off : ℕ) : Formula 1 := .load (.op .add (.load (.lit current)) (.lit off))

/-- Old lanes encode the consumed port in the low digit. The resulting base appends the
port in row-major order and the remaining lane becomes the low digit of each new site. -/
def expr (current m : ℕ) (outChild : Bool) : Formula 1 :=
  let f := field current
  if outChild then
    .op .add (f 6) (RefreshOwnership.childExpr m (f 8) (.cut (.reg 0) (f 42)))
  else RefreshOwnership.ownerExpr m (f 8) (.cut (.reg 0) (f 44))

def procedure (current : Word W) (m : ℕ) : Procedure W :=
  (HeaderScan.procedure current 42 43 (HeaderScan.closed (expr current.val m true))).seq
    (HeaderScan.procedure current 44 45 (HeaderScan.closed (expr current.val m false)))

theorem expr_child (current m : ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ) :
    (expr current m true).natural W (fun _ => 0) mem vs =
      mem (mem current+6)+RefreshOwnership.child m (mem (mem current+8)) (vs 0-mem (mem current+42)) := rfl

theorem expr_owner (current m : ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ) :
    (expr current m false).natural W (fun _ => 0) mem vs =
      RefreshOwnership.owner m (mem (mem current+8)) (vs 0-mem (mem current+44)) := rfl

end ThreeFlat.Diagonal.RefreshNodeOwners

end OAI
