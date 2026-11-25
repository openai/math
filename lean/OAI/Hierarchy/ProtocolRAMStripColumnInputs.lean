import OAI.Hierarchy.ProbeStripDirectoryCore
import OAI.Hierarchy.ProtocolRAMReportGroupROM

namespace OAI
/-! # Stored column inputs and the public purchase directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen Calendar
open scoped Classical Fin.CommRing
variable {z d k w attempts : ℕ}

structure Inputs where
  group : Expr
  port : Expr
  tag : Expr

def readTile (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (j : Fin (depth+1)) :=
  StripDirectory.tile (sh.L S depth i).source (paths z S.degree depth) j.val

/-- A two-word quotient/remainder header dispatches among public expressions.
It never stores an input-dependent tile, live candidate, or endpoint. -/
def select (header : Calendar.StockCommit.PortHeader) {n : ℕ} (terms : Fin n→Expr) : Expr :=
  chooseField n 0 (fun i=>(terms i).atRow header.fieldTerm) header.ballTerm

theorem select_read (header : Calendar.StockCommit.PortHeader) {n : ℕ} (terms : Fin n→Expr)
    (m : Memory w) (r row : Word w) (i : Fin n) (room : n≤2^w) (key : (header.ballTerm.eval m r).val=i.val)
    (localRow : header.fieldTerm.eval m r=row) : (select header terms).eval m r=(terms i).eval m row := by
  calc
    _ = ((terms i).atRow header.fieldTerm).eval m r :=
      eval_chooseField n 0 (fun j : Fin n => (terms j).atRow header.fieldTerm)
        header.ballTerm m r i (by simpa using room) (by simpa using key)
    _ = _ := by rw [eval_atRow,localRow]

/-- Public addresses used by all candidates. An event-specific flag and menu
address is the original permanent report produced by that calendar event. -/
structure Directory (attempts : ℕ) where
  outerBase : ℕ
  keysBase : ℕ
  remapBase : ℕ
  superBase : ℕ
  sitesBase : ℕ
  shelf : Fin attempts→Shelf
  flagBase : Fin attempts→ℕ
  menuBase : Fin attempts→ℕ

def Directory.header (v : Directory attempts) (z d k D depth : ℕ) : StockCommit.PortHeader :=
  ⟨v.outerBase,attempts,count z d k*paths z D depth⟩

end Hierarchy.ProtocolRAM.BoughtSockets

end

end OAI
