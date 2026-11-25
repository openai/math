import OAI.Hierarchy.TaggedWireRoleInventory
import OAI.Hierarchy.ProtocolRAMCalendarBootFrame

namespace OAI
/-! # The signed role tables survive the original native subdivision boot -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {h W k attempts H R jobs : ℕ} (S : PurchaseSampler)
variable (order : Fin R≃Edges S h (2^W) k)
variable (dir : Directory (reserved h W (copies k attempts)) H)

/-- The upstream boot publisher may carry its actual price, sampler and
route data below the signed directory. The finite boot tape and the
subdivision receipt then establish all terminal table invariants. -/
theorem from_boot (edges start size : ℕ) (raw words mid : Boot.Tape h (2^W))
    (V : Fin jobs→Market h (2^W) k) (π : Equiv.Perm (Fin (2^h)))
    (receipt : Boot.Receipt V π (Computability.VPVNP.RAMMemory.initialMemory size words) mid)
    (cover : (shape (R:=R) S dir edges).ceiling start≤ size)
    (heap : Native.heapEnd h (2^W) Native.copies≤ start)
    (markets : ∀i,Boot.high (V i)≤ start)
    (advice : ∀u,start≤u → u < (shape (R:=R) S dir edges).ceiling start →
      words u=mountStocks S order dir edges start raw u) :
    let z := shape (R:=R) S dir edges
    (tables S order dir edges).Resident start mid ∧ SiteROM.Resident dir (z.offset start) mid ∧
      StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) (z.stop start) mid := by
  apply retained S order dir edges start raw mid
  intro u lo hi
  have seen := receipt.kept u (heap.trans lo) (fun i hit=>by
    have small := hit.2
    exact (not_lt_of_ge ((markets i).trans lo)) small)
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le cover)] at seen
  exact seen.trans (advice u lo hi)

/-- The same finite tape supplies the signed tables after any mounted prefix
whose actual writes avoid the protected interval. -/
theorem from_prefix {q n : ℕ} (edges start size : ℕ) (raw words mid : Boot.Tape h (2^W))
    (V : Fin jobs→Market h (2^W) k) (π : Equiv.Perm (Fin (2^h)))
    (receipt : Boot.Receipt V π (Computability.VPVNP.RAMMemory.initialMemory size words) mid)
    (C : Calendar.Chart (Native.wordBits h (2^W) Native.copies) q n) (es : List Event) (ran : mounted C es mid)
    (cover : (shape (R:=R) S dir edges).ceiling start≤ size)
    (heap : Native.heapEnd h (2^W) Native.copies≤ start)
    (markets : ∀i,Boot.high (V i)≤ start)
    (safe : ∀u,start≤u → u < (shape (R:=R) S dir edges).ceiling start → ∀e∈es,Calendar.outside C u e)
    (advice : ∀u,start≤u → u < (shape (R:=R) S dir edges).ceiling start →
      words u=mountStocks S order dir edges start raw u) :
    let z := shape (R:=R) S dir edges
    let after := Calendar.run C es mid
    (tables S order dir edges).Resident start after ∧ SiteROM.Resident dir (z.offset start) after ∧
      StockResident (h:=h) (W:=W) (k:=k) (edges:=edges) (z.stop start) after := by
  apply retained S order dir edges start raw (Calendar.run C es mid)
  intro u lo hi
  have seen := receipt.word_after_prefix C es ran u (heap.trans lo) (fun i hit=>
    (not_lt_of_ge ((markets i).trans lo)) hit.2) (safe u lo hi)
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le cover)] at seen
  exact seen.trans (advice u lo hi)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
end

end OAI
