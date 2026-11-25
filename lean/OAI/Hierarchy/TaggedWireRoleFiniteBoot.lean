import OAI.Hierarchy.TaggedWireRoleInventory
import OAI.Hierarchy.ProtocolRAMCatalystChargedSlab

namespace OAI
/-! # Appending the signed directory to the finite original permutation tape -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {h W k attempts H R jobs w : ℕ} (S : PurchaseSampler)
variable (order : Fin R≃Edges S h (2^W) k)
variable (dir : Directory (reserved h W (copies k attempts)) H)

theorem stocks_below (edges start x : ℕ) (raw : Memory w) (low : x< start) :
    mountStocks S order dir edges start raw x=raw x := by
  let z:=shape (R:=R) S dir edges
  have top : start≤z.stop start := by
    dsimp [Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub];omega
  unfold mountStocks
  rw [outside S order dir edges start x _ (.inl low)]
  exact RoleROM.publish_frame _ _ _ raw (.inl (low.trans_le top))

theorem finite_boot {oldSize : ℕ} (V : Fin jobs→Market h (2^W) k) (layout : Boot.Layout V oldSize)
    (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^W)) (edges start : ℕ)
    (origin : ∀i : Fin (2^h),raw i.val=((π i).val:Word (Native.wordBits h (2^W) Native.copies))) (old : oldSize≤ start) :
    let z:=shape (R:=R) S dir edges
    let size:=z.ceiling start
    let words:=mountStocks S order dir edges start raw
    let m:=Boot.booted V size words
    (Native.subdivisionProgram h (2^W)).Exec (Boot.initial V size words) m (Native.subdivisionConstant (2^W)*2^h) ∧
      ∀x,start≤x → x< size → m x=words x := by
  intro z size words m
  have span : start≤ size := by
    dsimp [size,Sizes.ceiling,Sizes.stop,Sizes.offset,Sizes.positive,Sizes.axis,Sizes.ext,Sizes.free,Sizes.pub]
    omega
  have auth (i : Fin (2^h)) : words i.val=((π i).val:Word (Native.wordBits h (2^W) Native.copies)) := by
    have small : i.val< start := i.isLt.trans_le (Boot.root_extent.trans (layout.subdivision.trans old))
    exact (stocks_below S order dir edges start i.val raw small).trans (origin i)
  have started:=Boot.start V (layout.extend (old.trans span)) (Nat.one_le_two_pow) π words auth
  refine ⟨started.1,?_⟩
  intro x lo hi
  exact started.2.high hi (layout.subdivision.trans (old.trans lo))
    (fun i=>(layout.extent i).trans (old.trans lo))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
