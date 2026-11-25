import OAI.Hierarchy.TaggedWireSocketWork
import OAI.Hierarchy.TaggedWirePaidOperands
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Native paid and purchased socket costs, uniform in the permutation height -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets ProtocolRAM Calendar

def coreWidthWork (k attempts : ℕ) := 246+26*copies k attempts

private theorem operands_work (base G H : ℕ) (g s : Expr) {n : ℕ}
    (ok : (SiteROM.siteExpr base G H g s).work≤n) : g.work≤n ∧ s.work≤n := by
  dsimp [SiteROM.siteExpr,Expr.work] at ok
  omega

theorem core_work (base freeBase R bits superBase K k attempts : ℕ) (side : Bool) :
    (coreInputs base freeBase R bits superBase K k attempts side).Work (coreWidthWork k attempts) := by
  let c:=CoreCatalogue.source base R bits 0 superBase K 0 0 k attempts
  let C:=coreWidthWork k attempts
  have total : c.group.work+c.left.work+c.right.work+c.lengthCode.work+c.menu.work=C :=
    CoreCatalogue.source_work base R bits 0 superBase K 0 0 k attempts
  have near : c.left.work≤C := by omega
  have far : c.right.work≤C := by omega
  have seven : 7≤C := by dsimp [C,coreWidthWork];omega
  let box (port tag : Fin 10) := SiteROM.atPort 0 0 0 superBase K (copies k attempts)
    (CoreCatalogue.globalGroup base R bits) (CoreCatalogue.pointed base R bits port) (CoreCatalogue.field base R tag)
  cases side
  · have half : (box 4 7).work≤C := by
      change (CoreCatalogue.field base R 0).work+1+(CoreCatalogue.field base R 1).work+(box 4 7).work+1≤C at near
      omega
    have seen:=operands_work _ _ _ _ _ half
    exact ⟨seven,seven,seen.1,seen.2⟩
  · have half : (box 5 8).work≤C := by
      change (CoreCatalogue.field base R 0).work+1+(CoreCatalogue.field base R 2).work+(box 5 8).work+1≤C at far
      omega
    have seen:=operands_work _ _ _ _ _ half
    exact ⟨seven,seven,seen.1,seen.2⟩

theorem bought_work {attempts : ℕ} (v : BoughtSockets.Directory attempts) (S : PurchaseSampler)
    (h W k depth K : ℕ) (side : Bool) :
    (boughtInputs v S h W k depth K side).Work (BoughtSockets.wordWork (2^W) k attempts) := by
  have all:=v.source_work S h W k depth K 0 0
  have one : 1≤BoughtSockets.wordWork (2^W) k attempts := by
    change 1 ≤ 50 + _
    exact (by decide : 1 ≤ 50).trans (Nat.le_add_right ..)
  cases side
  · have seen:=operands_work _ _ _ _ _ all.2.1
    exact ⟨one,one,seen.1,seen.2⟩
  · have seen:=operands_work _ _ _ _ _ all.2.2.1
    exact ⟨one,one,seen.1,seen.2⟩

def paidWidthWork (W k attempts : ℕ) := coreWidthWork k attempts+5*BoughtSockets.wordWork (2^W) k attempts+4

theorem paid_work (b : CatalogueRows.Board) {attempts : ℕ} (v : BoughtSockets.Directory attempts)
    (S : PurchaseSampler) (h W k depth K base freeBase R bits superBase : ℕ) (side : Bool) :
    (paidInputs b (coreInputs base freeBase R bits superBase K k attempts)
      (boughtInputs v S h W k depth K) side).Work (paidWidthWork W k attempts) := by
  have c := core_work base freeBase R bits superBase K k attempts side
  have p := bought_work v S h W k depth K side
  have choose {x y : Expr} (hx : x.work≤coreWidthWork k attempts) (hy : y.work≤BoughtSockets.wordWork (2^W) k attempts) :
      (b.select x y).work≤paidWidthWork W k attempts :=
    (b.select_work x y).trans (Nat.add_le_add_right (Nat.add_le_add hx (Nat.mul_le_mul_left _ hy)) 4)
  exact ⟨choose c.positive p.positive,choose c.ordinal p.ordinal,choose c.group p.group,choose c.slot p.slot⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
