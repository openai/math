import OAI.Hierarchy.TaggedWirePaidWork
import OAI.Hierarchy.TaggedWireOriginalSocketExpr

namespace OAI
/-! # Uniform instruction bounds for the complete original signed role expressions -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ReportSockets ProtocolRAM Calendar

private theorem zip_work (f : Expr→Expr→Expr) (a b : Socket) {u v n : ℕ} (left : a.Work u) (right : b.Work v)
    (ok : ∀x y,x.work≤u → y.work≤v → (f x y).work≤n) : (zipSocket f a b).Work n :=
  ⟨ok _ _ left.positive right.positive,ok _ _ left.ordinal right.ordinal,
    ok _ _ left.group right.group,ok _ _ left.slot right.slot⟩

private theorem map_work (f : Expr→Expr) (a : Socket) {u n : ℕ} (input : a.Work u)
    (ok : ∀x,x.work≤u → (f x).work≤n) : (mapSocket f a).Work n :=
  ⟨ok _ input.positive,ok _ input.ordinal,ok _ input.group,ok _ input.slot⟩

private theorem public_work (e : Expr) {n : ℕ} (one : 1≤n) (ok : e.work≤n) : (publicInput e).Work n :=
  ⟨one,ok,one,one⟩

def oldWork (k n core : ℕ) := 8*(2*(4*n+18)+2*n+1)+65+(2*k)*(8*core+1)

theorem normalized_work (L : Chart) (paid : Bool→Socket) {n : ℕ}
    (raw : ∀s,(paid s).Work n) (side : Bool) :
    (normalized L paid side).Work (2*(4*n+18)+2*n+1) := by
  apply zip_work _ _ _ (raw false) (raw true)
  intro x y hx hy
  have a := (socket_work L _ (raw false)).1
  have b := (socket_work L _ (raw true)).1
  cases side <;> simp [sortedRead,Expr.work] <;> omega

theorem original_work (L : Chart) (mb rows ext axis h W k : ℕ) (core : CatalogueRows.CoreSource)
    (paid : Bool→Socket) {n c : ℕ} (raw : ∀s,(paid s).Work n)
    (near : core.left.work≤c) (far : core.right.work≤c) (side : Bool) :
    (originalInputs L mb rows ext axis h W k core paid side).Work (oldWork k n c) := by
  let id:=«meta» mb rows 1
  let K:=2*(4*n+18)+2*n+1
  have wm (j : Fin 7) : («meta» mb rows j).work=7 := rfl
  have normal : (normalized L paid side).Work K := normalized_work L paid raw side
  have buy : (mapSocket (fun e=>e.atRow id) (normalized L paid side)).Work (8*K) := by
    apply map_work _ _ normal
    intro x hx
    have cap := CatalogueRows.substitute_work x id
    change (x.atRow id).work≤x.work*8 at cap
    exact cap.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right 8 hx)
  have payload : (exterior ext h id side).Work 17 := by
    apply public_work _ (by decide)
    cases side
    · change 12≤17;decide
    · change 17≤17;exact le_rfl
  have dir : (altSite core («meta» mb rows (if side then 3 else 2)) side).work≤8*c := by
    let a:=if side then core.right else core.left
    have aw:a.work≤c := by cases side <;> assumption
    have cap:=CatalogueRows.substitute_work a («meta» mb rows (if side then 3 else 2))
    rw [wm] at cap
    exact cap.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 8 aw)
  let axisWork:=14+(2*k)*(8*c+1)
  have alt : (altInput axis (siteLast h (2^W) k+1) k
      (altSite core («meta» mb rows (if side then 3 else 2)) side) («meta» mb rows 4)).Work axisWork := by
    apply public_work _ (by dsimp [axisWork];omega)
    have scaled := Nat.mul_le_mul_left (2*k) (Nat.add_le_add_right dir 1)
    change (scale (2*k) (altSite core («meta» mb rows (if side then 3 else 2)) side)).work+
      («meta» mb rows 4).work+1+5≤axisWork
    rw [scale_work,wm]
    dsimp [axisWork]
    omega
  have reserve : (publicInput («meta» mb rows (if side then 6 else 5))).Work 7 := public_work _ (by decide) (wm _).le
  have branch (tag : ℕ) (x y : Socket) {u v : ℕ} (hx : x.Work u) (hy : y.Work v) :
      (branchSocket («meta» mb rows 0) tag x y).Work (9+u+v) := by
    apply zip_work _ _ _ hx hy
    intro a b ha hb
    change («meta» mb rows 0).work+1+a.work+b.work+1≤_
    rw [wm]
    omega
  have full := branch 0 _ _ buy (branch 1 _ _ payload (branch 2 _ _ alt reserve))
  have cost : 9+8*K+(9+17+(9+axisWork+7))=oldWork k n c := by dsimp [K,axisWork,oldWork];omega
  rw [cost] at full
  exact full

theorem full_original_work (L : Chart) (b : CatalogueRows.Board) {attempts : ℕ}
    (v : BoughtSockets.Directory attempts) (S : PurchaseSampler)
    (mb rows ext axis base freeBase R bits siteBase superBase K G H h W k depth : ℕ) (side : Bool) :
    let core:=CoreCatalogue.source base R bits siteBase superBase K G H k attempts
    let paid:=paidInputs b (coreInputs base freeBase R bits superBase K k attempts) (boughtInputs v S h W k depth K)
    (originalInputs L mb rows ext axis h W k core paid side).Work (oldWork k (paidWidthWork W k attempts) (coreWidthWork k attempts)) := by
  dsimp only
  apply original_work _ _ _ _ _ _ _ _ _ _ (paid_work b v S h W k depth K base freeBase R bits superBase)
  all_goals
    have tot:=CoreCatalogue.source_work base R bits siteBase superBase K G H k attempts
    dsimp only [coreWidthWork]
    omega

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
