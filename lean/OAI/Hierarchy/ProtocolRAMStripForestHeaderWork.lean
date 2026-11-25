import OAI.Hierarchy.ProtocolRAMCalendarStripForestHeader
import OAI.Hierarchy.ProtocolRAMStripTreeFinalWork

namespace OAI
/-! # Instruction count of a strip forest using the installed occurrence header -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open ProbeStage CoreBoard AdaptiveProbe CatalogueRows BoughtSockets StockCommit StripDirectory

private theorem row_work_eq (e : Expr) {i j : Expr} (index : i.work = j.work) :
    (e.atRow i).work = (e.atRow j).work := by
  induction e <;> simp only [Expr.atRow, Expr.work, *]

private theorem choice_work_eq {i j : Expr} (index : i.work = j.work) (n start : ℕ)
    (xs ys : Fin n → Expr) (fields : ∀ a, (xs a).work = (ys a).work) :
    (chooseField n start xs i).work = (chooseField n start ys j).work := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    have tail := ih (start + 1) (fun a => xs a.succ) (fun a => ys a.succ) (fun a => fields a.succ)
    simp only [chooseField, Expr.work, index, fields 0, tail]

private theorem checked_work_eq (b : Board) {x y : Expr} (h : x.work = y.work) :
    (b.checkedEdge x).work = (b.checkedEdge y).work := by
  have index : (Expr.op .sub x (.lit b.coreRows)).work = (Expr.op .sub y (.lit b.coreRows)).work := by
    simp only [Expr.work, h]
  have flag := row_work_eq b.bought.flag index
  simp only [Board.checkedEdge, Expr.work, flag, h]

private def workBound (t : Traversals) (limit : ℕ) : Prop :=
  t.edge.work ≤ limit ∧ t.sourceRow.work ≤ limit ∧
    ∀ mask mate, t.catalystMate = some (mask,mate) → mask.work ≤ limit ∧ mate.work ≤ limit

private def maskAt {n : ℕ} (flags : Fin n → Expr) (H : PortHeader) :=
  chooseField n 0 flags H.fieldTerm

private def mateAt {n : ℕ} (radii : Fin n → Expr) (H : PortHeader) :=
  chooseField n 0 (fun i => (radii i).atRow H.ballTerm) H.fieldTerm

private def walkAt {n : ℕ} (b : Board) (flags radii : Fin n → Expr) (old : Traversals) (H : PortHeader) :=
  b.guardWalk {old with catalystMate := some (maskAt flags H, mateAt radii H)}

private theorem move_work {n : ℕ} (b : Board) (flags radii : Fin n → Expr)
    (old : Traversals) (previous H : PortHeader) (bound : ℕ)
    (prior : workBound (walkAt b flags radii old previous) bound) :
    workBound (walkAt b flags radii old H) bound := by
  obtain ⟨edge, row, mates⟩ := prior
  refine ⟨edge, row, ?_⟩
  intro mask mate eqn
  change some (maskAt flags H, b.checkedEdge (mateAt radii H)) = some (mask,mate) at eqn
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eqn)
  have earlier := mates (maskAt flags previous) (b.checkedEdge (mateAt radii previous)) rfl
  have field : H.fieldTerm.work = previous.fieldTerm.work := rfl
  have ball : H.ballTerm.work = previous.ballTerm.work := rfl
  have maskEq := choice_work_eq field n 0 flags flags (fun _ => rfl)
  have mateEq := choice_work_eq field n 0 (fun i => (radii i).atRow H.ballTerm)
    (fun i => (radii i).atRow previous.ballTerm) (fun i => row_work_eq (radii i) ball)
  exact ⟨maskEq.le.trans earlier.1, (checked_work_eq b mateEq).le.trans earlier.2⟩

variable {z W k q depth : ℕ}
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

set_option cleanup.letToHave false in
set_option maxHeartbeats 1400000 in
/-- Both occurrence-header reads take seven instructions for every installed bank.
The bound covers the located tree and the checked mate at the decoded ball. -/
theorem final_tree_work_at_header (H : PortHeader) (base : ℕ) (a : Attempt)
    (u flags links : ℕ) (one : 1 ≤ u) (flag : b.bought.flag.work ≤ flags)
    (outerLinks : Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount (Stages z (2^W))) k) ≤ links)
    (innerLinks : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount depth) k) ≤ links)
    (ports : DatePortWork (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G u a) :
    let tree := forestAtHeader (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G H
      (originalTree (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G F base a) a
    let bound := finalTreeWork
      (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))) links u flags
    tree.edge.work ≤ bound ∧ tree.sourceRow.work ≤ bound ∧
      ∀ mask mate, tree.catalystMate = some (mask, mate) → mask.work ≤ bound ∧ mate.work ≤ bound := by
  let fields := catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a
  let radii := radiusMate (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G a
  let old := originalTree (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G F base a
  let previous := header F (withPorts (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G) a
  let n := max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))
  exact move_work (n:=n) b fields radii old previous H (finalTreeWork n links u flags)
    (final_tree_work (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth)
      s c b G F base a u flags links one flag outerLinks innerLinks ports)

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
