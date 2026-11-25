import OAI.Hierarchy.ProbeFixedPrintedRole

namespace OAI
/-! # The original finite role selected by each physical debit operand -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StockCommit PortPadding CatalogueRows StripChart StripDirectory
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

variable {w n D : ℕ}

theorem PortPadding.real_hit (v : Fin n→Expr) (b : Board) (room : b.rows<2^w)
    (m : Memory w) (r : Word w) (j : Fin D) (e : Fin b.rows)
    (hit : ((extend v (.lit b.rows) j).eval m r).val=e.val) :
    ∃u,((v u).eval m r).val=e.val := by
  by_cases small : j.val<n
  · refine ⟨⟨_,small⟩,?_⟩
    simpa [extend,small,Fin.val_cast_of_lt (e.isLt.trans room)] using hit
  · rw [extend_tail _ _ _ (Nat.le_of_not_gt small)] at hit
    have bad : b.rows=e.val := by simpa [Expr.eval,Fin.val_cast_of_lt room] using hit
    exact False.elim ((Nat.ne_of_lt e.isLt) bad.symm)

theorem CatalogueRows.Board.raw_of_guard (b : Board) (keep raw : Expr) (m : Memory w) (r : Word w)
    (room : b.rows<2^w) (e : Fin b.rows)
    (hit : ((physicalEdge b keep raw).eval m r).val=e.val) : (raw.eval m r).val=e.val := by
  rw [physicalEdge_val b keep raw m r room] at hit
  split_ifs at hit <;> omega

theorem CatalogueRows.Board.raw_of_checked (b : Board) (raw : Expr) (m : Memory w) (r : Word w)
    (room : b.rows<2^w) (e : Fin b.rows)
    (hit : ((b.checkedEdge raw).eval m r).val=e.val) : (raw.eval m r).val=e.val := by
  rw [b.checkedEdge_val raw m r room] at hit
  split_ifs at hit <;> omega

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
set_option quotPrecheck false
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "ports" => max n₀ n₁
local notation "bs" => v.nativeBoards P z width
local notation "cat" => P.catalogue
local notation "H" => StripChart.header F bs

theorem role_reads (a : Attempt) (row : Fin (H a).rows) (j : Fin ports) (m : Memory W)
    (h : (H a).Loaded m) (size : ports≤2^W) :
    let u:=v.roleOccurrence P z width a row j
    ((H a).fieldTerm.eval m (u.val:Word W)).val=j.val ∧
      (H a).ballTerm.eval m (u.val:Word W)=(row.val:Word W) := by
  intro u
  let i:=(H a).enum ⟨row,j⟩
  have pos : u.val=i.val:=rfl
  rw [pos]
  have role:=h.second i
  have ball:=h.first i
  change (H a).fieldTerm.eval m (i.val:Word W)=(((H a).enum.symm i).2.val:Word W) at role
  change (H a).ballTerm.eval m (i.val:Word W)=(((H a).enum.symm i).1.val:Word W) at ball
  rw [show (H a).enum.symm i=⟨row,j⟩ from (H a).enum.symm_apply_apply _] at role ball
  exact ⟨(congrArg Fin.val role).trans (Fin.val_cast_of_lt (j.isLt.trans_le size)),ball⟩

/-- Remove exactly the printed ID prefix and the retention guard. At a real
physical row neither of the guards can manufacture a successful role. -/
theorem original_direct (a : Attempt) (row : Fin (H a).rows) (j : Fin ports) (m : Memory W)
    (h : (H a).Loaded m) (size : ports≤2^W) (room : (cat).rows<2^W) (e : Fin (cat).rows) :
    let u:=v.roleOccurrence P z width a row j
    let pf:=v.nativeFormats P z width a
    let g:=LabelSource.fromPorts pf.labelStart (cat).idBase (cat).geometry (H a).fieldTerm (StripChart.id F bs cat a)
    (g.edge.eval m (u.val:Word W)).val=e.val →
      ((rawEdge bs (cat).rows a j).eval m (row.val:Word W)).val=e.val := by
  intro u pf g hit
  obtain ⟨role,ball⟩:=v.role_reads P z width a row j m h size
  have cancel : g.edge.eval m (u.val:Word W)=
      (physicalEdge cat (retainedAt F bs a) (StripChart.edge F bs (cat).rows a j)).eval m (u.val:Word W) := by
    change (chooseField ports 0 (StripChart.id F bs cat a) (H a).fieldTerm).eval m (u.val:Word W)-((cat).idBase:Word W)=_
    rw [eval_chooseField _ _ _ _ _ _ j (by simpa using size) (by simpa using role)]
    change (P.catalogue.idBase:Word W)+_-(P.catalogue.idBase:Word W)=_
    abel
  rw [cancel] at hit
  have real:=P.catalogue.raw_of_guard _ _ m _ room e hit
  have actualBall : (H a).ballTerm.eval m (u.val : Word W) = (row.val : Word W) := ball
  rw [←actualBall]
  simpa only [StripChart.edge,eval_atRow] using real

/-- The second-radius read uses the same true stock header, and the
terminal bought-flag check can only discard an operand. -/
theorem original_mate (a : Attempt) (row : Fin (H a).rows) (j : Fin ports) (m : Memory W)
    (h : (H a).Loaded m) (size : ports≤2^W) (room : (cat).rows<2^W) (e : Fin (cat).rows)
    (mate : Fin ports→Expr) :
    let u:=v.roleOccurrence P z width a row j
    let packed:=chooseField ports 0 (fun t=>(mate t).atRow (H a).ballTerm) (H a).fieldTerm
    (((cat).checkedEdge packed).eval m (u.val:Word W)).val=e.val →
      ((mate j).eval m (row.val:Word W)).val=e.val := by
  intro u packed hit
  obtain ⟨role,ball⟩:=v.role_reads P z width a row j m h size
  have unguard:=P.catalogue.raw_of_checked packed m _ room e hit
  change ((chooseField ports 0 _ _).eval m (u.val:Word W)).val=e.val at unguard
  rw [eval_chooseField _ _ _ _ _ _ j (by simpa using size) (by simpa using role),eval_atRow,ball] at unguard
  exact unguard

/-- The actual second operand saved by this format, prior to testing the
occurrence's catalyst flag. Its field expression is independent of later
reserve updates. -/
def paidMatePorts (a : Attempt) :=
  StripChart.radiusMate (v.located (v.seed P z width) P width) v.mesh P.catalogue P.routes a

theorem forest_second (a : Attempt) (mask mate : Expr)
    (receipt : (v.nativeTrees P z width a).catalystMate=some (mask,mate)) :
    mate=P.catalogue.checkedEdge (chooseField ports 0
      (fun j=>((v.paidMatePorts P z width a j).atRow (H a).ballTerm)) (H a).fieldTerm) := by
  cases a <;> exact (congrArg Prod.snd (Option.some.inj receipt)).symm

theorem payload_roles (phase trial : ℕ) (j : Fin ports) (m : Memory W) (r : Word W)
    (room : (cat).rows<2^W) (e : Fin (cat).rows) :
    (((rawEdge bs (cat).rows (.outer phase trial) j).eval m r).val=e.val →
      ∃v₀ : PayloadRole N k,(((v.payloadPricePorts P z width).primary cat v₀).eval m r).val=e.val) ∧
    (((v.paidMatePorts P z width (.outer phase trial) j).eval m r).val=e.val →
      ∃v₀ : PayloadRole N k,(((v.payloadPricePorts P z width).mate cat v₀).eval m r).val=e.val) := by
  constructor
  · intro hit
    obtain ⟨i,res⟩:=PortPadding.real_hit (fun i : Fin n₀=>(v.payloadPricePorts P z width).primary cat
      ((Fintype.equivFin (PayloadRole N k)).symm i)) cat room m r j e hit
    exact ⟨_,res⟩
  · intro hit
    obtain ⟨i,res⟩:=PortPadding.real_hit (fun i : Fin n₀=>(v.payloadPricePorts P z width).mate cat
      ((Fintype.equivFin (PayloadRole N k)).symm i)) cat room m r j e hit
    exact ⟨_,res⟩

theorem purchased_roles (phase trial tick step : ℕ) (j : Fin ports) (m : Memory W) (r : Word W)
    (room : (cat).rows<2^W) (e : Fin (cat).rows) :
    (((rawEdge bs (cat).rows (.inner phase trial tick step) j).eval m r).val=e.val →
      ∃v₀ : PurchasedRole v.depth k,(((v.purchasedPricePorts P z width phase trial).primary cat v₀).eval m r).val=e.val) ∧
    (((v.paidMatePorts P z width (.inner phase trial tick step) j).eval m r).val=e.val →
      ∃v₀ : PurchasedRole v.depth k,(((v.purchasedPricePorts P z width phase trial).mate cat v₀).eval m r).val=e.val) := by
  constructor
  · intro hit
    obtain ⟨i,res⟩:=PortPadding.real_hit (fun i : Fin n₁=>(v.purchasedPricePorts P z width phase trial).primary cat
      ((Fintype.equivFin (PurchasedRole v.depth k)).symm i)) cat room m r j e hit
    exact ⟨_,res⟩
  · intro hit
    obtain ⟨i,res⟩:=PortPadding.real_hit (fun i : Fin n₁=>(v.purchasedPricePorts P z width phase trial).mate cat
      ((Fintype.equivFin (PurchasedRole v.depth k)).symm i)) cat room m r j e hit
    exact ⟨_,res⟩

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
