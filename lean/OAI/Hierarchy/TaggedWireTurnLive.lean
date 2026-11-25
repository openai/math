import OAI.Hierarchy.TaggedWireOldBoardNative
import OAI.Hierarchy.TaggedWireRoleSemantics

namespace OAI
/-! # The eleven actual turn banks, including dormant source rows -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.Board
open AdaptiveProbe ReportSockets ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h W k attempts w : ℕ} (S : PurchaseSampler) (b : Board) (g : Inventory)
local notation "P" => Public S h W k attempts

private theorem bank_at (start n : ℕ) (m : Memory w) (i : Fin n) (fit : n≤2^w) :
    (RoleROM.bank start n).read m (i.val:Word w)=m (start+i.val) := by
  change m (start+(i.val:Word w).val%(RoleROM.bank start n).size)=_
  rw [Fin.val_cast_of_lt (i.isLt.trans_le fit)]
  change m (start+i.val%ProtocolRAMPurchaseSampler.span n)=_
  rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span n))]

structure LiveReads (old : Fin b.old→ℕ) (out : Fin b.edges→ℕ)
    (before : ∀i,0<old i→Bool→P) (after : ∀j,0<out j→Bool→P) (mem : Memory w) : Prop where
  width : ∀i,((b.widthBank).read mem (i.val:Word w)).val=old i
  rawSite : ∀i (hi : 0<old i) s,(b.forwardSite s).read mem (i.val:Word w)=((name (site S (before i hi s))).val:Word w)
  oldSite : ∀i (hi : 0<old i) s,(b.oldSite s).read mem (i.val:Word w)=actual S false (before i hi) s true
  oldRole : ∀i (hi : 0<old i) s,(b.oldRole s).read mem (i.val:Word w)=actual S false (before i hi) s false
  newSite : ∀i (hi : 0<out i) s,(b.newSite s).read mem (i.val:Word w)=actual S true (after i hi) s true
  newRole : ∀i (hi : 0<out i) s,(b.newRole s).read mem (i.val:Word w)=actual S true (after i hi) s false

theorem LiveReads.frame {old : Fin b.old→ℕ} {out : Fin b.edges→ℕ}
    {before : ∀i,0<old i→Bool→P} {after : ∀j,0<out j→Bool→P} {m m' : Memory w}
    (r : LiveReads S b old out before after m) (floor : ℕ) (endAt : b.endAt+3*b.old≤floor)
    (o : b.old≤2^w) (n : b.edges≤2^w) (kept : ∀x,x<floor→m' x=m x) : LiveReads S b old out before after m' := by
  have read (a len : ℕ) (room : len≤2^w) (bound : a+len≤floor) (i : Fin len) :
      (RoleROM.bank a len).read m' (i.val:Word w)=(RoleROM.bank a len).read m (i.val:Word w) := by
    rw [bank_at _ _ _ _ room,bank_at _ _ _ _ room]
    exact kept _ ((Nat.add_lt_add_left i.isLt a).trans_le bound)
  have addr := endAt
  unfold Board.endAt Board.newBase at addr
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [widthBank,read _ _ o (by unfold Board.endAt Board.newBase;omega)]
    exact r.width i
  · intro i hi s
    rw [forwardSite,read _ _ o (by cases s <;> simp [Board.endAt,Board.newBase,Bool.toNat] <;> omega)]
    exact r.rawSite i hi s
  · intro i hi s
    rw [Board.oldSite,read _ _ o (by cases s <;> simp [Bool.toNat] <;> omega)]
    exact r.oldSite i hi s
  · intro i hi s
    rw [Board.oldRole,read _ _ o (by cases s <;> simp [Bool.toNat] <;> omega)]
    exact r.oldRole i hi s
  · intro i hi s
    rw [Board.newSite,read _ _ n (by cases s <;> simp [Board.newBase,Bool.toNat] <;> omega)]
    exact r.newSite i hi s
  · intro i hi s
    rw [Board.newRole,read _ _ n (by cases s <;> simp [Board.newBase,Bool.toNat] <;> omega)]
    exact r.newRole i hi s

theorem extended_live (m : Memory w) (ok : b.Ready w) (fit : ∀j,(b.rawFields g j).Fits w b.base)
    (room : b.endAt+3*b.old<2^w) (sites : siteLast h (2^W) k+1≤2^w)
    (old : Fin b.old→ℕ) (out : Fin b.edges→ℕ)
    (before : ∀i,0<old i→Bool→P) (after : ∀j,0<out j→Bool→P)
    (values : ∀i : Fin b.old,(g.width.eval m (i.val:Word w)).val=old i)
    (oldResolved : ∀i hi s,Resolved S b.chart (b.before s) m (i.val:Word w) (before i hi s))
    (newResolved : ∀i hi s,Resolved S b.chart (b.finish s) m (i.val:Word w) (after i hi s)) :
    (b.extended g w).Exec m (b.extendedState g m) (b.extendedTime g) ∧
      LiveReads S b old out before after (b.extendedState g m) := by
  have emit:=b.extended_exec g m ok fit room
  have base:=b.output m ok
  have small:=ok.room
  unfold endAt newBase at small
  have o:b.old≤2^w:=by omega
  have n:b.edges≤2^w:=by omega
  have oldAt (j : Fin 4) (i : Fin b.old) :
      (RoleROM.bank (b.base+j.val*b.old) b.old).read (b.extendedState g m) (i.val:Word w)=
        (field b.chart b.before false j).eval m (i.val:Word w) := by
    rw [bank_at _ _ _ _ o, emit.2.2 _ (by
      unfold endAt newBase
      have h:=Nat.mul_le_mul_right b.old (show j.val+1≤4 from j.isLt)
      rw [Nat.succ_mul] at h
      have hi:=i.isLt
      omega)]
    exact base.2.1 _ _
  have newAt (j : Fin 4) (i : Fin b.edges) :
      (RoleROM.bank (b.newBase+j.val*b.edges) b.edges).read (b.extendedState g m) (i.val:Word w)=
        (field b.chart b.finish true j).eval m (i.val:Word w) := by
    rw [bank_at _ _ _ _ n,emit.2.2 _ (by
      unfold endAt
      have h:=Nat.mul_le_mul_right b.edges (show j.val+1≤4 from j.isLt)
      rw [Nat.succ_mul] at h
      have hi:=i.isLt
      omega)]
    exact base.2.2.1 _ _
  have forward (j : Fin 3) (i : Fin b.old) :
      (RoleROM.bank (b.endAt+j.val*b.old) b.old).read (b.extendedState g m) (i.val:Word w)=
        (b.rawFields g j).eval m (i.val:Word w) := (bank_at _ _ _ _ o).trans (emit.2.1 j i)
  refine ⟨emit.1,⟨fun i=>(congrArg Fin.val (forward 2 i)).trans (values i),?_,?_,?_,?_,?_⟩⟩
  · intro i hi s
    cases s with
    | false=>exact (forward 0 i).trans (oldResolved i hi false).1
    | true=>exact (forward 1 i).trans (oldResolved i hi true).1
  · intro i hi s
    have got:=fields S b.chart m (i.val:Word w) b.before (before i hi) false (oldResolved i hi) sites
    cases s with
    | false=>exact (oldAt 0 i).trans got.1
    | true=>exact (oldAt 1 i).trans got.2.1
  · intro i hi s
    have got:=fields S b.chart m (i.val:Word w) b.before (before i hi) false (oldResolved i hi) sites
    cases s with
    | false=>exact (oldAt 2 i).trans got.2.2.1
    | true=>exact (oldAt 3 i).trans got.2.2.2
  · intro i hi s
    have got:=fields S b.chart m (i.val:Word w) b.finish (after i hi) true (newResolved i hi) sites
    cases s with
    | false=>exact (newAt 0 i).trans got.1
    | true=>exact (newAt 1 i).trans got.2.1
  · intro i hi s
    have got:=fields S b.chart m (i.val:Word w) b.finish (after i hi) true (newResolved i hi) sites
    cases s with
    | false=>exact (newAt 2 i).trans got.2.2.1
    | true=>exact (newAt 3 i).trans got.2.2.2

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.Board

end
end OAI
