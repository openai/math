import OAI.Hierarchy.ProbeStripPortDestination
import OAI.Hierarchy.ProtocolRAMStockCommitPortSources
import OAI.Hierarchy.ProtocolRAMRepairScatter

namespace OAI
/-! # Extracting the commodity account of a physical accepted occurrence -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.StockCommit
open scoped Fin.CommRing Classical
noncomputable section
variable {w q : ℕ}

/-- The occurrence column carries the decoded local stock address, or the genuine
sink word in its absence. The hardware clamps both out-of-range values to the
same sink. Any occurrence assigned to an actual commodity has a unique enabled
slot and the physical index in the recorded row is that commodity's index. -/
theorem fresh_kind_iff (h : PortHeader) (start goods limit : ℕ) (old reserve half price : Bank) (mode : Expr)
    (slot : Fin h.ports→Option Expr) (b : Batch q h.ports) (tabs : Fin h.ports→Fin q→Expr)
    (mem : Memory w) (loaded : h.Loaded mem) (portFit : h.ports≤2^w) (fit : start+goods<2^w)
    (j : Fin h.rows) (v : Fin h.ports) (i : Fin goods) :
    let slotExpr := destination h goods slot
    let c := fresh (h.area start goods limit) (h.sources old reserve half price mode slotExpr b tabs)
    RepairHistogram.kind c.plan.bank c.columns mem (h.enum ⟨j,v⟩)=some i ↔
      ∃ addr,slot v=some addr ∧ (addr.eval mem (j.val:Word w)).val=i.val := by
  intro slotExpr c
  let e := h.enum ⟨j,v⟩
  have field : (h.fieldTerm.eval mem (e.val:Word w)).val=v.val := by
    have id := loaded.second e
    change h.fieldTerm.eval mem (e.val:Word w)=(((h.enum.symm e).2.val:ℕ):Word w) at id
    rw [id]
    change (((h.enum.symm (h.enum ⟨j,v⟩)).2.val:Word w)).val=v.val
    rw [Equiv.symm_apply_apply,Fin.val_cast_of_lt (v.isLt.trans_le portFit)]
  have row : h.ballTerm.eval mem (e.val:Word w)=(j.val:Word w) := by
    have id := loaded.first e
    change h.ballTerm.eval mem (e.val:Word w)=(((h.enum.symm e).1.val:ℕ):Word w) at id
    rw [id]
    change (((h.enum.symm (h.enum ⟨j,v⟩)).1.val:ℕ):Word w)=(j.val:Word w)
    rw [Equiv.symm_apply_apply]
  rw [RepairHistogram.kind_iff]
  change ((RepairHistogram.destination start goods slotExpr).eval mem (e.val:Word w)).val=start+i.val ↔ _
  rw [RepairHistogram.destination_val _ _ _ _ _ fit, destination_read h goods slot mem _ v portFit field,row]
  cases status : slot v with
  | none =>
    have width : goods<2^w := by omega
    simp [Expr.eval,Fin.val_cast_of_lt width,i.isLt.ne']
  | some addr =>
    simp only [Option.getD_some,Option.some.injEq,exists_eq_left',Nat.add_left_cancel_iff]
    have lim := i.isLt
    omega

/-- The `PortPlan.funded` address condition for an ordinary slot. The actual
stock registers come from the authoritative bank at exactly the index decoded by
the commit. This equality never inspects a cash slot. -/
theorem fresh_stock_position (h : PortHeader) (start goods limit : ℕ) (old reserve half price : Bank) (mode : Expr)
    (slot : Fin h.ports→Option Expr) (b : Batch q h.ports) (tabs : Fin h.ports→Fin q→Expr)
    (mem : Memory w) (loaded : h.Loaded mem) (portFit : h.ports≤2^w) (fit : start+goods<2^w)
    (j : Fin h.rows) (v : Fin h.ports) (i : Fin goods)
    (stock : ∀ addr,slot v=some addr → b.stock v=.lookup old addr)
    (seed : old.read mem (i.val:Word w)=mem (start+i.val)) :
    let c := fresh (h.area start goods limit) (h.sources old reserve half price mode (destination h goods slot) b tabs)
    RepairHistogram.kind c.plan.bank c.columns mem (h.enum ⟨j,v⟩)=some i →
      ((b.stock v).eval mem (j.val:Word w)).val=(mem (start+i.val)).val := by
  intro c hit
  obtain ⟨addr,active,read⟩ := (fresh_kind_iff h start goods limit old reserve half price mode slot b tabs mem loaded portFit fit j v i).mp hit
  rw [stock addr active]
  change (old.read mem (addr.eval mem (j.val:Word w))).val=(mem (start+i.val)).val
  have word : addr.eval mem (j.val:Word w)=(i.val:Word w) := Fin.ext (read.trans (Fin.val_cast_of_lt (i.isLt.trans (by omega : goods<2^w))).symm)
  rw [word,seed]

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
