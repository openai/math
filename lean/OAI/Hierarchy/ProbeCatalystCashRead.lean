import OAI.Hierarchy.ProbeCatalystArchiveRows
import OAI.Hierarchy.ProtocolRAMStockPortPlan
import OAI.Hierarchy.ProbeColumnAccounts
import OAI.Hierarchy.ProtocolRAMLocalCharge
import OAI.Hierarchy.ProbeCatalystProvision
import OAI.Hierarchy.ProtocolRAMPortPadding

namespace OAI
/-! # Native committed-packet reads for the external catalyst archive -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit RepairHistogram
open scoped BigOperators Classical Fin.CommRing

variable {A B C H G R : Type*} {k D q balls w payload K : ℕ}
  [Fintype A] [Fintype C] [Fintype H] [Fintype B]

omit [Fintype H] [Fintype B] in
/-- A catalyst demand occurs once in the local packet. Ordinary demands may
use repeated addresses. Both radius hops serve the same external demand. -/
theorem catalyst_need (ordinary : A→B) (bits : ℕ) (c : C) (axis : Fin k) :
    debited (demand (I:=C) (H:=H) ordinary) bits (.catalyst c axis)=bits := by
  classical
  simp [debited,Fintype.sum_sum_type,Fintype.sum_prod_type,demand]
  rw [Finset.sum_eq_single c]
  · simp
  · intro j _ different
    simp [different]
  · simp

def released : Role C H B k→ℕ→ℕ
  | .catalyst ..,bits => bits
  | _,_ => 0

omit [Fintype H] [Fintype B] in
/-- The actual signed cash column and catalyst projection agree on every
primitive port. Ordinary demand goes to stock. No non-catalyst cash port is demanded. -/
theorem cash_demand {I : Type*} (address : A→I) (bits : ℕ) (v : Role C H (A⊕B) k) :
    (if account address v=none then
      debited (demand (Sum.inl (α:=A) (β:=B))) bits v else 0)=released v bits := by
  classical
  cases v with
  | catalyst c j => simpa [account,released] using catalyst_need (H:=H) (Sum.inl (α:=A) (β:=B)) bits c j
  | radius c j s => simp [account,released,debited,demand,Fintype.sum_sum_type]
  | cross c a s t => simp [account,released,debited,demand,Fintype.sum_sum_type]
  | horizontal e l => simp [account,released,debited,demand,Fintype.sum_sum_type]
  | extra e => cases e <;> simp [account,released,debited,demand,Fintype.sum_sum_type]

variable {s : StockCommit} {m : Memory w}

variable {b : Batch q D} {count : ℕ}

def cashWord (layout : PortPlan s b m balls) (cell : Fin balls × Fin D) :=
  let e := layout.enum ⟨cell.1,cell.2⟩
  if RepairHistogram.kind (goods:=s.goods) s.plan.bank s.columns m e=none then
    consumedBits s.columns m e else 0

/-- A positive archived debit is on the original row and catalyst role.
The native flag selects actual balls, and every other true role has the
signed cash value computed by `cash_demand`. Padding contributes zero. -/
theorem positive_cell (layout : PortPlan s b m balls) (ballsAt : R ↪ Fin balls)
    (bound : Fintype.card (Role C H B k)≤D)
    (live : ∀j,j∈liveRows b m balls → ∃r,ballsAt r=j)
    (width : Fin balls→ℕ)
    (realRead : ∀ j,j∈liveRows b m balls → ∀v : Role C H B k,
      cashWord layout (j,PortPadding.inject bound (Fintype.equivFin _ v))=released v (width j))
    (pad : ∀(j : Fin balls) (i : Fin D),Fintype.card (Role C H B k) ≤ i.val → cashWord layout (j,i)=0)
    (cell : Fin balls × Fin D) (pos : 0<cashWord layout cell) :
    ∃z,portCell ballsAt bound z=cell := by
  obtain ⟨j,i⟩ := cell
  have entered : j∈liveRows b m balls := by
    by_contra off
    have zero := (layout.off (layout.enum ⟨j,i⟩) (by simpa only [Equiv.symm_apply_apply] using off)).2
    simp [cashWord,zero] at pos
  obtain ⟨r,hr⟩ := live j entered
  by_cases hi : i.val<Fintype.card (Role C H B k)
  · let ix : Fin (Fintype.card (Role C H B k)) := ⟨i.val,hi⟩
    let v := (Fintype.equivFin (Role C H B k)).symm ix
    have code : PortPadding.inject bound (Fintype.equivFin _ v)=i := by
      apply Fin.ext
      simp [v,ix,PortPadding.inject]
    have actual := realRead j entered v
    rw [code] at actual
    have nz := pos.trans_le actual.le
    cases hv : v with
    | catalyst c axis =>
      refine ⟨(r,c,axis),Prod.ext hr ?_⟩
      rw [←code]
      exact congrArg (fun x=>PortPadding.inject bound (Fintype.equivFin _ x)) hv.symm
    | radius | cross | horizontal | extra => simp [hv,released] at nz
  · rw [pad j i (Nat.le_of_not_gt hi)] at pos
    omega

/-- Form a chronological event directly from the signed commit's observed
consumed-bit words. Off-mask balls read zero through the actual program. -/
def readEntry (layout : PortPlan s b m balls) (ballsAt : R ↪ Fin balls)
    (bound : Fintype.card (Role C H B k)≤D) (columns : R × C ↪ G)
    (keys : G × Fin k ↪ Fin count) (idle : Fin count) (positive : 0<K) (width : R→ℕ)
    (copies : ∀ r,b.copies≤copied K (width r) payload)
    (packet : ∀ r,ballsAt r∈liveRows b m balls → ∀c axis,
      cashWord layout (ballsAt r,catalystPort bound (c,axis))≤b.copies*width r) :
    Entry count payload := by
  apply repairEntry ballsAt bound columns keys idle (cashWord layout)
  rintro ⟨r,c,j⟩
  by_cases live : ballsAt r ∈ liveRows b m balls
  · exact (packet r live c j).trans (catalyst_bits_le positive (copies r))
  · have off := layout.off (layout.enum ⟨ballsAt r,catalystPort bound (c,j)⟩) (by simpa only [Equiv.symm_apply_apply] using live)
    simp [portCell,cashWord,off.2]

/-- The heterogeneous physical program itself emits zero in every unused
role beyond the true port bound, even when the real packet commits. -/
theorem padded_debit_zero {_a n : ℕ} (raw : Batch q n) (mem : Memory w) (row : Word w)
    (bound : n≤D) (fit : raw.maxWidth<2^w) (terms : q≤2^w) (num : raw.copies<2^w)
    (sumFit : q*raw.copies<2^w) (i : Fin D) (tailRow : n ≤ i.val) :
    (RepairHistogram.debit (PortPadding.batch D raw) i).eval mem row=0 := by
  rw [PortPadding.debit raw mem row bound fit terms num sumFit i]
  exact PortPadding.extend_tail _ _ _ tailRow

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
