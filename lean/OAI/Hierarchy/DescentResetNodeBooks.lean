import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Pack the scalar reset outputs into the physical node books of the next date -/
namespace Hierarchy.DescentResetNodeBooks
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentOrdinaryAtomFieldRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- A common zero-preserving shift page and one insertion page per node.
The page and operand ordinals do not enter the dictionary aperture. -/
def page (s N M : ℕ) : Fin (N+1)→ROM.Page :=
  Fin.cases ⟨(s*N)*M,fun x=>2^(s*M)*x.val⟩
    (fun i=>⟨(s*N+s)*M,fun x=>(DescentPackedZip.table (M:=M) (Gather.setField (d:=s) i) x).val⟩)
def tabs (floor s N M : ℕ) (j : Fin N) : Tables :=
  ROM.joined (page s N M) ((s*N+s)*M) floor ![0,j.succ]
def rows (H G M : ℕ) := H*chunks G M
def rounded (r : ℕ) := 2^Nat.clog 2 (r+1)
def volume (N s M : ℕ) := (N+1)*2^((s*N+s)*M)
def output (floor _names N H G s M : ℕ) := floor+max (volume N s M) (rounded (rows H G M))
def endAddress (floor names N H G s M : ℕ) := output floor names N H G s M+names*rows H G M+rounded (rows H G M)
def bank (floor names N H G s M : ℕ) (p : Fin names) : Bank :=
  ⟨output floor names N H G s M+p.val*rows H G M,Nat.clog 2 (rows H G M+1)⟩
def scalar (old N H G M p : ℕ) (n : Fin N) : Bank :=
  ⟨old+(p*N+n.val)*rows H G M,Nat.clog 2 (rows H G M+1)⟩
def term (floor old N H G s M p : ℕ) :=
  Gather.assembly (tabs floor s N M) (fun n=>.lookup (scalar old N H G M p n) .row)
def passes (floor old names N H G s M : ℕ) := DescentPackedFlowBatch.passes (output floor names N H G s M)
  (rows H G M) (rows H G M) (term floor old N H G s M) 0 names
def program (floor old names N H G s M w : ℕ) :=
  (ROM.mount (page s N M) ((s*N+s)*M) w floor).seq (ProtocolRAM.program w (passes floor old names N H G s M))
def ticks (floor old names N H G s M : ℕ) := (4+10*volume N s M)+clock (passes floor old names N H G s M)
def image (floor old names N H G s M : ℕ) (m : Memory w) := result (passes floor old names N H G s M)
  (ROM.after (page s N M) ((s*N+s)*M) floor m)

theorem affine (floor names N H G s M : ℕ) :
    endAddress floor names N H G s M=floor+endAddress 0 names N H G s M := by
  simp only [endAddress,output,Nat.zero_add,Nat.add_assoc]

theorem capacity (r : ℕ) : r≤rounded r := (Nat.le_succ r).trans (Nat.le_pow_clog (by decide) _)

theorem placed (floor names N H G s M : ℕ) (p : Fin names) (space : endAddress floor names N H G s M<2^w) :
    (bank floor names N H G s M p).Fits w (endAddress floor names N H G s M) ∧
      rows H G M≤(bank floor names N H G s M p).size := by
  have bound:=Nat.mul_le_mul_right (rows H G M) p.isLt.le
  have short : (bank floor names N H G s M p).base+(bank floor names N H G s M p).size≤endAddress floor names N H G s M :=by
    change output floor names N H G s M+p.val*rows H G M+rounded (rows H G M)≤
      output floor names N H G s M+names*rows H G M+rounded (rows H G M)
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (short.trans_lt space),short⟩,capacity _⟩

theorem page_bits (s N M : ℕ) (i : Fin (N+1)) : (page s N M i).bits≤(s*N+s)*M :=by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  · exact le_rfl

theorem static (floor N s M : ℕ) (m : Memory w) (i : Fin N) :
    Static (tabs floor s N M i) (Gather.setField (d:=s) i) M (ROM.after (page s N M) ((s*N+s)*M) floor m) :=by
  apply ROM.binary_mounted _ _ _ _ _ _ (page_bits s N M) _
  intro z;fin_cases z <;> rfl

private theorem geometry (floor old names N H G s M : ℕ) (p : Fin names)
    (prior : old+(names*N)*rows H G M≤floor) (space : endAddress floor names N H G s M<2^w) :
    Gather.Bounds (w:=w) (d:=s) (M:=M) (tabs floor s N M)
      (fun n=>Expr.lookup (scalar old N H G M p.val n) .row) (output floor names N H G s M) := by
  let out:=output floor names N H G s M
  have top : out<2^w := (Nat.le_trans (Nat.le_add_right out _) (Nat.le_add_right _ _)).trans_lt space
  have rom : floor+volume N s M≤out:=Nat.add_le_add_left (Nat.le_max_left ..) _
  have pad : floor+rounded (rows H G M)≤out:=Nat.add_le_add_left (Nat.le_max_right ..) _
  intro j
  have last : p.val*N+j.val<names*N:=calc
    _ < p.val*N+N:=Nat.add_lt_add_left j.isLt _
    _ = (p.val+1)*N:=(Nat.succ_mul ..).symm
    _ ≤ names*N:=Nat.mul_le_mul_right _ p.isLt
  have below:=Nat.mul_le_mul_right (rows H G M) last.le
  have end_ : (scalar old N H G M p.val j).base+(scalar old N H G M p.val j).size≤out:=by
    change old+(p.val*N+j.val)*rows H G M+rounded (rows H G M)≤out
    omega
  have valid (i : Fin (N+1)) :=ROM.bank_room (page s N M) ((s*N+s)*M) floor out i (page_bits ..) rom top
  exact ⟨⟨⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (end_.trans_lt top),end_⟩,trivial⟩,valid 0,valid j.succ,rfl,rfl⟩

theorem cheap (floor old names N H G s M w : ℕ) : CheapCode (program floor old names N H G s M w) := by
  unfold program
  apply ProtocolRAM.cheap_seq
  · apply ROM.cheap
  · apply ProtocolRAM.program_cheap

theorem any (floor old names N H G s M : ℕ) (m : Memory w)
    (prior : old+(names*N)*rows H G M≤floor) (space : endAddress floor names N H G s M<2^w) :
    (program floor old names N H G s M w).Exec m (image floor old names N H G s M m) (ticks floor old names N H G s M) ∧
    ∀a,a<floor ∨ endAddress floor names N H G s M≤a→image floor old names N H G s M m a=m a :=by
  let out:=output floor names N H G s M
  have rom : floor+volume N s M≤out:=Nat.add_le_add_left (Nat.le_max_left ..) _
  have ends : out+names*rows H G M≤endAddress floor names N H G s M:=Nat.le_add_right ..
  have top:=(Nat.le_add_right out (names*rows H G M)).trans ends
  obtain ⟨mounted,_⟩:=ROM.run (page s N M) ((s*N+s)*M) floor m ((rom.trans top).trans_lt space)
  let mid:=ROM.after (page s N M) ((s*N+s)*M) floor m
  have valid (j : ℕ) (hj:j<names) : (term floor old N H G s M j).Fits w out :=
    Gather.fits _ _ _ (geometry floor old names N H G s M ⟨j,hj⟩ prior space) _
  obtain ⟨run,_,low⟩:=DescentPackedFlowBatch.execute out (rows H G M) (rows H G M) names _ mid valid (ends.trans_lt space) le_rfl
  refine ⟨mounted.then run,?_⟩
  intro addr h
  rcases h with h|h
  · exact (low addr (h.trans_le ((Nat.le_add_right ..).trans rom))).trans (ROM.frame _ _ _ _ _ (.inl h))
  · have after_:=DescentPackedFlowBatch.above out (rows H G M) (rows H G M) (term floor old N H G s M) mid 0 names addr le_rfl
        (by simpa only [Nat.zero_add] using ends.trans h)
    exact after_.trans (ROM.frame _ _ _ _ _ (.inr ((rom.trans top).trans h)))

/-- Read the physically posted scalar pages at their original chronological addresses. -/
theorem posted_at (floor old names N H G s M : ℕ) (m : Memory w)
    (prior : old+(names*N)*rows H G M≤floor) (space : endAddress floor names N H G s M<2^w)
    (p : Fin names) (x : Fin N→Fin H→Fin G→Cell s)
    (scalarRead : ∀(n : Fin N),DescentPackedColony.Reads (scalar old N H G M p.val n) (x n) M m) :
    DescentPackedColony.Reads (bank floor names N H G s M p) (fun h g=>encode s N (fun n=>x n h g)) M (image floor old names N H G s M m) :=by
  let out:=output floor names N H G s M
  let mid:=ROM.after (page s N M) ((s*N+s)*M) floor m
  have fits (j : Fin names) :=geometry floor old names N H G s M j prior space
  have valid (j : ℕ) (hj:j<names) : (term floor old N H G s M j).Fits w out:=Gather.fits _ _ _ (fits ⟨j,hj⟩) _
  have packed :=(DescentPackedFlowBatch.execute out (rows H G M) (rows H G M) names _ mid valid
    ((Nat.le_add_right ..).trans_lt space) le_rfl).2.1 p
  have seen (n : Fin N) : Source (.lookup (scalar old N H G M p.val n) .row) (x n) M mid :=by
    apply source_column _ out ((fits p n).1.1) mid _ (capacity _)
    intro rowId
    let t:=(row H G M rowId).val
    have hrow : t<rows H G M :=(row H G M rowId).isLt
    have before : p.val*N+n.val<names*N:=calc
      _ < p.val*N+N:=Nat.add_lt_add_left n.isLt _
      _ = (p.val+1)*N:=(Nat.succ_mul ..).symm
      _ ≤ names*N:=Nat.mul_le_mul_right _ p.isLt
    have inside:=Nat.mul_le_mul_right (rows H G M) before
    rw [Nat.succ_mul] at inside
    have haddr : (scalar old N H G M p.val n).base+t<floor:=by change old+_+t<floor;omega
    exact (ROM.frame _ _ _ _ _ (.inl haddr)).trans (scalarRead n rowId)
  have complete:=Gather.collected (tabs floor s N M) _ out (fits p) mid (static floor N s M m)
    (fun h g n=>x n h g) seen (List.finRange N)
  intro rowId
  apply (packed (row H G M rowId)).trans
  simpa only [term,Gather.assembly,List.mem_finRange,ite_true] using complete rowId

theorem posted (floor old names N H G s M : ℕ) (m : Memory w)
    (prior : old+(names*N)*rows H G M≤floor) (space : endAddress floor names N H G s M<2^w)
    (x : Fin names→Fin N→Fin H→Fin G→Cell s)
    (scalarRead : ∀(p : Fin names) (n : Fin N),DescentPackedColony.Reads (scalar old N H G M p.val n) (x p n) M m) (p : Fin names) :
    DescentPackedColony.Reads (bank floor names N H G s M p) (fun h g=>encode s N (fun n=>x p n h g)) M (image floor old names N H G s M m) :=
  posted_at floor old names N H G s M m prior space p (x p) (scalarRead p)

end
end Hierarchy.DescentResetNodeBooks

end OAI
