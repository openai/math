import OAI.Hierarchy.DescentEdgeTapePrefix
import OAI.Hierarchy.DescentBestLayoutPlan
import OAI.Hierarchy.DescentPackedScore
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # A single common packed layout comparison before the venue update -/
namespace Hierarchy.DescentPackedLayoutCPU
open DescentBestLayoutRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w n : ℕ} (B : DescentBestLayoutRAM.Banks)
def side (which : Bool) (w n : ℕ) : Procedure w :=
  (scan w (B.counts which) n (DescentPackedScore.read B.pairs (B.tariff which))).seq
    (ProtocolRAMEndpointPrefix.exclusive w (B.counts which) (B.starts which) n)

def program (w n : ℕ) : Procedure w := ((side B false w n).seq (side B true w n)).seq (scan w B.out 1 (chooseLine B))
def ticks (n : ℕ) := 2*((4+28*n)+(10+(3+12*n)))+(4+1*(2*(chooseLine B).work+4))

structure Space (w n : ℕ) : Prop where
  source : ∀b,B.pairs.Fits w (B.counts b)
  tariff : ∀b,(B.tariff b).Fits w (B.counts b)
  rows : n≤B.pairs.size
  apart : ∀b,B.counts b+n≤B.starts b
  endFits : ∀b,B.starts b+n+1 < 2^w
  first : B.starts false+n < B.counts true
  saved : (B.tariff true).base+(B.tariff true).size≤B.counts false
  left : B.leftEnd.base=B.starts false+n
  right : B.rightEnd.base=B.starts true+n
  lFit : B.leftEnd.Fits w B.out
  rFit : B.rightEnd.Fits w B.out
  last : B.out+1 < 2^w

def sideImage (b : Bool) (m : Memory w) (fee : Fin n→ℕ) :=
  ProtocolRAMEndpointPrefix.image (B.starts b) (DescentEdgeTapePrefix.before fee Fin.val)
    (image (B.counts b) n (DescentPackedScore.read B.pairs (B.tariff b)) m) n

def both (m : Memory w) (fee : Bool→Fin n→ℕ) := sideImage B true (sideImage B false m (fee false)) (fee true)
def after (m : Memory w) (fee : Bool→Fin n→ℕ) := image B.out 1 (chooseLine B) (both B m fee)

theorem side_run (b : Bool) (m : Memory w) (fee : Fin n→ℕ) (room : Space B w n)
    (actual : ∀i : Fin n,(DescentPackedScore.read B.pairs (B.tariff b)).eval m (i.val:Word w)=(fee i:Word w)) :
    (side B b w n).Exec m (sideImage B b m fee) ((4+28*n)+(10+(3+12*n))) := by
  let E:=DescentPackedScore.read B.pairs (B.tariff b)
  have first : (scan w (B.counts b) n E).Exec m (image (B.counts b) n E m) (4+28*n) := by
    have expense : 4+n*(2*E.work+4)=4+28*n :=by
      change 4+n*28=4+28*n
      rw [Nat.mul_comm n 28]
    rw [←expense]
    intro P R K machine pc reg pub exit installed data cfg mem enter same
    exact scan_exec (B.counts b) n E m (show E.Fits w (B.counts b) from
      ⟨room.tariff b,room.source b,trivial⟩) (by have h:=room.apart b;have h':=room.endFits b;omega)
      machine pc reg pub exit installed data cfg mem enter same
  apply Procedure.Exec.then first
  apply DescentEdgeTapePrefix.physical fee Fin.val _ (room.apart b) (room.endFits b)
  intro j hj
  let i : Fin n:=⟨j,hj⟩
  rw [show j=i.val from rfl,DescentEdgeTapePrefix.row_present fee Fin.val Fin.val_injective i]
  apply (read_image _ _ _ m i).trans
  exact actual i

theorem side_exec (b : Bool) (m : Memory w) (id fee : Fin n→ℕ) (room : Space B w n)
    (input : ∀i,m (B.pairs.base+i.val)=(id i:Word w))
    (size : ∀i,id i < (B.tariff b).size)
    (lookup : ∀i,m ((B.tariff b).base+id i)=(fee i:Word w)) :
    (side B b w n).Exec m (sideImage B b m fee) ((4+28*n)+(10+(3+12*n))) := by
  apply side_run B b m fee room
  intro i
  change (B.tariff b).read m (B.pairs.read m (i.val:Word w))=_
  rw [show B.pairs.read m (i.val:Word w)=m (B.pairs.base+i.val) by
    simp [Bank.read,Fin.val_cast_of_lt ((i.isLt.trans_le room.rows).trans (room.source b).2.1),
      Nat.mod_eq_of_lt (i.isLt.trans_le room.rows)],input]
  rw [show (B.tariff b).read m (id i:Word w)=m ((B.tariff b).base+id i) by
    simp [Bank.read,Fin.val_cast_of_lt ((size i).trans (room.tariff b).2.1),Nat.mod_eq_of_lt (size i)]]
  exact lookup i

theorem side_frame (b : Bool) (m : Memory w) (fee : Fin n→ℕ) (room : Space B w n) (x : ℕ)
    (outside : x < B.counts b ∨ B.starts b+n < x) : sideImage B b m fee x=m x := by
  have h:=room.apart b
  exact (ProtocolRAMEndpointPrefix.frame _ _ _ n x (by rcases outside with lo|hi;exact .inl (by omega);exact .inr (by omega))).trans
    (frame_image _ n _ _ _ (by rcases outside with lo|hi;exact .inl lo;exact .inr (by omega)))

theorem side_total (b : Bool) (m : Memory w) (fee : Fin n→ℕ) :
    sideImage B b m fee (B.starts b+n)=((∑i,fee i):ℕ) := by
  rw [sideImage,ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl]
  exact congrArg (fun j : ℕ=>(j:Word w)) (DescentEdgeTapePrefix.before_end fee Fin.val _ (fun i=>i.isLt))

private theorem finish (m : Memory w) (fee : Bool→Fin n→ℕ) (room : Space B w n)
    (first : (side B false w n).Exec m (sideImage B false m (fee false)) ((4+28*n)+(10+(3+12*n))))
    (second : (side B true w n).Exec (sideImage B false m (fee false)) (both B m fee)
      ((4+28*n)+(10+(3+12*n)))) :
    (program B w n).Exec m (after B m fee) (ticks B n) := by
  unfold ticks
  rw [two_mul]
  intro P R K machine pc reg pub exit installed data cfg mem enter same
  exact Procedure.Exec.then (Procedure.Exec.then first second)
    (scan_exec B.out 1 (chooseLine B) (both B m fee)
      (show (chooseLine B).Fits w B.out from ⟨⟨room.rFit,trivial⟩,⟨room.lFit,trivial⟩,trivial,trivial⟩) room.last)
    machine pc reg pub exit installed data cfg mem enter same

theorem run (m : Memory w) (id : Fin n→ℕ) (fee : Bool→Fin n→ℕ) (room : Space B w n)
    (input : ∀i,m (B.pairs.base+i.val)=(id i:Word w)) (size : ∀b i,id i < (B.tariff b).size)
    (lookup : ∀b i,m ((B.tariff b).base+id i)=(fee b i:Word w)) :
    (program B w n).Exec m (after B m fee) (ticks B n) := by
  apply finish B m fee room
  · exact side_exec B false m id (fee false) room input (size false) (lookup false)
  · exact side_exec B true (sideImage B false m (fee false)) id (fee true) room
      (fun i=>(side_frame B false m _ room _ (.inl (by have h:=(room.source false).2.2;have j:=i.isLt;have:=room.rows;omega))).trans (input i))
      (size true) (fun i=>(side_frame B false m _ room _ (.inl (by have:=room.saved;have:=size true i;omega))).trans (lookup true i))

/-- Every input memory, including a malformed candidate, executes the same finite program. -/
theorem total_run (m : Memory w) (room : Space B w n) :
    ∃fee : Bool→Fin n→ℕ,(program B w n).Exec m (after B m fee) (ticks B n) := by
  let rate (b : Bool) (mem : Memory w) (i : Fin n) := ((DescentPackedScore.read B.pairs (B.tariff b)).eval mem (i.val:Word w)).val
  let left:=sideImage B false m (rate false m)
  let fee (b : Bool) := if b then rate true left else rate false m
  refine ⟨fee,finish B m fee room ?_ ?_⟩
  · exact side_run B false m (rate false m) room (fun _=>by simp [rate])
  · exact side_run B true left (rate true left) room (fun _=>by simp [rate])

theorem above (m : Memory w) (fee : Bool→Fin n→ℕ) (room : Space B w n) (x : ℕ) (high : B.out < x) :
    after B m fee x=m x := by
  have endRight:=room.rFit.2.2
  rw [room.right] at endRight
  have ends:=room.apart true
  have left:=room.first
  exact (frame_image _ _ _ _ _ (.inr (by omega))).trans
    ((side_frame B true _ _ room x (.inr (by omega))).trans (side_frame B false _ _ room x (.inr (by omega))))

theorem read (m : Memory w) (fee : Bool→Fin n→ℕ) (room : Space B w n) (fits : ∀b,(∑i,fee b i) < 2^w) :
    after B m fee B.out=if (∑i,fee true i) < (∑i,fee false i) then (1:Word w) else 0 := by
  have lhs : both B m fee B.leftEnd.base=((∑i,fee false i):ℕ) := by
    rw [room.left]
    exact (side_frame B true _ _ room _ (.inl room.first)).trans (side_total B false m _)
  have rhs : both B m fee B.rightEnd.base=((∑i,fee true i):ℕ) := by rw [room.right];exact side_total B true _ _
  rw [show after B m fee B.out=(chooseLine B).eval (both B m fee) 0 by simpa [after] using read_image B.out 1 (chooseLine B) (both B m fee) (0:Fin 1)]
  change (if Comparison.lt.test (B.rightEnd.read _ 0) (B.leftEnd.read _ 0) then _ else _)=_
  simp only [Bank.read,Fin.val_zero,Nat.zero_mod,Nat.add_zero,rhs,lhs,Comparison.test,decide_eq_true_eq]
  have compare : ((∑i,fee true i:ℕ):Word w) < ((∑i,fee false i:ℕ):Word w) ↔ (∑i,fee true i) < (∑i,fee false i) := by
    change (((∑i,fee true i:ℕ):Word w).val < ((∑i,fee false i:ℕ):Word w).val) ↔ _
    rw [Fin.val_cast_of_lt (fits true),Fin.val_cast_of_lt (fits false)]
  simp only [compare,Expr.eval,Nat.cast_one,Nat.cast_zero]

end
end Hierarchy.DescentPackedLayoutCPU

end OAI
