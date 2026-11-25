import OAI.Hierarchy.DescentPackedWalshDepth

namespace OAI
/-! # Chronological publication of every measured depth from one immutable local spectrum -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w H u l : ℕ}

structure Calendar (k : ℕ) where
  limit : ℕ
  atDepth : ℕ→DepthShelf
  pre : ∀j,limit≤(atDepth j).first
  order : ∀i j,i<j→(atDepth i).out+2^k≤(atDepth j).first

namespace Calendar
variable (C : Calendar (u+l)) (P : Plan)
local notation "k" => u+l

def code (w H : ℕ) : ℕ→Procedure w
  | 0=>scan w C.limit 0 .row
  | j+1=>(code w H j).seq ((C.atDepth j).code P w H u j)

def state (H : ℕ) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | j+1=>(C.atDepth j).after P H u j (state H m j)

def ticks (H : ℕ) : ℕ→ℕ
  | 0=>4
  | j+1=>ticks H j+(C.atDepth j).clock P H u

/-- Each call is to the concrete checked-weight/read/extract program. The induction keeps every
earlier scalar result and the one copy of the original spectrum and public dictionaries. -/
theorem folded {H : ℕ} (mem : Memory w) (value : ℕ→Fin (2^k)→ℕ)
    (width : C.limit<2^w) (n : ℕ)
    (steps : ∀j<n,∀cur : Memory w,(∀x<C.limit,cur x=mem x) →
      let D:=C.atDepth j; let dst:=D.after P H u j cur
      (D.code P w H u j).Exec cur dst (D.clock P H u) ∧
      (∀i : Fin (2^k),dst (D.out+i.val)=(value j i:Word w)) ∧ ∀z<D.first,dst z=cur z) :
    (C.code P w H n).Exec mem (C.state P H mem n) (C.ticks P H n) ∧
    (∀j<n,∀i : Fin (2^k),C.state P H mem n ((C.atDepth j).out+i.val)=(value j i:Word w)) ∧
    ∀z<C.limit,C.state P H mem n z=mem z := by
  induction n with
  | zero =>
    refine ⟨?_,by simp,fun _ _=>rfl⟩
    have same : image C.limit 0 .row mem=mem:=by
      funext z
      exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
    have start : (scan w C.limit 0 .row).Exec mem (image C.limit 0 .row mem)
        (4+0*(2*Expr.row.work+4)) :=
      @scan_exec w C.limit 0 .row mem trivial (by simpa only [Nat.add_zero] using width)
    rw [same,Nat.zero_mul,Nat.add_zero] at start
    exact @start
  | succ n ih =>
    obtain ⟨before,rows,prefixRead⟩:=ih (fun j h=>steps j (Nat.lt_succ_of_lt h))
    obtain ⟨afterwards,newRows,low⟩:=steps n (Nat.lt_succ_self _) (C.state P H mem n) prefixRead
    refine ⟨?_,?_,fun z hz=>(low z (hz.trans_le (C.pre n))).trans (prefixRead z hz)⟩
    · intro labels regs slots machine
      exact Procedure.Exec.then before afterwards machine
    · intro j hj i
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with lt|rfl
      · exact (low _ ((Nat.add_lt_add_left i.isLt _).trans_le (C.order j n lt))).trans (rows j lt i)
      · exact newRows i

end Calendar
end
end Hierarchy.DescentPackedWalsh

end OAI
