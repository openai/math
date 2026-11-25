import OAI.Hierarchy.ProtocolRAMPortScale
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # A native row-base column for immutable endpoint port wiring -/

namespace Hierarchy.ProtocolRAMStaticPorts

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM
open scoped Fin.CommRing

variable {w n ports : ℕ}

def expression (w out lanes : ℕ) (port : Expr) : Term w 0 1 :=
  (port.compile w out).letThen
    ((ProtocolRAMPortScale.scale w (ProtocolRAMPortScale.bitWidth lanes) lanes).rename (fun _ => (0:Fin 2)))

def program (w out n lanes : ℕ) (port : Expr) : Procedure w :=
  PhysicalInputPhases.writing (expression w out lanes port) Fin.elim0 out n

def work (n lanes : ℕ) (port : Expr) : ℕ :=
  4+n*(2*(port.work+1+2*ProtocolRAMPortScale.bitWidth lanes)+4)

def word (out lanes : ℕ) (port : Fin n→Fin ports) (a : ℕ) : Word w :=
  if h : a-out < n then (((port ⟨a-out,h⟩).val*lanes:ℕ):Word w) else 0

def image (out lanes : ℕ) (port : Fin n→Fin ports) (m : Memory w) : Memory w :=
  fillSegment out n (word out lanes port) m

theorem read (out lanes : ℕ) (port : Fin n→Fin ports) (m : Memory w) (i : Fin n) :
    image out lanes port m (out+i.val)=(((port i).val*lanes:ℕ):Word w) := by
  simp [image,fillSegment,word,show out+i.val < out+n by have := i.isLt; omega,i.isLt]

theorem frame (out lanes : ℕ) (port : Fin n→Fin ports) (m : Memory w) (a : ℕ)
    (away : a < out ∨ out+n ≤ a) : image out lanes port m a=m a := by
  simp [image,fillSegment,show ¬ (out ≤ a ∧ a < out+n) by omega]

/-- Read one actual port expression per row and materialize its immutable `port*lanes`
base. Each binary digit uses at most two additions, without native multiplication. -/
theorem run (out lanes : ℕ) (port : Fin n→Fin ports) (e : Expr) (m : Memory w)
    (fit : e.Fits w out) (room : out+n<2^w)
    (data : ∀ i : Fin n, e.eval m (i.val:Word w)=((port i).val:Word w)) :
    (program w out n lanes e).Exec m (image out lanes port m) (work n lanes e) := by
  have pass : (program w out n lanes e).Spec (·=m) (fun src dst => dst=image out lanes port src)
      (4+n*(2*(expression w out lanes e).binds+4)) := PhysicalInputPhases.writing_spec (expression w out lanes e) Fin.elim0 out n room
    (·=m) (word out lanes port) (by
      intro original eq a now lo hi agrees
      subst original
      have live : a.val-out < n := by omega
      let i : Fin n := ⟨a.val-out,live⟩
      have sub : a-(out:Word w)=(i.val:Word w) := by simp only [i,Nat.cast_sub lo,Fin.cast_val_eq_self]
      have got : (e.compile w out).eval Fin.elim0 now (fun _=>a) = ((port i).val:Word w) := by
        rw [eval_compile e now a fit (by omega),sub]
        exact (eval_below e _ m now fit (fun j hj => agrees j (.inl hj))).trans (data i)
      simp only [expression,Term.eval_letThen,Term.eval_rename,ProtocolRAMPortScale.eval_scale _ _ _ _
        (ProtocolRAMPortScale.fits lanes),Function.comp_apply,Fin.cons_zero,got,word,dite_eq_left live,Nat.cast_mul]
      rfl)
  have limit : 4+n*(2*(expression w out lanes e).binds+4) ≤ work n lanes e := by
    have cnt := ProtocolRAMPortScale.binds w (ProtocolRAMPortScale.bitWidth lanes) lanes
    have bound : (expression w out lanes e).binds ≤ e.work+1+2*ProtocolRAMPortScale.bitWidth lanes := by
      simp only [expression,Term.binds_letThen,Term.binds_rename,compile_binds]
      omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) 4
  intro P R K M pc reg pub exit rom data cfg raw entry eq
  subst raw
  obtain ⟨t,ht,done,after,run,hpc,value⟩ := pass M pc reg pub exit rom data cfg m entry rfl
  exact ⟨t,ht.trans limit,done,after,run,hpc,value⟩


end Hierarchy.ProtocolRAMStaticPorts

end OAI
