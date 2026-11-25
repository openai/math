import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # A native addition-only address generator for accepted descriptor fields -/

namespace Hierarchy.ProtocolRAMFieldLoop

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w k r : ℕ}

/-- The loop ordinal is in register 0. Registers 2, 3 and 4 form the source and
destination offsets with doublings and additions. Register 5 holds the one word copied. -/
def ops : List (Op 6 3) :=
  [.binary .add 2 0 0,.binary .add 3 2 0,.binary .add 4 2 2,.binary .add 4 4 4,
   .publicWord 2 0,.binary .add 2 2 4,.read 5 2,.publicWord 2 1,.binary .add 2 2 3,
   .write 2 5,.constant 4 1,.binary .add 0 0 4]

def values (w src dst n : ℕ) : Fin 3 → Word w := ![src,dst,n]

def procedure (w src dst n : ℕ) : Procedure w :=
  ⟨15,6,3,OrdinalOpLoop.block w ops 0 1 2,values w src dst n⟩

def image (src dst n : ℕ) (m : Memory w) : Memory w := fun a =>
  if dst ≤ a ∧ (a-dst)%3=0 ∧ (a-dst)/3<n then m (src+8*((a-dst)/3)) else m a

theorem image_read (src dst n : ℕ) (m : Memory w) (i : Fin n) :
    image src dst n m (dst+3*i.val)=m (src+8*i.val) := by
  have hi := i.isLt
  simp [image,show dst≤dst+3*i.val by omega,hi]

theorem image_frame (src dst n : ℕ) (m : Memory w) (a : ℕ)
    (away : ∀ i : Fin n, a ≠ dst+3*i.val) : image src dst n m a=m a := by
  apply ite_eq_right
  rintro ⟨lo,mod,idx⟩
  exact away ⟨_,idx⟩ (by dsimp;omega)

private theorem image_step (src dst n : ℕ) (m : Memory w) :
    image src dst (n+1) m=Function.update (image src dst n m) (dst+3*n) (m (src+8*n)) := by
  funext a
  by_cases e : a=dst+3*n
  · subst a
    rw [Function.update_self]
    exact image_read src dst (n+1) m ⟨n,Nat.lt_succ_self _⟩
  · have same : (dst≤a ∧ (a-dst)%3=0 ∧ (a-dst)/3<n+1) ↔
        dst≤a ∧ (a-dst)%3=0 ∧ (a-dst)/3<n := by omega
    simp only [image,same,Function.update_of_ne e]

set_option maxRecDepth 8192 in
private theorem row_trace (reg : Fin 6 ↪ Fin r) (pub : Fin 3 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w) :
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,writeMemory m (v (pub 1)+3*rs (reg 0)) (m (v (pub 0)+8*rs (reg 0)).val)) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  have three (z : Word w) : z+z+z = 3*z := by ring
  have eight (z : Word w) : z+z+(z+z)+(z+z+(z+z)) = 8*z := by ring
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,
    reg.injective.eq_iff,eight,three]


theorem run (src dst n : ℕ) (countFit : n<2^w)
    (inputFit : ∀ i : Fin n, src+8*i.val<2^w) (outputFit : ∀ i : Fin n, dst+3*i.val<2^w)
    (apart : ∀ i j : Fin n,src+8*i.val ≠ dst+3*j.val) :
    (procedure w src dst n).Spec (fun _=>True) (fun m o=>o=image src dst n m) (3+13*n) := by
  intro pcs regs pubs M pc reg pub exit rom data c m entry _
  change Fin 6↪Fin regs at reg
  change Fin 3→Fin pubs at pub
  change ∀ i,M.publicData (pub i)=values w src dst n i at data
  obtain ⟨out,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 2 M pc reg pub exit rom n countFit
    (data 2) (fun i=> image src dst i m) (by
      intro i hi state rs cur limit
      obtain ⟨es,z,act,inc,keep⟩ := row_trace reg pub M.publicData state rs (image src dst i m)
      refine ⟨es,z,?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,cur] at act
      change trace _ _ _ _ _ = some (_,_,writeMemory _ ((dst:Word w)+3*(i:Word w))
        (image src dst i m ((src:Word w)+8*(i:Word w)).val)) at act
      have srcAddr : (src:Word w)+8*(i:Word w) = (src+8*i:ℕ) := by simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      have dstAddr : (dst:Word w)+3*(i:Word w) = (dst+3*i:ℕ) := by simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      have srcRead : image src dst i m (src+8*i)=m (src+8*i) :=
        image_frame _ _ _ _ _ (fun j=>apart ⟨i,hi⟩ ⟨j.val,j.isLt.trans hi⟩)
      have store : writeMemory (image src dst i m) ((dst+3*i:ℕ):Word w) (m (src+8*i)) =
          Function.update (image src dst i m) (dst+3*i) (m (src+8*i)) := by
        funext a
        change (if a=(((dst+3*i:ℕ):Word w).val) then m (src+8*i) else image src dst i m a) = _
        rw [Fin.val_cast_of_lt (outputFit ⟨i,hi⟩)]
        by_cases eq : a=dst+3*i <;> simp [eq]
      simpa only [srcAddr,dstAddr,Fin.val_cast_of_lt (inputFit ⟨i,hi⟩),srcRead,store,image_step] using act)
    c entry
  have init : image src dst 0 m=m := by funext a;simp [image]
  rw [init] at advance
  exact ⟨_,by change 3+n*13≤3+13*n;omega,out,_,advance,stop,rfl⟩

/-- The complete CPU alphabet used by descriptor emission. -/
def Cheap {P R K : ℕ} : Instr w P R K → Prop
  | .binary op .. => op = .add
  | .constant .. | .publicWord .. | .readExternal .. | .writeExternal .. | .jumpLt .. => True
  | _ => False

def CheapCode (A : Procedure w) : Prop :=
  ∀ {P R K : ℕ} (pc : Fin A.labels ↪ Fin P) (reg : Fin A.registers ↪ Fin R)
    (pub : Fin A.slots → Fin K) (exit : Fin P) (i : Fin A.labels), Cheap (A.block.emit pc reg pub exit i)

theorem cheap_seq {A B : Procedure w} (a : CheapCode A) (b : CheapCode B) : CheapCode (A.seq B) := by
  intro P R K pc reg pub exit i
  induction i using Fin.addCases with
  | left t =>
    simp only [Procedure.seq,ContinuationLink.Block.seq,ContinuationLink.Block.reindex,Fin.addCases_left]
    exact a _ _ _ _ t
  | right t =>
    simp only [Procedure.seq,ContinuationLink.Block.seq,ContinuationLink.Block.reindex,Fin.addCases_right]
    exact b _ _ _ _ t

set_option maxRecDepth 8192 in
theorem procedure_cheap (w src dst n : ℕ) : CheapCode (procedure w src dst n) := by
  intro P R K pc reg pub exit i
  change Fin 15 at i
  fin_cases i <;> first | exact True.intro | rfl

end Hierarchy.ProtocolRAMFieldLoop

end OAI
