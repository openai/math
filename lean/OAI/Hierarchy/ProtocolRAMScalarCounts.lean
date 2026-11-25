import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Native histogram of scalar-table requests -/

namespace Hierarchy.ProtocolRAMScalarCounts
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators

variable {w n r k : ℕ}

/-- Load the current key and increment its indirect bin. Registers zero and
one carry the chronological cursor and its exclusive end. -/
def ops : List (Op 5 3) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,.publicWord 3 1,.binary .add 2 2 3,
   .read 3 2,.constant 4 1,.binary .add 3 3 4,.write 2 3,.binary .add 0 0 4]

def values (w src base n : ℕ) : Fin 3 → Word w := ![src,base,n]

def counting (w src base n : ℕ) : Procedure w :=
  ⟨13,5,3,OrdinalOpLoop.block w ops 0 1 2,values w src base n⟩

def accumulated (base : ℕ) (key : ℕ → ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | i+1 => fun a => if a=base+key i then accumulated base key m i a+1
                     else accumulated base key m i a

theorem below (base : ℕ) (key : ℕ → ℕ) (m : Memory w) (i a : ℕ) (h : a<base) :
    accumulated base key m i a=m a := by
  induction i with
  | zero => rfl
  | succ i ih => simp [accumulated,show a≠base+key i by omega,ih]

theorem bin (base : ℕ) (key : ℕ → ℕ) (m : Memory w) (i h : ℕ) :
    accumulated base key m i (base+h)=m (base+h)+
        ((∑ j ∈ Finset.range i, if key j=h then 1 else 0 : ℕ) : Word w) := by
  induction i with
  | zero => simp [accumulated]
  | succ i ih =>
    rw [accumulated,Finset.sum_range_succ]
    change (if base+h=base+key i then accumulated base key m i (base+h)+1
      else accumulated base key m i (base+h))=_
    by_cases same : key i=h
    · have together : base+h=base+key i := congrArg (base+·) same.symm
      rw [ite_eq_left together,ite_eq_left same,ih,Nat.cast_add,Nat.cast_one,add_assoc]
    · have apart : base+h≠base+key i := fun eqn=>same (Nat.add_left_cancel eqn).symm
      simp only [ite_eq_right apart,ite_eq_right same,Nat.add_zero,ih]

set_option maxRecDepth 8192 in
private theorem trace_row (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) (v : Fin k → Word w)
    (state : Word w) (rs : Regs w r) (m : Memory w) :
    let address := m (v (pub 0)+rs (reg 0)).val+v (pub 1)
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,writeMemory m address (m address.val+1)) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem run (src base bins n : ℕ) (key : ℕ → ℕ) (safe : src+n≤base) (fit : base+bins<2^w)
    (countFit : n<2^w) (bounded : ∀ i<n, key i<bins) :
    (counting w src base n).Spec (fun m => ∀ i<n,m (src+i)=(key i:Word w))
      (fun m o => o=accumulated base key m n) (3+11*n) := by
  intro pcs regs pubs M pc reg pub exit rom data c m entry loaded
  change Fin 5 ↪ Fin regs at reg
  change Fin 3 → Fin pubs at pub
  change ∀ i, M.publicData (pub i)=values w src base n i at data
  obtain ⟨out,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 2 M pc reg pub exit rom n
    countFit (data 2) (accumulated base key m) (by
      intro i hi state rs cur limit
      obtain ⟨es,z,act,inc,keep⟩ := trace_row reg pub M.publicData state rs (accumulated base key m i)
      refine ⟨es,z,?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,cur] at act
      let mem := accumulated base key m i
      change trace _ _ _ _ _ = some (_,_,writeMemory mem
        (mem ((src:Word w)+(i:Word w)).val+(base:Word w))
        (mem (mem ((src:Word w)+(i:Word w)).val+(base:Word w)).val+1)) at act
      have fetch : mem ((src:Word w)+(i:Word w)).val=(key i:Word w) := by
        rw [←Nat.cast_add, Fin.val_cast_of_lt (by omega : src+i<2^w)]
        exact (below base key m i _ (by omega)).trans (loaded i hi)
      have where_ : (key i:Word w)+(base:Word w) = ((base+key i:ℕ):Word w) := by
        rw [Nat.cast_add,add_comm]
      have fits : base+key i<2^w := by have := bounded i hi; omega
      rw [fetch,where_,Fin.val_cast_of_lt fits] at act
      have writes : writeMemory mem ((base+key i:ℕ):Word w) (mem (base+key i)+1)=
          accumulated base key m (i+1) := by
        funext a
        simp only [writeMemory,Fin.val_cast_of_lt fits,accumulated]
        by_cases same : a=base+key i
        · simp only [same,mem]
        · simp only [ite_eq_right same,mem]
      rwa [writes] at act) c entry
  exact ⟨_,by change 3+n*11≤3+11*n; omega,out,_,advance,stop,rfl⟩

def clear (w base bins : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (.literal 0 : Term w 0 1) Fin.elim0 base bins

/-- Empty all possible bins before processing the request stream, so
unrequested keys have exactly the zero count. -/
theorem histogram (src base bins n : ℕ) (key : ℕ → ℕ)
    (safe : src+n≤base) (fit : base+bins<2^w) (countFit : n<2^w)
    (bounded : ∀ i<n,key i<bins) :
    ((clear w base bins).seq (counting w src base n)).Spec
      (fun m => ∀ i<n, m (src+i)=(key i:Word w))
      (fun _ o => ∀ b : Fin bins, o (base+b.val)=
        ((∑ j ∈ Finset.range n, if key j=b.val then 1 else 0 : ℕ) : Word w))
      (7+6*bins+11*n) := by
  have first : (clear w base bins).Spec (fun m => ∀ i<n,m (src+i)=(key i:Word w))
      (fun m o=>o=fillSegment base bins (fun _=>0) m) (4+6*bins) := by
    unfold clear
    have eqn : 4+6*bins=4+bins*(2*(Term.literal (w:=w) (k:=0) (n:=1) 0).binds+4) := by
      change 4+6*bins=4+bins*(2*1+4)
      omega
    rw [eqn]
    apply PhysicalInputPhases.writing_spec _ _ _ _ fit
    intros
    exact Term.eval_literal ..
  have first' : (clear w base bins).Spec (fun m => ∀ i<n,m (src+i)=(key i:Word w))
      (fun m o=>o=fillSegment base bins (fun _=>0) m ∧ ∀ i<n,o (src+i)=(key i:Word w))
      (4+6*bins) := by
    intro P R K M pc reg pub exit rom data c m start inp
    obtain ⟨t,ht,z,o,adv,pc',eqn⟩ := first M pc reg pub exit rom data c m start inp
    subst o
    refine ⟨t,ht,z,_,adv,pc',rfl,?_⟩
    intro i hi
    simp only [fillSegment,show ¬ (base ≤ src+i ∧ src+i < base+bins) by omega,ite_false]
    exact inp i hi
  have second : (counting w src base n).Spec _ _ _ := run src base bins n key safe fit countFit bounded
  have both : ((clear w base bins).seq (counting w src base n)).Spec _ _ _ :=
    first'.seq second (fun _ _ h=>h.2)
  intro P R K M pc reg pub exit rom data c m start inp
  obtain ⟨t,ht,z,o,adv,done,mid,⟨eqn,_⟩,image⟩ := both M pc reg pub exit rom data c m start inp
  refine ⟨t,by omega,z,o,adv,done,?_⟩
  intro b
  rw [image,eqn]
  rw [bin]
  simp [fillSegment,show base+b.val<base+bins by have := b.isLt; omega]

end Hierarchy.ProtocolRAMScalarCounts

end OAI
