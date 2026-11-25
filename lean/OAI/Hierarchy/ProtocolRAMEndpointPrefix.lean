import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Addition-only native exclusive prefixes of site-bin counts -/

namespace Hierarchy.ProtocolRAMEndpointPrefix

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing

variable {w : ℕ}

def ops : List (Op 6 3) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,
   .publicWord 3 1,.binary .add 3 3 0,.read 4 3,
   .binary .add 4 4 2,.constant 5 1,.binary .add 3 3 5,.write 3 4,.binary .add 0 0 5]

def values (w counts starts n : ℕ) : Fin 3→Word w := ![counts,starts,n]

def accumulate (w counts starts n : ℕ) : Procedure w :=
  ⟨14,6,3,OrdinalOpLoop.block w ops 0 1 2, values w counts starts n⟩

def zero (w starts : ℕ) : Procedure w :=
  PhysicalInputPhases.writing (.literal 0 : Term w 0 1) Fin.elim0 starts 1

def exclusive (w counts starts n : ℕ) : Procedure w := (zero w starts).seq (accumulate w counts starts n)

/-- The site-start buffer also records the final exclusive end at position `n`. -/
def image (starts : ℕ) (pref : ℕ→ℕ) (m : Memory w) (n : ℕ) : Memory w :=
  fillSegment starts (n+1) (fun a => (pref (a-starts):Word w)) m

theorem read (starts : ℕ) (pref : ℕ→ℕ) (m : Memory w) (n t : ℕ) (ht : t ≤ n) :
    image starts pref m n (starts+t)=(pref t:Word w) := by
  simp [image,fillSegment,show starts+t < starts+(n+1) by omega]

theorem frame (starts : ℕ) (pref : ℕ→ℕ) (m : Memory w) (n a : ℕ)
    (h : a < starts ∨ starts+(n+1) ≤ a) : image starts pref m n a=m a := by
  simp [image,fillSegment,show ¬(starts ≤ a ∧ a < starts+(n+1)) by omega]

set_option maxRecDepth 8192 in
private theorem trace_row {r k : ℕ} (reg : Fin 6 ↪ Fin r) (pub : Fin 3→Fin k)
    (v : Fin k→Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    let i:=rs (reg 0)
    let curr:=v (pub 1)+i
    ∃ es after, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,after,writeMemory m (curr+1) (m curr.val+m (v (pub 0)+i).val)) ∧
      after (reg 0)=i+1 ∧ after (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem run (counts starts n : ℕ) (pref : ℕ→ℕ) (m : Memory w)
    (sep : counts+n ≤ starts) (fit : starts+n+1<2^w) (first : pref 0=0)
    (step : ∀ i < n, (pref (i+1):Word w)=(pref i:Word w)+m (counts+i)) :
    (exclusive w counts starts n).Exec m (image starts pref m n) (10+(3+12*n)) := by
  have boot : (zero w starts).Exec m (image starts pref m 0) 10 := by
    have same : image starts pref m 0 = fillSegment starts 1 (fun _ => (0:Word w)) m := by
      funext a
      by_cases h : a=starts
      · subst a; simp [image,fillSegment,first]
      · change (if starts ≤ a ∧ a < starts+(0+1) then _ else _)=(if starts ≤ a ∧ a < starts+1 then _ else _)
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
    rw [same]
    have install : (zero w starts).Spec (fun _=>True)
        (fun src dst=>dst=fillSegment starts 1 (fun _=>0) src) 10 :=
      PhysicalInputPhases.writing_spec (.literal 0 : Term w 0 1) Fin.elim0 starts 1
        (by omega) (fun _=>True) (fun _=>0) (by intros; exact Term.eval_literal ..)
    intro P R K mach pc reg pub exit code data cfg raw enter eq
    subst raw
    exact install mach pc reg pub exit code data cfg m enter trivial
  apply boot.then
  intro P R K M pc reg pub exit rom data cfg init entry eq
  subst init
  change Fin 6 ↪ Fin R at reg
  change Fin 3 → Fin K at pub
  change ∀ i, M.publicData (pub i)=values w counts starts n i at data
  obtain ⟨z,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 2 M pc reg pub exit rom n
    (by omega) (data 2) (image starts pref m) (by
      intro t ht state rs cur limit
      let mem := image starts pref m t
      obtain ⟨es,rs',act,inc,keep⟩ := trace_row reg pub M.publicData state rs mem
      refine ⟨es,rs',?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,cur] at act
      change trace _ _ _ _ _ = some (_,_,writeMemory mem (((starts:Word w)+(t:Word w))+1)
        (mem ((starts:Word w)+(t:Word w)).val+mem ((counts:Word w)+(t:Word w)).val)) at act
      have hcur : ((starts:Word w)+(t:Word w)).val=starts+t := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
      have hval : ((counts:Word w)+(t:Word w)).val=counts+t := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
      have summands : mem (starts+t)+mem (counts+t)=(pref (t+1):Word w) := by
        dsimp only [mem]
        rw [read starts pref m t t le_rfl,frame starts pref m t (counts+t) (.inl (by omega))]
        exact (step t ht).symm
      rw [hcur,hval,summands] at act
      have next : writeMemory mem (((starts:Word w)+(t:Word w))+1) (pref (t+1):Word w)=
          image starts pref m (t+1) := by
        have addr : (((starts:Word w)+(t:Word w))+1).val=starts+t+1 := by
          rw [←Nat.cast_add,←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
        funext a
        by_cases last : a=starts+t+1
        · subst a
          simp [writeMemory,addr,image,fillSegment,show starts ≤ starts+t+1 by omega,
            show starts+t+1 < starts+(t+1+1) by omega,show starts+t+1-starts=t+1 by omega]
        · have iff : (starts ≤ a ∧ a < starts+(t+1)) ↔ (starts ≤ a ∧ a < starts+(t+1+1)) := by omega
          simp [writeMemory,addr,last,mem,image,fillSegment,iff]
      rwa [next] at act) cfg entry
  exact ⟨_,by change 3+n*12≤3+12*n; omega,z,_,advance,stop,rfl⟩


end Hierarchy.ProtocolRAMEndpointPrefix

end OAI
