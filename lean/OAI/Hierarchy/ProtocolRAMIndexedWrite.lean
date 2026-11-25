import OAI.ThreeFlat.RAM.OrdinalOpLoop

namespace OAI
/-! # Native scatter from parallel destination and value columns -/

namespace Hierarchy.ProtocolRAMIndexedWrite

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w n : ℕ}

def ops : List (Op 5 3) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,
   .publicWord 3 1,.binary .add 3 3 0,.read 3 3,.write 2 3,
   .constant 4 1,.binary .add 0 0 4]

def values (w addresses words n : ℕ) : Fin 3 → Word w := ![addresses,words,n]

def scatter (w addresses words n : ℕ) : Procedure w :=
  ⟨12,5,3,OrdinalOpLoop.block w ops 0 1 2,values w addresses words n⟩

def image (address : Fin n → ℕ) (word : Fin n → Word w) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | t+1 => if h : t<n then Function.update (image address word m t) (address ⟨t,h⟩) (word ⟨t,h⟩)
             else image address word m t

theorem frame (address : Fin n → ℕ) (word : Fin n → Word w) (m : Memory w) (t a : ℕ)
    (away : ∀ i, a ≠ address i) : image address word m t a=m a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t<n
    · simpa only [image,dite_eq_left ht,Function.update_of_ne (away ⟨t,ht⟩)] using ih
    · simpa [image,ht] using ih

theorem read_unique (address : Fin n → ℕ) (word : Fin n → Word w) (m : Memory w)
    (inj : Function.Injective address) (t : ℕ) (ht : t≤n) (i : Fin n) (hi : i.val<t) :
    image address word m t (address i)=word i := by
  induction t with
  | zero => omega
  | succ t ih =>
    have live : t<n := by omega
    let row : Fin n := ⟨t,live⟩
    by_cases last : i=row
    · subst i
      simp only [image,dite_eq_left live,Function.update_self,row]
    · have ne : address i ≠ address ⟨t,live⟩ := inj.ne last
      have earlier : i.val<t := by
        have h : i.val≠t := fun e => last (Fin.ext e)
        omega
      simpa only [image,dite_eq_left live,Function.update_of_ne ne] using ih (by omega) earlier

set_option maxRecDepth 8192 in
private theorem trace_row {r k : ℕ} (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k)
    (v : Fin k → Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    let i:=rs (reg 0)
    ∃ es after, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,after,writeMemory m (m (v (pub 0)+i).val) (m (v (pub 1)+i).val)) ∧
      after (reg 0)=i+1 ∧ after (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem run (addresses words : ℕ) (address : Fin n → ℕ) (word : Fin n → Word w)
    (endA : addresses+n<2^w) (endW : words+n<2^w)
    (fit : ∀ i, address i<2^w)
    (safeA : ∀ i j : Fin n, addresses+i.val ≠ address j)
    (safeW : ∀ i j : Fin n, words+i.val ≠ address j) :
    (scatter w addresses words n).Spec
      (fun m => ∀ i, m (addresses+i.val)=(address i : Word w) ∧ m (words+i.val)=word i)
      (fun m result => result=image address word m n) (3+10*n) := by
  intro pcs regs pubs M pc reg pub exit rom data cfg m entry loaded
  change Fin 5 ↪ Fin regs at reg
  change Fin 3 → Fin pubs at pub
  change ∀ i, M.publicData (pub i)=values w addresses words n i at data
  obtain ⟨z,adv,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 2 M pc reg pub exit rom n
    (by omega) (data 2) (image address word m) (by
      intro t ht state rs cur limit
      let i : Fin n := ⟨t, ht⟩
      let mem := image address word m t
      obtain ⟨es,rs',act,inc,keep⟩ := trace_row reg pub M.publicData state rs mem
      refine ⟨es,rs',?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,cur] at act
      change trace _ _ _ _ _ = some (_,_,writeMemory mem
        (mem ((addresses:Word w)+(t:Word w)).val) (mem ((words:Word w)+(t:Word w)).val)) at act
      have dst : mem ((addresses:Word w)+(t:Word w)).val=(address i:Word w) := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega : addresses+t<2^w)]
        exact (frame address word m t (addresses+t) (safeA i)).trans (loaded i).1
      have val : mem ((words:Word w)+(t:Word w)).val=word i := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega : words+t<2^w)]
        exact (frame address word m t (words+t) (safeW i)).trans (loaded i).2
      rw [dst,val] at act
      have next : writeMemory mem (address i:Word w) (word i) = image address word m (t+1) := by
        funext a
        simp only [writeMemory,Fin.val_cast_of_lt (fit i),image,dite_eq_left ht,Function.update_apply,i,mem]
      rwa [next] at act) cfg entry
  exact ⟨_,by change 3+n*10≤3+10*n; omega,z,_,adv,stop,rfl⟩


end Hierarchy.ProtocolRAMIndexedWrite

end OAI
