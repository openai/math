import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.Computability.BorderVNP.FragmentBucketOrder

namespace OAI
/-! # Stable scatter of original row numbers into their endpoint-site buckets -/

namespace Hierarchy.ProtocolRAMEndpointScatter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open Computability.BorderVNP.FragmentBucket
open scoped Fin.CommRing

variable {w n sites : ℕ}

/-- Load the site key and its next free slot, publish the original ordinal at that slot,
then advance the site's cursor and the input cursor. -/
def ops : List (Op 7 4) :=
  [.publicWord 2 0, .binary .add 2 2 0, .read 2 2,
   .publicWord 3 1, .binary .add 3 3 2, .read 4 3,
   .publicWord 5 2, .binary .add 5 5 4, .write 5 0,
   .constant 6 1, .binary .add 4 4 6, .write 3 4, .binary .add 0 0 6]

def values (w src bins out n : ℕ) : Fin 4 → Word w := ![src,bins,out,n]

def scatter (w src bins out n : ℕ) : Procedure w :=
  ⟨16,7,4,OrdinalOpLoop.block w ops 0 1 3, values w src bins out n⟩

def image (site : Fin n → Fin sites) (bins out : ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | t+1 =>
    let prev := image site bins out m t
    if h : t < n then
      let i : Fin n := ⟨t,h⟩
      let bucket := bins+(site i).val
      fun a => if a=bucket then prev bucket+1
        else if a=out+(dest site i).val then (t : Word w) else prev a
    else prev

private theorem image_at (site : Fin n → Fin sites) (bins out : ℕ) (m : Memory w)
    (i : Fin n) (a : ℕ) :
    image site bins out m (i.val+1) a =
      if a = bins+(site i).val then image site bins out m i.val (bins+(site i).val)+1
      else if a = out+(dest site i).val then (i.val:Word w) else image site bins out m i.val a := by
  simp only [image,dite_eq_left i.isLt,Fin.eta]

theorem frame (site : Fin n → Fin sites) (bins out : ℕ) (m : Memory w) (t a : ℕ)
    (hb : a < bins ∨ bins+sites ≤ a) (ho : a < out ∨ out+n ≤ a) :
    image site bins out m t a=m a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < n
    · let i : Fin n := ⟨t,ht⟩
      have hb' : a ≠ bins+(site i).val := by have := (site i).isLt; omega
      have ho' : a ≠ out+(dest site i).val := by have := (dest site i).isLt; omega
      rw [image_at site bins out m i a,ite_eq_right hb',ite_eq_right ho']
      exact ih
    · simpa [image, ht] using ih

theorem cursor (site : Fin n → Fin sites) (bins out : ℕ) (m : Memory w)
    (sep : bins+sites ≤ out) (initial : ∀ s : Fin sites, m (bins+s.val)=(start site s.val : Word w))
    (t : ℕ) (ht : t ≤ n) (s : Fin sites) :
    image site bins out m t (bins+s.val)=((start site s.val+prior site t s : ℕ) : Word w) := by
  induction t with
  | zero => simpa only [image, prior_zero, add_zero] using initial s
  | succ t ih =>
    have live : t < n := by omega
    let i : Fin n := ⟨t,live⟩
    have away : bins+s.val ≠ out+(dest site i).val := by have := s.isLt; omega
    have step := prior_step site i s
    change prior site (t+1) s=prior site t s + if site i=s then 1 else 0 at step
    rw [step]
    by_cases hs : site i=s
    · have eqn : bins+s.val=bins+(site i).val := by rw [hs]
      rw [image_at site bins out m i _,ite_eq_left eqn,ite_eq_left hs,←eqn,ih (by omega)]
      simp [Nat.cast_add,add_assoc]
    · have ne : bins+s.val≠bins+(site i).val := by
        intro h
        exact hs (Fin.ext (by omega))
      rw [image_at site bins out m i _,ite_eq_right ne,ite_eq_right away,ite_eq_right hs,add_zero]
      exact ih (by omega)

theorem sorted (site : Fin n → Fin sites) (bins out : ℕ) (m : Memory w)
    (sep : bins+sites ≤ out) (t : ℕ) (ht : t ≤ n) (i : Fin n) (hi : i.val < t) :
    image site bins out m t (out+(dest site i).val)=(i.val : Word w) := by
  induction t with
  | zero => omega
  | succ t ih =>
    have live : t < n := by omega
    let row : Fin n := ⟨t,live⟩
    have away : out+(dest site i).val≠bins+(site row).val := by have := (site row).isLt; omega
    by_cases last : i=row
    · subst i
      simp only [image,dite_eq_left live,ite_eq_right away,ite_true,row]
    · have different : out+(dest site i).val ≠ out+(dest site row).val := by
        intro h
        exact last ((dest site).injective (Fin.ext (by omega)))
      have earlier : i.val < t := by
        have ne : i.val ≠ t := fun h => last (Fin.ext h)
        omega
      rw [image_at site bins out m row _,ite_eq_right away,ite_eq_right different]
      exact ih (by omega) earlier

set_option maxRecDepth 8192 in
private theorem trace_row {r k : ℕ} (reg : Fin 7 ↪ Fin r) (pub : Fin 4 → Fin k)
    (v : Fin k → Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    let i := rs (reg 0)
    let s := m (v (pub 0)+i).val
    let c := v (pub 1)+s
    let z := m c.val
    ∃ es after, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,after,writeMemory (writeMemory m (v (pub 2)+z) i) c (z+1)) ∧
      after (reg 0)=i+1 ∧ after (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

/-- One native loop consumes the original site column and the exclusive site starts.
Every row writes one original row number and one updated cursor. -/
theorem run (site : Fin n → Fin sites) (src bins out : ℕ)
    (safe : src+n ≤ bins) (sep : bins+sites ≤ out) (room : out+n<2^w) :
    (scatter w src bins out n).Spec
      (fun m => (∀ i, m (src+i.val)=((site i).val : Word w)) ∧
        (∀ s : Fin sites, m (bins+s.val)=(start site s.val : Word w)))
      (fun m result => result=image site bins out m n) (3+14*n) := by
  intro pcs regs pubs M pc reg pub exit rom data cfg m entry loaded
  change Fin 7 ↪ Fin regs at reg
  change Fin 4 → Fin pubs at pub
  change ∀ i, M.publicData (pub i)=values w src bins out n i at data
  obtain ⟨z,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 3 M pc reg pub exit rom n
    (by omega) (data 3) (image site bins out m) (by
      intro t ht state rs cur limit
      let i : Fin n := ⟨t,ht⟩
      let mem := image site bins out m t
      obtain ⟨es,rs',act,inc,keep⟩ := trace_row reg pub M.publicData state rs mem
      refine ⟨es,rs',?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,data 2,cur] at act
      change trace _ _ _ _ _ = some (_,_,writeMemory
        (writeMemory mem ((out:Word w)+mem ((bins:Word w)+mem ((src:Word w)+(t:Word w)).val).val) (t:Word w))
        ((bins:Word w)+mem ((src:Word w)+(t:Word w)).val)
        (mem ((bins:Word w)+mem ((src:Word w)+(t:Word w)).val).val+1)) at act
      have key : mem ((src:Word w)+(t:Word w)).val=((site i).val : Word w) := by
        rw [← Nat.cast_add, Fin.val_cast_of_lt (by omega : src+t<2^w)]
        exact (frame site bins out m t (src+t) (.inl (by omega)) (.inl (by omega))).trans (loaded.1 i)
      have fitBin : bins+(site i).val<2^w := by have := (site i).isLt; omega
      have fitOut : out+(dest site i).val<2^w := by have := (dest site i).isLt; omega
      have pos : mem (bins+(site i).val)=((dest site i).val : Word w) := by
        rw [dest_val]
        exact cursor site bins out m sep loaded.2 t (by omega) (site i)
      rw [key, ← Nat.cast_add, Fin.val_cast_of_lt fitBin, pos, ← Nat.cast_add] at act
      have upd : writeMemory (writeMemory mem ((out+(dest site i).val : ℕ):Word w) (t:Word w))
          ((bins+(site i).val : ℕ):Word w) (((dest site i).val:Word w)+1) =
          image site bins out m (t+1) := by
        funext a
        simp only [writeMemory, Fin.val_cast_of_lt fitBin, Fin.val_cast_of_lt fitOut,
          image, dite_eq_left ht]
        change (if a=bins+(site i).val then _ else _) = (if a=bins+(site i).val then _ else _)
        rw [← pos]
      rwa [upd] at act) cfg entry
  exact ⟨_,by change 3+n*14 ≤ 3+14*n; omega,z,_,advance,stop,rfl⟩


end Hierarchy.ProtocolRAMEndpointScatter

end OAI
