import OAI.Hierarchy.ProtocolRAMIndexedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # A segmented native walk over the chronological terminal occurrences -/

namespace Hierarchy.ProtocolRAMTurnWalk

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing

variable {W N : ℕ}

/-- Read the predecessor word, subtract it from the current endpoint sum, and store
the new site. Segment starts address a reserved zero word and supply their old
source site as the sum. No word stores a data-dependent prefix before execution. -/
def ops : List (Op 5 4) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,.read 2 2,
   .publicWord 3 1,.binary .add 3 3 0,.read 3 3,.binary .sub 3 3 2,
   .publicWord 2 2,.binary .add 2 2 0,.write 2 3,.constant 4 1,.binary .add 0 0 4]

def values (W pointers sums dst N : ℕ) : Fin 4 → Word W := ![pointers,sums,dst,N]

def program (W pointers sums dst N : ℕ) : Procedure W :=
  ⟨16,5,4,OrdinalOpLoop.block W ops 0 1 3,values W pointers sums dst N⟩

abbrev Before (i : Fin N) := Option (Fin i.val)

def previous (i : Fin N) (j : Fin i.val) : Fin N := ⟨j.val,j.isLt.trans i.isLt⟩

def pointer (dst initial : ℕ) (i : Fin N) : Before i → ℕ
  | none => initial
  | some j => dst+j.val

def carried (site : Fin N → Word W) (i : Fin N) : Before i → Word W
  | none => 0
  | some j => site (previous i j)

def image (dst : ℕ) (site : Fin N → Word W) (m : Memory W) (t : ℕ) : Memory W :=
  ProtocolRAMIndexedWrite.image (fun i : Fin N=>dst+i.val) site m t

theorem site_read (dst : ℕ) (site : Fin N → Word W) (m : Memory W) (t : ℕ) (ht : t ≤ N)
    (i : Fin N) (hi : i.val < t) : image dst site m t (dst+i.val)=site i := by
  apply ProtocolRAMIndexedWrite.read_unique _ _ _ _ t ht i hi
  intro a b h
  exact Fin.ext (Nat.add_left_cancel h)

theorem frame (dst : ℕ) (site : Fin N → Word W) (m : Memory W) (t a : ℕ)
    (out : a < dst ∨ dst+N ≤ a) : image dst site m t a=m a := by
  apply ProtocolRAMIndexedWrite.frame
  intro i
  have := i.isLt
  omega

set_option maxRecDepth 8192 in
private theorem row {R K : ℕ} (reg : Fin 5 ↪ Fin R) (pub : Fin 4 → Fin K)
    (v : Fin K → Word W) (state : Word W) (rs : Regs W R) (m : Memory W) :
    let i := rs (reg 0)
    ∃ es after, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,after,writeMemory m (v (pub 2)+i)
        (m (v (pub 1)+i).val-m (m (v (pub 0)+i).val).val)) ∧
      after (reg 0)=i+1 ∧ after (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem run (pointers sums dst initial : ℕ) (site : Fin N → Word W) (prev : (i : Fin N) → Before i)
    (m : Memory W) (pLow : pointers+N ≤ dst) (sLow : sums+N ≤ dst) (zLow : initial < dst)
    (enough : dst+N < 2^W) (zeroAt : m initial=0)
    (pointerAt : ∀ i : Fin N,m (pointers+i.val)=(pointer dst initial i (prev i):Word W))
    (sumAt : ∀ i : Fin N,m (sums+i.val)=site i+carried site i (prev i)) :
    (program W pointers sums dst N).Exec m (image dst site m N) (3+14*N) := by
  intro P R K M pc reg pub exit rom data cfg raw entry same
  subst raw
  change Fin 5 ↪ Fin R at reg
  change Fin 4 → Fin K at pub
  change ∀ i,M.publicData (pub i)=values W pointers sums dst N i at data
  obtain ⟨z,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 3 M pc reg pub exit rom N
    (by omega) (data 3) (image dst site m) (by
      intro t ht state rs cur limit
      let i : Fin N := ⟨t,ht⟩
      let mem := image dst site m t
      obtain ⟨es,rs',act,inc,keep⟩ := row reg pub M.publicData state rs mem
      refine ⟨es,rs',?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,data 2,cur] at act
      change trace _ _ _ _ _ = some (_,_,writeMemory mem ((dst:Word W)+(t:Word W))
        (mem ((sums:Word W)+(t:Word W)).val-mem (mem ((pointers:Word W)+(t:Word W)).val).val)) at act
      have p : mem ((pointers:Word W)+(t:Word W)).val=(pointer dst initial i (prev i):Word W) := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
        exact (frame dst site m t _ (.inl (by omega))).trans (pointerAt i)
      have s : mem ((sums:Word W)+(t:Word W)).val=site i+carried site i (prev i) := by
        rw [←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
        exact (frame dst site m t _ (.inl (by omega))).trans (sumAt i)
      have prior : mem (pointer dst initial i (prev i):Word W).val=carried site i (prev i) := by
        cases h : prev i with
        | none =>
          change mem (initial:Word W).val=0
          rw [Fin.val_cast_of_lt (by omega)]
          exact (frame dst site m t _ (.inl zLow)).trans zeroAt
        | some j =>
          change mem ((dst+j.val:ℕ):Word W).val=site (previous i j)
          have hlt : j.val < t := j.isLt
          rw [Fin.val_cast_of_lt (by omega)]
          exact site_read dst site m t ht.le (previous i j) hlt
      rw [p,s,prior,add_sub_cancel_right] at act
      have next : writeMemory mem ((dst:Word W)+(t:Word W)) (site i)=image dst site m (t+1) := by
        funext a
        simp only [writeMemory,←Nat.cast_add,Fin.val_cast_of_lt (by omega : dst+t < 2^W),image,
          ProtocolRAMIndexedWrite.image,dite_eq_left ht,Function.update_apply,mem,i]
      rwa [next] at act) cfg entry
  exact ⟨_,by change 3+N*14≤3+14*N;omega,z,_,advance,stop,rfl⟩

set_option maxRecDepth 8192 in
theorem cheap (W pointers sums dst N : ℕ) : CheapCode (program W pointers sums dst N) := by
  intro P R K pc reg pub exit i
  change Fin 16 at i
  fin_cases i <;> trivial

end Hierarchy.ProtocolRAMTurnWalk

end OAI
