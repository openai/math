import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import OAI.Hierarchy.TaggedShorterCheapCPU
import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Adding a tape of weighted occurrences to installed edge loads -/

namespace Hierarchy.ProtocolRAMWeightedScatter

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators

variable {w n : ℕ}

def ops : List (Op 6 2) :=
  [.publicWord 2 0, .binary .add 2 2 0, .binary .add 2 2 0, .read 3 2,
   .constant 4 1, .binary .add 2 2 4, .read 2 2, .read 5 3,
   .binary .add 5 5 2, .write 3 5, .binary .add 0 0 4]

def params (w src n : ℕ) : Fin 2 → Word w := ![src,n]

def program (w src n : ℕ) : Procedure w :=
  ⟨14,6,2,OrdinalOpLoop.block w ops 0 1 1,params w src n⟩

def partialLoad (address weight : Fin n → ℕ) (a t : ℕ) :=
  ∑ i : Fin n, if i.val<t ∧ address i=a then weight i else 0

def image (address weight : Fin n → ℕ) (m : Memory w) (t : ℕ) : Memory w :=
  fun a => m a + (partialLoad address weight a t : Word w)

private theorem initial (address weight : Fin n → ℕ) (m : Memory w) :
    image address weight m 0=m := by
  funext a
  simp [image,partialLoad]

theorem frame (address weight : Fin n → ℕ) (m : Memory w) (t a : ℕ)
    (away : ∀ i, address i≠a) : image address weight m t a=m a := by
  simp [image,partialLoad,away]

/-- Total mass of all retained occurrences addressing the same physical cell. -/
def sumAt (address amount : Fin n → ℕ) (a : ℕ) :=
  ∑ i : Fin n, if address i=a then amount i else 0

private theorem partial_le_full (address amount : Fin n → ℕ) (a t : ℕ) :
    partialLoad address amount a t≤sumAt address amount a := by
  unfold partialLoad sumAt
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i.val<t <;> simp [h]

/-- A bound on the full load certifies each individual native addition. -/
theorem read_prefix_nat (address weight : Fin n → ℕ) (m : Memory w) (a t : ℕ)
    (room : (m a).val+(∑ i : Fin n, if address i=a then weight i else 0)<2^w) :
    (image address weight m t a).val=(m a).val+partialLoad address weight a t := by
  have le : partialLoad address weight a t ≤ ∑ i : Fin n, if address i=a then weight i else 0 :=
    partial_le_full address weight a t
  have cast : m a+(partialLoad address weight a t : Word w) =
      (((m a).val+partialLoad address weight a t : ℕ) : Word w) := by
    rw [Nat.cast_add,Fin.cast_val_eq_self]
  rw [image,cast,Fin.val_cast_of_lt (by omega)]

theorem read_nat (address weight : Fin n → ℕ) (m : Memory w) (a : ℕ)
    (room : (m a).val+(∑ i : Fin n, if address i=a then weight i else 0)<2^w) :
    (image address weight m n a).val =
      (m a).val+(∑ i : Fin n, if address i=a then weight i else 0) := by
  simpa only [partialLoad,Fin.is_lt,true_and] using read_prefix_nat address weight m a n room

/-- The two's-complement word emitted by an installed-minus-consumed occurrence. -/
def delta (w : ℕ) (installed consumed : Fin n → ℕ) (i : Fin n) : ℕ :=
  ((installed i : Word w)-(consumed i : Word w)).val

private theorem cast_partial_delta (address installed consumed : Fin n → ℕ) (a t : ℕ) :
    (partialLoad address (delta w installed consumed) a t : Word w) =
      (partialLoad address installed a t : Word w)-(partialLoad address consumed a t : Word w) := by
  simp only [partialLoad,Nat.cast_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : i.val<t ∧ address i=a <;> simp [hit,delta]

/-- The funded total withdrawals and upper capacity bound ensure that each
prefix of the native tape has the correct natural, nonwrapping stock value. -/
theorem read_prefix_balance (address installed consumed : Fin n → ℕ) (m : Memory w) (a t : ℕ)
    (funded : sumAt address consumed a≤(m a).val)
    (room : (m a).val+sumAt address installed a<2^w) :
    (image address (delta w installed consumed) m t a).val+partialLoad address consumed a t =
      (m a).val+partialLoad address installed a t := by
  let I:=partialLoad address installed a t
  let C:=partialLoad address consumed a t
  have paid : C≤(m a).val := (partial_le_full address consumed a t).trans funded
  have bounded : I≤sumAt address installed a := partial_le_full address installed a t
  have can : C≤(m a).val+I := by omega
  have top : (m a).val+I-C<2^w := by omega
  have val : image address (delta w installed consumed) m t a=(((m a).val+I-C:ℕ):Word w) := by
    rw [image,cast_partial_delta,Nat.cast_sub can,Nat.cast_add,Fin.cast_val_eq_self]
    dsimp only [I,C]
    abel
  rw [val,Fin.val_cast_of_lt top]
  change (m a).val+I-C+C=(m a).val+I
  exact Nat.sub_add_cancel can

theorem read_balance (address installed consumed : Fin n → ℕ) (m : Memory w) (a : ℕ)
    (funded : sumAt address consumed a≤(m a).val)
    (room : (m a).val+sumAt address installed a<2^w) :
    (image address (delta w installed consumed) m n a).val+sumAt address consumed a =
      (m a).val+sumAt address installed a := by
  simpa only [partialLoad,sumAt,Fin.is_lt,true_and] using
    read_prefix_balance address installed consumed m a n funded room

/-- The original allocation also bounds the actual post-commit natural word. -/
theorem read_le_allocation (address installed consumed : Fin n → ℕ) (m : Memory w) (a allocation : ℕ)
    (funded : sumAt address consumed a≤(m a).val) (room : (m a).val+sumAt address installed a<2^w)
    (capacity : (m a).val+sumAt address installed a≤allocation+sumAt address consumed a) :
    (image address (delta w installed consumed) m n a).val≤allocation := by
  have h:=read_balance address installed consumed m a funded room
  omega

private theorem advanceLoad (address weight : Fin n → ℕ) (a : ℕ) (i : Fin n) :
    partialLoad address weight a (i.val+1)=partialLoad address weight a i.val+
      if address i=a then weight i else 0 := by
  have split (j : Fin n) :
      (if j.val < i.val+1 ∧ address j=a then weight j else 0) =
        (if j.val < i.val ∧ address j=a then weight j else 0) +
        (if j=i then (if address i=a then weight i else 0) else 0) := by
    by_cases eq : j=i
    · subst j
      simp
    · have neq : j.val≠i.val := fun h => eq (Fin.ext h)
      have same : j.val < i.val+1 ↔ j.val < i.val := by omega
      simp [eq,same]
  unfold partialLoad
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp

set_option maxRecDepth 8192 in
private theorem trace_row {r k : ℕ} (reg : Fin 6 ↪ Fin r) (pub : Fin 2 → Fin k)
    (v : Fin k → Word w) (state : Word w) (rs : Regs w r) (m : Memory w) :
    let p := v (pub 0) + rs (reg 0) + rs (reg 0)
    let a := m p.val
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,writeMemory m a (m a.val + m (p+1).val)) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

/-- Each row contains one absolute destination and the weight to add there.
The output bank may already hold purchased capacities and destinations may repeat. -/
theorem run (src : ℕ) (address weight : Fin n → ℕ) (m : Memory w)
    (tape : src+2*n≤2^w) (bounded : ∀ i, address i<2^w)
    (disjoint : ∀ i, address i<src ∨ src+2*n≤address i)
    (loaded : ∀ i, m (src+2*i.val)=(address i:Word w) ∧
      m (src+2*i.val+1)=(weight i:Word w)) :
    (program w src n).Exec m (image address weight m n) (3+12*n) := by
  intro pcs regs pubs M pc reg pub exit rom data cfg mem entry hm
  subst mem
  change Fin 6 ↪ Fin regs at reg
  change Fin 2 → Fin pubs at pub
  change ∀ i, M.publicData (pub i)=params w src n i at data
  have countFit : n<2^w := by have := Nat.two_pow_pos w; omega
  obtain ⟨out,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 1 M pc reg pub exit rom n
    countFit (data 1) (image address weight m) (by
      intro t ht state rs cur limit
      let i : Fin n:=⟨t,ht⟩
      let prior := image address weight m t
      obtain ⟨es,z,act,inc,keep⟩ := trace_row reg pub M.publicData state rs prior
      refine ⟨es,z,?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,cur] at act
      let p := ((src:Word w)+(t:Word w))+(t:Word w)
      change trace _ _ _ _ _ = some (_,_,writeMemory prior (prior p.val)
        (prior (prior p.val).val+prior (p+1).val)) at act
      have pos : p=((src+2*t : ℕ):Word w) := by
        dsimp only [p]
        rw [←Nat.cast_add,←Nat.cast_add,show src+t+t=src+2*t by omega]
      have pval : p.val=src+2*t := by rw [pos,Fin.val_cast_of_lt (by omega)]
      have qval : (p+1).val=src+2*t+1 := by
        rw [pos,←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
      have atA : prior p.val=(address i : Word w) := by
        rw [pval]
        exact (frame address weight m t (src+2*t) (fun j => by have := disjoint j; omega)).trans (loaded i).1
      have atV : prior (p+1).val=(weight i : Word w) := by
        rw [qval]
        exact (frame address weight m t (src+2*t+1) (fun j => by have := disjoint j; omega)).trans (loaded i).2
      rw [atA,atV,Fin.val_cast_of_lt (bounded i)] at act
      have writes : writeMemory prior (address i : Word w)
          (prior (address i)+(weight i:Word w)) = image address weight m (t+1) := by
        funext a
        change writeMemory prior _ _ a=image address weight m (i.val+1) a
        simp only [writeMemory,Fin.val_cast_of_lt (bounded i),image,advanceLoad,Nat.cast_add]
        by_cases same : a=address i
        · subst a
          simp [prior,image,add_assoc]; rfl
        · simp [same,Ne.symm same,prior,image]; rfl
      rwa [writes] at act) cfg entry
  rw [initial] at advance
  exact ⟨_,by change 3+n*12≤3+12*n; omega,out,_,advance,stop,rfl⟩

set_option maxRecDepth 8192 in
theorem cheap (w src n : ℕ) :
    ∀ {P R K : ℕ} (pc : Fin (program w src n).labels ↪ Fin P)
      (reg : Fin (program w src n).registers ↪ Fin R)
      (pub : Fin (program w src n).slots → Fin K) (exit : Fin P)
      (i : Fin (program w src n).labels),
      TaggedShorterCheapCPU.Cheap ((program w src n).block.emit pc reg pub exit i) := by
  intro P R K pc reg pub exit i
  change Fin 14 at i
  fin_cases i <;> exact True.intro

end Hierarchy.ProtocolRAMWeightedScatter

end OAI
