import OAI.Hierarchy.GridThroughIdle
import OAI.Hierarchy.UniversalTick
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # The identity selector's direct rail allocation and accepting program -/

noncomputable section
namespace Hierarchy.GridIdleLayout
open ThreeFlat Diagonal RAM GridThrough GridLens
open Computability.VPVNP.BurstRAM
open scoped Classical BigOperators

variable {m n B p : ℕ}
abbrev each (m n B : ℕ) := 2*(n+1)^m*B
abbrev Rails (m n B : ℕ) := Fin ((m+1)*each m n B)
abbrev Line (m n : ℕ) := Fin m → Fin (n+1)

/-- Higher digits encode the direction and transverse line. The low digit
names one of the two banks of B rails on that line. -/
def ordinal (m n B : ℕ) : (Fin (m+1) × (Line m n × Fin (2*B))) ≃ Rails m n B :=
  let line := (Equiv.prodCongr finFunctionFinEquiv (Equiv.refl (Fin (2*B)))).trans finProdFinEquiv
  ((Equiv.prodCongr (Equiv.refl _) line).trans finProdFinEquiv).trans
    (finCongr (by dsimp [each]; ring))

def direction (e : Rails m n B) : Fin (m+1) := ((ordinal m n B).symm e).1

def row (e : Rails m n B) : Cell (m+1) n :=
  let a := (ordinal m n B).symm e
  a.1.insertNth (α:=fun _ => Fin (n+1)) 0 a.2.1

theorem direction_val (e : Rails m n B) : (direction e).val=e.val/each m n B := by
  change e.val/((n+1)^m*(2*B)) = e.val/_
  congr 1
  dsimp [each]
  ring

/-- Insertion of a zero radix digit at the direction is computed from a
remainder, a quotient and the public power of the radix. -/
theorem insert_zero (j : Fin (m+1)) (f : Line m n) :
    (finFunctionFinEquiv (j.insertNth (α:=fun _ => Fin (n+1)) 0 f)).val =
      let z := (finFunctionFinEquiv f).val
      let p := (n+1)^j.val
      z%p + (z/p)*(p*(n+1)) := by
  let g := n+1
  let p := g^j.val
  let low := Finset.univ.filter (fun i : Fin m => i.val<j.val)
  let high := Finset.univ.filter (fun i : Fin m => ¬i.val<j.val)
  let z (i : Fin m) := (f i).val*g^i.val
  let lo := ∑ i ∈ low,z i
  let hi := ∑ i ∈ high,(f i).val*g^(i.val-j.val)
  have jp : j.val ≤ m := Nat.le_of_lt_succ j.isLt
  have loEq : lo=(finFunctionFinEquiv (fun a : Fin j.val => f (a.castLE jp))).val := by
    rw [finFunctionFinEquiv_apply]
    apply Finset.sum_bij (fun i h => (⟨i.val,(Finset.mem_filter.mp h).2⟩ : Fin j.val))
    · intros; exact Finset.mem_univ _
    · intro _ _ _ _ h
      exact Fin.ext (congrArg (fun a : Fin j.val => a.val) h)
    · intro a _
      exact ⟨a.castLE jp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.isLt⟩,rfl⟩
    · intros; rfl
  have lo_lt : lo<p := loEq.trans_lt (finFunctionFinEquiv _).isLt
  have upper : (∑ i ∈ high,z i)=p*hi := by
    dsimp only [hi]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i ih
    have le : j.val ≤ i.val := Nat.le_of_not_gt (Finset.mem_filter.mp ih).2
    dsimp only [p,z]
    rw [mul_left_comm (g^j.val) _ _,←pow_add,Nat.add_sub_of_le le]
  have splitDigits (h : Fin m → ℕ) : (∑ i,h i)=(∑ i∈low,h i)+(∑ i∈high,h i) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
  have base : (finFunctionFinEquiv f).val=lo+p*hi :=
    (splitDigits z).trans (congrArg (lo+·) upper)
  have total : (finFunctionFinEquiv (j.insertNth (α:=fun _=>Fin (n+1)) 0 f)).val =
      lo+g*(p*hi) := by
    rw [finFunctionFinEquiv_apply,Fin.sum_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same,Fin.val_zero,zero_mul,zero_add,Fin.insertNth_apply_succAbove]
    rw [splitDigits,←upper,Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i member
      have h : i.castSucc<j := (Finset.mem_filter.mp member).2
      simp [Fin.succAbove,h,z,g]
    · apply Finset.sum_congr rfl
      intro i member
      have h : ¬i.castSucc<j := (Finset.mem_filter.mp member).2
      simp [Fin.succAbove,h,z,g,pow_succ,mul_left_comm,mul_comm]
  change _ = (finFunctionFinEquiv f).val%p + ((finFunctionFinEquiv f).val/p)*(p*g)
  rw [total,base,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lo_lt,Nat.add_mul_div_left _ _
    (Nat.pow_pos (Nat.succ_pos _)),Nat.div_eq_of_lt lo_lt,zero_add]
  ring

theorem row_val (e : Rails m n B) :
    (finFunctionFinEquiv (row e)).val =
      let d := e.val/each m n B
      let z := (e.val%each m n B)/(2*B)
      let p := (n+1)^d
      z%p+(z/p)*(p*(n+1)) := by
  let a := (ordinal m n B).symm e
  have line : (finFunctionFinEquiv a.2.1).val = (e.val%each m n B)/(2*B) := by
    change (finFunctionFinEquiv (finFunctionFinEquiv.symm _)).val=_
    rw [Equiv.apply_symm_apply]
    change (e.val%((n+1)^m*(2*B)))/(2*B) = _
    rw [show (n+1)^m*(2*B)=each m n B from by dsimp [each]; ring]
  change (finFunctionFinEquiv (a.1.insertNth (α:=fun _=>Fin (n+1)) 0 a.2.1)).val=_
  simp only [insert_zero,line,show a.1.val=e.val/each m n B from direction_val e]

private theorem line_eq (j : Fin (m+1)) (x : Cell (m+1) n) :
    cellOnRail j (j.insertNth (α:=fun _ => Fin (n+1)) 0 (j.removeNth x)) (x j) = x := by
  calc
    _ = j.insertNth (α:=fun _ => Fin (n+1)) (x j) (j.removeNth x) := by
      rw [← Fin.update_insertNth (α:=fun _ => Fin (n+1)) j 0 (x j) (j.removeNth x)]
      funext i
      by_cases h : i=j
      · simp [cellOnRail,h]
      · simp [cellOnRail,h]
    _ = x := Fin.insertNth_self_removeNth j x

theorem room (width : Fin (m+1) → ℕ) (reserved : ∀ j,width j≤B) (x : Cell (m+1) n) (j : Fin (m+1)) :
    width j≤(untouchedRails (direction (n:=n) (B:=B)) row (fun _=>none) x j).card := by
  let emb (i : Fin (width j)) : untouchedRails (direction (n:=n) (B:=B)) row (fun _=>none) x j :=
    ⟨ordinal m n B (j,j.removeNth x,i.castLE (by have := reserved j; omega)), by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp [direction],by simpa [row] using line_eq j x,by simp⟩⟩
  have hi : Function.Injective emb := by
    intro i i' eq
    apply Fin.ext
    exact congrArg (fun a : Fin (m+1) × (Line m n × Fin (2*B)) => a.2.2.val)
      ((ordinal m n B).injective (congrArg Subtype.val eq))
  simpa using Fintype.card_le_of_injective emb hi

def program (width : Fin (m+1) → ℕ) (reserved : ∀ j,width j≤B) (literal : Fin p → Bool) :
    Program (Rails m n B) n p width :=
  Program.ofUntouched direction row (fun _=>none) width (room width reserved)
    (fun _ i => .inr (literal i)) (fun _ _ _ h => by cases h) (fun z => by cases z.1.property)

@[simp] theorem data (width : Fin (m+1) → ℕ) (reserved : ∀ j,width j≤B) (literal : Fin p → Bool)
    (x : GridDiagonal.Pins (Rails m n B)) (c : Cell (m+1) n) :
    (program width reserved literal).dataBits x c=literal := rfl

variable {w pc r K q S : ℕ}

def literal (hp : 0<pc) (i : Fin (q*S)) : Bool :=
  TraceBitHeader.advicePins 0 (NativeTrace.executable (UniversalTick.accept (64*w) pc r K hp))
    (fun _=>false) (finProdFinEquiv.symm i).2

theorem ticks_one {F : Type*} [Field F] [Fintype F] (hp : 0<pc)
    (fit : NativeTrace.Fits (UniversalTick.accept (64*w) pc r K hp) S 0
      (UniversalTick.depth w UniversalTick.saving) (UniversalTick.clock w UniversalTick.saving))
    (hf : Fintype.card F≤2^(64*w)) (st : Word (64*w))
    (width : Fin (m+1) → ℕ) (reserved : ∀ j,width j≤B)
    (x : GridDiagonal.Pins (Rails m n B)) (c : Cell (m+1) n) :
    Catalyst.tickProduct (UniversalTick.tick hf fit.width fit.labels 0 st fit.header fit.time r K) q
      ((program width reserved (literal (w:=w) (r:=r) (K:=K) hp)).dataBits x c)=1 := by
  rw [data]
  apply Finset.prod_eq_one
  intro j _
  simpa [literal] using UniversalTick.runs_one hp fit hf st (fun _=>false)

end Hierarchy.GridIdleLayout
end

end OAI
