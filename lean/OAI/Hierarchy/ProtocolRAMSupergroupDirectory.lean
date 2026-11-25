import OAI.Hierarchy.ProtocolRAMSupergroupPorts
import OAI.Hierarchy.TaggedShorterSupergroups
import Mathlib.Data.Nat.Log

namespace OAI
/-! # The immutable two-column ROM of an actual next-fit supergroup directory -/

namespace Hierarchy.ProtocolRAMSupergroupDirectory

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM TaggedShorterSupergroups
open scoped Fin.CommRing

variable {W K N H lanes : ℕ} {G : Type*} {size : G→ℕ}

def bits (K : ℕ) := Nat.log 2 (K+1)+1
def span (K : ℕ) := 2^bits K

theorem slotFits (K : ℕ) : K < span K :=
  (Nat.lt_succ_self K).trans (Nat.lt_pow_succ_log_self (by decide) _)

theorem space (K : ℕ) : 2*span K≤4*(K+1) := by
  have old := Nat.pow_log_le_self 2 (show K+1≠0 by omega)
  unfold span bits
  rw [pow_succ]
  omega

def groupBank (start K : ℕ) : Bank := ⟨start,bits K⟩
def offsetBank (start K : ℕ) : Bank := ⟨start+span K,bits K⟩

def store (start : ℕ) (value : Fin K→ℕ) (mem : Memory W) :=
  fillSegment start (span K) (fun a=>if h : a-start < K then (value ⟨a-start,h⟩:Word W) else 0) mem

def mount (start lanes : ℕ) (groups : Fin K≃G) (dir : Directory size H) (mem : Memory W) :=
  store (start+span K) (fun i=>dir.base (groups i)*lanes)
    (store start (fun i=>(dir.group (groups i)).val) mem)

theorem store_read (start : ℕ) (value : Fin K→ℕ) (mem : Memory W) (i : Fin K) :
    store start value mem (start+i.val)=(value i:Word W) := by
  have inside := i.isLt.trans (slotFits K)
  simp [store,fillSegment,show start+i.val < start+span K by omega,i.isLt]

theorem resident (start lanes : ℕ) (groups : Fin K≃G) (dir : Directory size H)
    (mem : Memory W) (fit : K≤2^W) (g : G) :
    (groupBank start K).read (mount start lanes groups dir mem) ((groups.symm g).val:Word W)=
        ((dir.group g).val:Word W) ∧
      (offsetBank start K).read (mount start lanes groups dir mem) ((groups.symm g).val:Word W)=
        ((dir.base g*lanes:ℕ):Word W) := by
  let i := groups.symm g
  have small : i.val<2^W := i.isLt.trans_le fit
  have inside : i.val < span K := i.isLt.trans (slotFits K)
  change mount start lanes groups dir mem (start+(i.val:Word W).val%span K)=_ ∧
    mount start lanes groups dir mem (start+span K+(i.val:Word W).val%span K)=_
  rw [Fin.val_cast_of_lt small,Nat.mod_eq_of_lt inside]
  constructor
  · have off : ¬(start+span K ≤ start+i.val ∧ start+i.val < start+span K+span K) := by omega
    change (if start+span K ≤ start+i.val ∧ start+i.val < start+span K+span K then _
      else store start (fun k=>(dir.group (groups k)).val) mem (start+i.val))=_
    rw [ite_eq_right off,store_read]
    simp [i]
  · rw [mount,store_read]
    simp [i]

theorem frame (start lanes : ℕ) (groups : Fin K≃G) (dir : Directory size H) (mem : Memory W)
    (a : ℕ) (outside : a < start ∨ start+2*span K ≤ a) : mount start lanes groups dir mem a=mem a := by
  have first : ¬(start ≤ a ∧ a < start+span K) := by omega
  have second : ¬(start+span K ≤ a ∧ a < start+span K+span K) := by omega
  simp [mount,store,fillSegment,first,second]

theorem read_slots (groupOut baseOut start lanes : ℕ) (groups : Fin K≃G)
    (dir : Directory size H) (localBase : Bank) (old : Expr) (mem : Memory W)
    (owner : Fin N→G) (port : (i : Fin N)→Fin (size (owner i))) (fit : K≤2^W)
    (low : old.Fits W groupOut) (bf : (offsetBank start K).Fits W groupOut) (lf : localBase.Fits W groupOut)
    (separate : groupOut+N ≤ baseOut)
    (oldData : ∀ i,old.eval (mount start lanes groups dir mem) (i.val:Word W)=((groups.symm (owner i)).val:Word W))
    (baseData : ∀ i,localBase.read (mount start lanes groups dir mem) (i.val:Word W)=(((port i).val*lanes:ℕ):Word W))
    (i : Fin N) :
    let result := ProtocolRAMSupergroupPorts.image N groupOut baseOut (groupBank start K) (offsetBank start K)
      localBase old (mount start lanes groups dir mem)
    result (groupOut+i.val)=((dir.group (owner i)).val:Word W) ∧
      result (baseOut+i.val)=(((dir.slot (owner i) (port i)).val*lanes:ℕ):Word W) :=
  ProtocolRAMSupergroupPorts.read groupOut baseOut _ _ _ _ _ (fun g=>(groups.symm g).val) owner
    (fun g=>(dir.group g).val) dir.base (fun j=>(port j).val) low bf lf separate oldData
    (fun g=>(resident start lanes groups dir mem fit g).1) (fun g=>(resident start lanes groups dir mem fit g).2)
    baseData i


end Hierarchy.ProtocolRAMSupergroupDirectory

end OAI
