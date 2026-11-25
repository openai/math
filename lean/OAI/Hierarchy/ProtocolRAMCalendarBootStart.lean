import OAI.Hierarchy.ProtocolRAMCalendarMarketTypes
import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMPurchaseCalendarROM
import OAI.Hierarchy.ProbeStageNativeCorrect
import OAI.Hierarchy.ProbeStagePhysicalOrdinal
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # The single subdivision run at the entrance to a finite purchase calendar -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

noncomputable section
variable {z d k jobs : ℕ}
abbrev Tape (z d : ℕ) := Shelf.Mem z d

/-- The threshold table and the per-stage sampler slabs share this event's reserved interval. -/
def low (v : Market z d k) := v.shelf.table.base
def high (v : Market z d k) := v.flags

structure Layout (v : Fin jobs → Market z d k) (size : ℕ) : Prop where
  subdivision : heapEnd z d copies ≤ size
  afterHeap : ∀i, heapEnd z d copies≤low (v i)
  extent : ∀i, high (v i) ≤ size
  threshold : ∀i,(v i).shelf.table.base+(v i).shelf.table.size≤(v i).shelf.firstBase
  apart : ProtocolRAMStaticSlabs.Disjoint (fun i=>low (v i)) (fun i=>high (v i))

theorem Layout.mono {v : Fin jobs→Market z d k} {size larger : ℕ} (h : Layout v size)
    (step : size≤larger) : Layout v larger :=
  ⟨h.subdivision.trans step,h.afterHeap,fun i=>(h.extent i).trans step,h.threshold,h.apart⟩

/-- Each successive controller event can place its live region inside its own arena stride. -/
theorem Layout.of_strides (v : Fin jobs → Market z d k) {size : ℕ} (arena : Arena)
    (first : heapEnd z d copies≤arena.first) (bound : arena.first+jobs*arena.stride ≤ size)
    (starts : ∀i,arena.first+i.val*arena.stride≤low (v i))
    (ends : ∀i,high (v i)≤arena.first+(i.val+1)*arena.stride)
    (threshold : ∀i,(v i).shelf.table.base+(v i).shelf.table.size≤(v i).shelf.firstBase) : Layout v size := by
  refine ⟨first.trans ((Nat.le_add_right ..).trans bound),
    fun i=>first.trans ((Nat.le_add_right ..).trans (starts i)),?_,threshold,?_⟩
  · intro i
    exact (ends i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right arena.stride i.isLt) _).trans bound)
  · apply ProtocolRAMStaticSlabs.disjoint_of_order
    intro i j hij
    exact (ends i).trans ((Nat.add_le_add_left (Nat.mul_le_mul_right arena.stride hij) _).trans (starts j))

def price (v : Market z d k) (raw : Tape z d) :=
  v.shelf.quoteTape v.phase v.temperature k v.kind raw

def localData (v : Market z d k) (raw : Tape z d) :=
  v.shelf.mountROM v.sampler k v.depth (price v raw)

def controller (v : Fin jobs → Market z d k) (raw : Tape z d) : Tape z d :=
  ProtocolRAMStaticSlabs.mounted (fun i=>low (v i)) (fun i=>high (v i)) (fun i=>localData (v i) raw) raw

def header (v : Fin jobs → Market z d k) (size : ℕ) (words : Tape z d) : Tape z d :=
  inputTape z d _ (controller v (Computability.VPVNP.RAMMemory.initialMemory size words))

def initial (v : Fin jobs → Market z d k) (size : ℕ) (words : Tape z d) : Tape z d :=
  Computability.VPVNP.RAMMemory.initialMemory size (header v size words)

def booted (v : Fin jobs → Market z d k) (size : ℕ) (words : Tape z d) :=
  images z d (initial v size words) (rounds d)

/-- Construct the initial words directly from a permutation and an independent high tape. -/
def permutationWords (π : Equiv.Perm (Fin (2^z))) (rest : Tape z d) : Tape z d :=
  fun a=>if h : a<2^z then ((π ⟨a,h⟩).val : Word _) else rest a

theorem permutationWords_get (π : Equiv.Perm (Fin (2^z))) (rest : Tape z d) (i : Fin (2^z)) :
    permutationWords π rest i.val=((π i).val : Word _) := by simp [permutationWords,i.isLt]

theorem initial_eq (v : Fin jobs → Market z d k) {size : ℕ} (h : Layout v size) (words : Tape z d) :
    initial v size words = header v size words := by
  funext a
  by_cases here : a<size
  · simp [initial,Computability.VPVNP.RAMMemory.initialMemory,here]
  · have beyond := h.subdivision.trans (Nat.le_of_not_gt here)
    have noneAt (i : Fin jobs) : ¬ ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i a :=
      fun hit => here (hit.2.trans_le (h.extent i))
    simp only [initial,Computability.VPVNP.RAMMemory.initialMemory,ite_eq_right here]
    rw [header,inputTape_above _ beyond,controller,ProtocolRAMStaticSlabs.outside _ _ noneAt]
    simp [Computability.VPVNP.RAMMemory.initialMemory,here]

/-- Actual subdivision geometry, threshold words and sampler fixture for every future job.
All other addresses above the subdivision heap retain their initial contents. -/
structure Receipt (v : Fin jobs → Market z d k) (π : Equiv.Perm (Fin (2^z))) (raw mid : Tape z d) : Prop where
  geometry : Shelf.Geometry π mid
  table : ∀i, PurchaseMarks.Table (v i).phase (v i).temperature k (v i).kind (v i).shelf.table mid
  rom : ∀i (j : Key z d k), (v i).shelf.Prepared (v i).sampler (v i).depth (price (v i) raw) j mid
  kept : ∀a,heapEnd z d copies≤a →
    (∀i,¬ ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i a) → mid a=raw a

private theorem first_le_high (v : Market z d k) : v.shelf.firstBase≤high v := by
  unfold high Market.flags Shelf.flagsBase
  omega

theorem subdivision (v : Fin jobs → Market z d k) {size : ℕ} (h : Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Tape z d)
    (authentic : ∀i : Fin (2^z), words i.val=((π i).val : Word _)) :
    (subdivisionProgram z d).Exec (initial v size words) (booted v size words) (subdivisionConstant d*2^z) ∧
    After (d:=d) π (initial v size words) (rounds d) := by
  let raw : Tape z d := Computability.VPVNP.RAMMemory.initialMemory size words
  let data := controller v raw
  have rows (i : Fin (2^z)) : data i.val=((π i).val : Word _) := by
    have early := i.isLt.trans_le (root_extent (z:=z) (d:=d))
    have miss (j : Fin jobs) : ¬ ProtocolRAMStaticSlabs.Inside (fun t=>low (v t)) (fun t=>high (v t)) j i.val :=
      fun hit => (not_le_of_gt (early.trans_le (h.afterHeap j))) hit.1
    change controller v raw i.val=_
    rw [controller,ProtocolRAMStaticSlabs.outside _ _ miss]
    simpa only [raw,Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (early.trans_le h.subdivision)] using authentic i
  obtain ⟨ran,done⟩ := native_linear_run hd π data rows (physical_ordinal hd π)
  have first : initial v size words=inputTape z d _ data := initial_eq v h words
  rw [booted,first]
  exact ⟨@ran,done⟩

theorem start (v : Fin jobs → Market z d k) {size : ℕ} (h : Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Tape z d)
    (authentic : ∀i : Fin (2^z), words i.val=((π i).val : Word _)) :
    (subdivisionProgram z d).Exec (initial v size words) (booted v size words) (subdivisionConstant d*2^z) ∧
    Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size words) (booted v size words) := by
  let raw : Tape z d := Computability.VPVNP.RAMMemory.initialMemory size words
  let data := controller v raw
  obtain ⟨ran,done⟩ := subdivision v h hd π words authentic
  have first : initial v size words=inputTape z d _ data := initial_eq v h words
  simp only [booted,first] at ran
  rw [first] at done
  simp only [booted,first]
  refine ⟨ran,Shelf.geometry_of_ct π _ done,?_,?_,?_⟩
  · intro i r
    let m := v i
    let a := m.shelf.table.base+r.val%m.shelf.table.size
    have rem : r.val % m.shelf.table.size < m.shelf.table.size := Nat.mod_lt _ (Nat.two_pow_pos _)
    have small : a < m.shelf.firstBase := by
      have order := h.threshold i
      change m.shelf.table.base+m.shelf.table.size ≤ m.shelf.firstBase at order
      dsimp [a]; omega
    have lowAt : low (v i)≤a := Nat.le_add_right ..
    have hit : ProtocolRAMStaticSlabs.Inside (fun j=>low (v j)) (fun j=>high (v j)) i a :=
      ⟨lowAt,small.trans_le (first_le_high m)⟩
    change images z d (inputTape z d _ data) (rounds d) a=_
    rw [images_above data done ((h.afterHeap i).trans lowAt)]
    change controller v raw a=_
    rw [controller,ProtocolRAMStaticSlabs.cell_on _ _ h.apart hit]
    change m.shelf.mountROM m.sampler k m.depth (price m raw) a=_
    rw [m.shelf.mount_frame m.sampler k m.depth (price m raw) a (.inl small)]
    exact PurchaseMarks.mount_table m.phase m.temperature k m.kind m.shelf.table raw r
  · intro i j a lo hi
    have sep := h.threshold i
    have firstAt : (v i).shelf.firstBase≤a := (Nat.le_add_right ..).trans lo
    have lowAt : low (v i)≤a := (Nat.le_add_right ..).trans (sep.trans firstAt)
    have hit : ProtocolRAMStaticSlabs.Inside (fun t=>low (v t)) (fun t=>high (v t)) i a :=
      ⟨lowAt,hi.trans_le (((v i).shelf.final_after (v i).sampler (v i).depth j).trans (Nat.le_add_right ..))⟩
    rw [images_above data done ((h.afterHeap i).trans lowAt)]
    change controller v raw a=_
    rw [controller,ProtocolRAMStaticSlabs.cell_on _ _ h.apart hit]
    exact (v i).shelf.mount_ready (v i).sampler (v i).depth (price (v i) raw) j a lo hi
  · intro a highAt miss
    rw [images_above data done highAt]
    exact ProtocolRAMStaticSlabs.outside _ _ miss

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
