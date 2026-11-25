import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseROMData
import OAI.Hierarchy.ProtocolRAMStaticSlabs
import OAI.Hierarchy.ProtocolRAMPrices
import OAI.Hierarchy.TaggedShorterPathPorts

namespace OAI
/-! # The native subdivision banks and the original static words for each market -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PurchaseCT
open ProbeStage
def reverseDigits (S : PurchaseSampler) (m : ℕ) : Fin m → Fin S.degree → Fin S.degree :=
  TaggedShorterPathPorts.backCode (S.rows m) (S.in_degree m)

end Hierarchy.ProtocolRAM.PurchaseCT

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {z d k : ℕ}

def slabData (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (raw : Mem z d) (i : Key z d k) :=
  let l := sh.L S depth i
  l.data (S.rows l.sockets) (reverseDigits S l.sockets) raw

abbrev Prepared (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (fixture : Mem z d) (i : Key z d k) (m : Mem z d) :=
  ∀ a,sh.lo S depth i≤a → a < sh.hi S depth i → m a=sh.slabData S depth fixture i a

/-- Each stage of the permutation has three permanent physical arrays. -/
def Geometry (π : Equiv.Perm (Fin (2^z))) (m : Mem z d) : Prop :=
  ∀ t : StageAt z d,∃ enc : (stageAt z d t).Group ↪ Fin (Fintype.card (stageAt z d t).Group),
    (allocation t 0 0 0 0).CTLoaded (banks t) (advisedStage z d π t) enc m

theorem geometry_of_ct (π : Equiv.Perm (Fin (2^z))) (input : Mem z d) (done : After (d:=d) π input (rounds d)) :
    Geometry π (images z d input (rounds d)) := fun t => ⟨(groupNumber t).toEmbedding, resident_numbered π t 0 0 0 0 input done⟩

theorem geometry_of_frame (π : Equiv.Perm (Fin (2^z))) (old new : Mem z d) (was : Geometry π old)
    (keep : ∀ a,a<heapEnd z d copies → new a=old a) : Geometry π new := by
  intro t
  obtain ⟨e,seen⟩ := was t
  have same (c : Fin 3) (r : Word _) :
      (stageBank z d (stageNumber t) c).read new r=(stageBank z d (stageNumber t) c).read old r := by
    apply keep
    exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (stageBank_end ..)
  exact ⟨e,fun i=>(same 0 _).trans (seen.group i),fun i=>(same 1 _).trans (seen.input i),
    fun i=>(same 2 _).trans (seen.output i)⟩

/-- Preload public sampler rows and DFS loop positions; the advice is independent of the permutation. -/
def mountROM (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (raw : Mem z d) : Mem z d :=
  ProtocolRAMStaticSlabs.mounted (sh.lo (k:=k) S depth) (sh.hi S depth) (sh.slabData S depth raw) raw

theorem mount_ready (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (raw : Mem z d) (i : Key z d k) :
    sh.Prepared S depth raw i (sh.mountROM S k depth raw) := by
  intro a lo hi
  apply ProtocolRAMStaticSlabs.cell_on _ _ _ ⟨lo,hi⟩
  intro l r a hl hr
  by_contra h
  rcases sh.separate S depth h with lt|gt <;> rcases hl with ⟨a1,a2⟩ <;> rcases hr with ⟨b1,b2⟩ <;> omega

theorem mount_frame (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (raw : Mem z d) (a : ℕ)
    (outside : a < sh.firstBase ∨ sh.flagsBase S z d k depth≤a) : sh.mountROM S k depth raw a=raw a := by
  apply ProtocolRAMStaticSlabs.outside
  intro i inside
  rcases outside with early|late
  · exact (not_le_of_gt early) ((Nat.le_add_right ..).trans inside.1)
  · exact (not_lt_of_ge ((sh.final_after S depth i).trans ((Nat.le_add_right ..).trans late))) inside.2

theorem ready_of_frame (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (fixture old new : Mem z d) (i : Key z d k)
    (prepared : sh.Prepared S depth fixture i old)
    (keep : ∀ a,sh.lo S depth i≤a → a < sh.hi S depth i → new a=old a) :
    sh.Prepared S depth fixture i new := fun a lo hi => (keep a lo hi).trans (prepared a lo hi)

def quoteTape (sh : Shelf) (phase : PhasePrice) (T : ℝ) (k kind : ℕ) (raw : Mem z d) :=
  PurchaseMarks.mount phase T k kind sh.table raw

end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
end

end OAI
