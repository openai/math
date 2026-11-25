import OAI.Hierarchy.ProtocolRAMPurchaseCalendarROM
import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult
import OAI.Hierarchy.ProtocolRAMStaticSlabs
import OAI.Hierarchy.ProbeStagePhysicalOrdinal

namespace OAI
/-! # Static sampler advice, permutation input, and reusable stage geometry -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

theorem incoming (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen : Mem z d)
    (size : ∀ i : Key z d k,Ready S (stage i) (sh.cfg S depth i)) (geo : Geometry π frozen)
    (table : PurchaseMarks.Table phase T k kind sh.table frozen) (lo : sh.table.base+sh.table.size ≤ sh.firstBase)
    (stock : ∀ (t : StageAt z d) (j : Fin (2*k)),(sh.stock t j).base+(sh.stock t j).size ≤ sh.firstBase)
    (stageBanks : heapEnd z d copies ≤ sh.firstBase) : sh.Incoming (k:=k) S π depth phase T kind frozen :=
  ⟨size,fun i => by
    obtain ⟨enc, seen⟩ := geo (stage i)
    exact ⟨enc, seen.group, seen.input, seen.output⟩,
    table,lo,stock,stageBanks⟩

def setup (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (raw : Mem z d) :=
  sh.mountROM S k depth (sh.quoteTape phase T k kind raw)

/-- One actual execution of the subdivision supplies every later stage geometry;
the static slabs and the score table are installed in the input to this execution. -/
theorem start (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ) (hd : 1≤d)
    (phase : PhasePrice) (T : ℝ) (kind : ℕ) (raw : Mem z d) (read : ∀ i:Fin (2^z),raw i.val=((π i).val:Word _))
    (size : ∀ i : Key z d k, Ready S (stage i) (sh.cfg S depth i)) (afterHeap : heapEnd z d copies ≤ sh.table.base)
    (afterRows : 2^z ≤ sh.table.base) (sep : sh.table.base+sh.table.size ≤ sh.firstBase)
    (stock : ∀ (t : StageAt z d) (j : Fin (2*k)),(sh.stock t j).base+(sh.stock t j).size ≤ sh.firstBase) :
    let data := sh.setup S k depth phase T kind raw
    let first := inputTape z d _ data
    let mid := images z d first (rounds d)
    (subdivisionProgram z d).Exec first mid (subdivisionConstant d*2^z) ∧ Geometry π mid ∧
      sh.Incoming (k:=k) S π depth phase T kind mid ∧
      (∀ i : Key z d k,sh.Prepared S depth (sh.quoteTape phase T k kind raw) i mid) ∧
      ∀ a,heapEnd z d copies≤a → mid a=data a := by
  let price := sh.quoteTape phase T k kind raw
  let data := sh.mountROM S k depth price
  let first := inputTape z d _ data
  let mid := images z d first (rounds d)
  have rows (r : Fin (2^z)) : data r.val=((π r).val:Word _) := by
    have early := r.isLt.trans_le afterRows
    rw [show data r.val=price r.val from sh.mount_frame S k depth price r.val (Or.inl (by omega))]
    simpa [price,quoteTape,PurchaseMarks.mount,fillSegment,not_le.mpr early] using read r
  obtain ⟨ct,done⟩ := native_linear_run hd π data rows (physical_ordinal hd π)
  have global := geometry_of_ct π first done
  have high (a : ℕ) (above : heapEnd z d copies≤a) : mid a=data a := images_above data done above
  have before : heapEnd z d copies ≤ sh.firstBase := by omega
  have quoted : PurchaseMarks.Table phase T k kind sh.table mid := by
    intro r
    let a := sh.table.base+r.val%sh.table.size
    have bound := Nat.mod_lt r.val (Nat.two_pow_pos sh.table.bits)
    change r.val%sh.table.size < sh.table.size at bound
    have low : a < sh.firstBase := by dsimp [a];omega
    have «prefix» : sh.table.read mid r=sh.table.read price r :=
      (high a (afterHeap.trans (Nat.le_add_right ..))).trans (sh.mount_frame S k depth price a (.inl low))
    exact «prefix».trans (PurchaseMarks.mount_table phase T k kind sh.table raw r)
  refine ⟨@ct,global,sh.incoming S π depth phase T kind mid size global quoted sep stock before,?_,high⟩
  intro i
  exact sh.ready_of_frame S depth price data mid i (sh.mount_ready S depth price i)
    (fun x low _=>high x (before.trans ((Nat.le_add_right ..).trans low)))

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
