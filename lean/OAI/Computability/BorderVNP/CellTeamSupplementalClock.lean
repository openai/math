import OAI.Computability.BorderVNP.CellTeamPreparedUnits
import OAI.Computability.BorderVNP.CellPacketSupplementalProducerRows
import OAI.Computability.BorderVNP.RoutingISATypedHistoryBounds

/-! # Native clock of the complete owned supplemental task preparation and calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM CellDispatch CellSparse CellSparse.Packet CellMacro.Generator CompactMachine

variable {w count table controls : ℕ} {Site : Type}

/-- The true task data resulting from all the preceding owned supplemental writes. -/
theorem patchedSource (m : Memory w) (owned : ℕ → Owned Site) (frame : ℕ)
    (init : ∀ i < count, Initial (owned i) table controls i m) (alloc : Allocation frame table controls count w owned)
    (i : ℕ) (hi : i < count) : (owned i).typed.cell.Stored (written m (fun j => (owned j).cell) count) := by
  have h := init i hi
  exact typed_stored m (fun j => (owned j).cell) hi (owned i).placed (owned i).geometry
    (owned i).callRow (owned i).extra rfl h.report h.prefixEnd h.stored h.mergeRoom h.original
    h.separateCount (alloc.originals i hi) (alloc.patched i hi)

/-- The actual prepass, seven-word initializer and three-word call-directory allowances,
including the probes of the words published by the initializer. -/
def nativeCharge (owned : ℕ → Owned Site) (f : Frame) (mt : Memory w) (count : ℕ) :=
  17+62*count+TypedBatch.loadDirectory.slots+TypedBatch.setup.slots+
      (∑ j ∈ Finset.range count, TypedBatch.rowCharge (fun k => (owned k).typed.cell.cost w) j)+1+
    (17+7*f.count+4*(f.ownedRows mt 0 f.count).length+
      ∑ j ∈ Finset.range count, ((owned j).typed.cell.burst w).length)

/-- The charge uses the initializer's actual source memory and the dispatch frame
read after initialization. This also applies when a native pass repoints the exterior. -/
theorem nativeCharge_of_stored (m : Memory w) (owned : ℕ → Owned Site) (description : ℕ)
    (f : Frame) (mt : Memory w) (hw : 0 < w) (stored : ∀ i < count, (owned i).typed.cell.Stored m)
    (body : ∀ i < count, ∀ j, (owned i).placed.headerWidth+(Source.boxBody ((owned i).placed.factors j)).length ≤ description) :
    nativeCharge owned f mt count ≤ 64+11*f.count+100*count+
      308*(∑ i ∈ Finset.range count, units (owned i).placed (owned i).extra w description) := by
  let q (i : ℕ) := ((owned i).typed.cell.burst w).length
  let charge (i : ℕ) := TypedBatch.rowCharge (fun k => (owned k).typed.cell.cost w) i
  have each (i : ℕ) (hi : i < count) :
      charge i+q i ≤ TypedBatch.fetch.slots+TypedBatch.publish.slots+2+308*units (owned i).placed (owned i).extra w description := by
    obtain ⟨c,_,b⟩ := limits (owned i).placed (owned i).layout (owned i).geometry (owned i).extra
      m description hw (stored i hi) (body i hi)
    have div := Nat.div_le_self (8*units (owned i).placed (owned i).extra w description) w
    change (owned i).typed.cell.cost w ≤ _ at c
    change q i ≤ _ at b
    dsimp only [charge,TypedBatch.rowCharge]
    omega
  have total := Finset.sum_le_sum (s:=Finset.range count) fun i hi => each i (Finset.mem_range.mp hi)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,←Finset.mul_sum] at total
  have length : (f.ownedRows mt 0 f.count).length ≤ f.count := (List.length_filter_le ..).trans_eq (List.length_range' ..)
  change 17+62*count+TypedBatch.loadDirectory.slots+TypedBatch.setup.slots+(∑ j ∈ Finset.range count,charge j)+1+
    (17+7*f.count+4*(f.ownedRows mt 0 f.count).length+∑ j ∈ Finset.range count,q j) ≤ _
  norm_num [TypedBatch.loadDirectory,TypedBatch.setup,TypedBatch.fetch,TypedBatch.publish,Code.block,Code.slots,
    readFrame] at total ⊢
  omega

/-- Charge the true sized bursts resulting from the exclusive supplemental tail
patches, using the source image produced by that prepass. -/
theorem nativeCharge_le (m : Memory w) (owned : ℕ → Owned Site) (description frame : ℕ)
    (f : Frame) (mt : Memory w) (hw : 0 < w) (init : ∀ i < count, Initial (owned i) table controls i m)
    (alloc : Allocation frame table controls count w owned)
    (body : ∀ i < count, ∀ j, (owned i).placed.headerWidth+(Source.boxBody ((owned i).placed.factors j)).length ≤ description) :
    nativeCharge owned f mt count ≤ 64+11*f.count+100*count+
      308*(∑ i ∈ Finset.range count, units (owned i).placed (owned i).extra w description) :=
  nativeCharge_of_stored (written m (fun j => (owned j).cell) count) owned description f mt hw
    (patchedSource m owned frame init alloc) body

/-- The true compact row order in the produced tasks charges precisely the same
sum as the all-cell filtered geometry bound. Absolute relocations do not affect lengths. -/
theorem produced_units (l : CellControlRows.Layout) (mem : ℕ → ℕ) (p : ℕ → Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List Record) (w description : ℕ) :
    (∑ i ∈ Finset.range (l.before mem l.cells),
      units (produced l mem p geom extra i).placed (produced l mem p geom extra i).extra w description) =
    Cube.TeamRowClock.assignedSum (fun c : Fin l.cells => l.owner mem c.val) l.team
      (fun c => units (p c.val) (extra c.val) w description) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact TypedTaskBuilder.sum_owned l.toLayout mem (fun c => units (p c) (extra c) w description)

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
