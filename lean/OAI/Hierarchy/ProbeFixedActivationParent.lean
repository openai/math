import OAI.Hierarchy.ProbeFixedActivationCoordinates
import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbePurchaseArchiveLifetime
import OAI.Hierarchy.ProtocolRAMCalendarFrozenThreshold

namespace OAI
/-! # Recovering the purchaser's chosen permutation and archived rows from the initial RAM tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseFrozen
open StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "s" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "market" => v.frozenMarket P z width
local notation "snapshot" => v.frozenInput P z width r banks src tab dst owners

/-- The boot's authenticated CT data and static stratum header persist through
the entire real prefix, stop guard, and discrepancy pass at a buying date. -/
theorem activation_parent (mem : Memory W) (π : Equiv.Perm (Fin (2^z))) (u h : ℕ)
    (hp : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel)
    (whole : Calendar.mounted C (events v.mesh) mem)
    (geometry : Shelf.Geometry π mem) (heap : heapEnd z (2^v.W) copies≤(G).first)
    (keyRoom : (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)).stop≤(G).first)
    («public» : (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)).Loaded mem) :
    let v₀:=market u h
    let frozen:=snapshot mem u h
    ∃fixture, v₀.shelf.Incoming (k:=k) v.sampler π v.depth v₀.phase v₀.temperature v₀.kind frozen ∧
      (∀i : Key z (2^v.W) k,v₀.shelf.Prepared v.sampler v.depth fixture i frozen) ∧
      (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)).Loaded frozen := by
  intro v₀ frozen
  let e:=Attempt.outer u h
  let base:=(G).base v.mesh (.attempt e)
  let entry:=trialState C mem u h
  let hdr:=stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)
  let input:=(guard C e).apply entry
  obtain ⟨_,cut⟩:=outer_slot C mem u h hp hh whole
  have earliest (a : Event) : (G).first≤(G).base v.mesh a := Nat.le_add_right ..
  have loc:=v.catalyst_birth_room P z width e
  have low (x : ℕ) (small : x<(G).first) : frozen x=mem x := by
    have early:=small.trans_le (earliest (.attempt e))
    have old : entry x=mem x:=by
      rw [show entry=run C _ mem from cut.entry.symm]
      exact run_frame C _ _ _ cut.prefixReady (fun a _=>(v.event_prefix P z width r banks src tab dst owners a x (small.trans_le (earliest a))).1)
    have guardLow : x<(C).stopAt e := early.trans_le (loc.1.trans (min_le_left ..))
    have failureLow : x<v₀.failures.base := early.trans_le (loc.1.trans (min_le_right ..))
    change image v₀.failures.base v₀.failures.rows _ input x=mem x
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl failureLow)]
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl guardLow)).trans old
  have actual:=Shelf.geometry_of_frame π mem frozen geometry (fun x h=>low x (h.trans_le heap))
  have ready : v₀.ready input:=cut.currentReady.2.1
  obtain ⟨_,fixture,sample,prepared⟩:=ready.2.2.2.2
  refine ⟨fixture,⟨sample.dimensions,?_,sample.table,sample.bankEnd,sample.stockEnd,sample.afterCT⟩,
    prepared,«public».frame (fun x _ hi=>low x (hi.trans_le keyRoom))⟩
  intro i
  obtain ⟨enc,seen⟩ := actual (PurchaseFrozen.stage i)
  exact ⟨enc,seen.group,seen.input,seen.output⟩

/-- The same outer shelf, fixed original sampler and price are read at the
actual final discrepancy memory for every inner candidate of that acquisition. -/
theorem activation_archive (mem fixture : Memory W) (π : Equiv.Perm (Fin (2^z))) (u h j b : ℕ)
    (hp : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) (hj : j<v.mesh.reserveSteps) (hb : b<v.mesh.innerFuel)
    (whole : Calendar.mounted C (events v.mesh) mem)
    (keys : (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)).stop≤(G).first) :
    let v₀:=market u h
    let frozen:=snapshot mem u h
    v₀.shelf.Incoming (k:=k) v.sampler π v.depth v₀.phase v₀.temperature v₀.kind frozen →
    (∀i : Key z (2^v.W) k,v₀.shelf.Prepared v.sampler v.depth fixture i frozen) →
    (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader u h)).Loaded frozen →
    ArchiveReads v₀.shelf v.sampler π v.depth ((s).stratumHeader u h) v₀.phase v₀.temperature v₀.kind frozen
      (replayScoreMemory C mem u h j b) k := by
  intro v₀ frozen input prepared «public»
  let a:=Attempt.outer u h
  have loc:=v.catalyst_birth_room P z width a
  have dated : (G).first≤(G).base v.mesh (.attempt a):=Nat.le_add_right ..
  have keyEnd:=keys.trans (dated.trans loc.2.1)
  have saved:=priced_purchase_archive v.mesh v.finish (v.basePhase width) f _ (P.catalogue.sink r banks src tab dst owners)
    P.catalogue.idBase _ _ mem u h ((s).stratumHeader u h) π fixture (outer_head_ready whole hp hh) input prepared keyEnd «public»
  exact purchased_replay_archive C mem G u h j b saved whole hp hh hj hb (Nat.one_le_two_pow) keyEnd loc.2.2
    (fun a x low=>(v.event_prefix P z width r banks src tab dst owners a x low).1)

/-- Every signed tile's old inventory is a valid table index on the real
frozen memory, by the chronological cap on the actual entering stock bank. -/
theorem activation_fit (mem : Memory W) (u h : ℕ) (hp : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel)
    (payload : width≤2^z)
    (stock : StockBound.Run C (v.stockBanks P z width) mem z (CoreBoard.Stages z (2^v.W)) k (v.keepLimit*width)) :
    let v₀:=market u h
    let frozen:=snapshot mem u h
    ∀t : Tile z (2^v.W),∀j : Fin k×Bool,stockBits v₀.shelf.stockBase k frozen t j<v₀.shelf.table.size := by
  intro v₀ frozen
  let a:=Attempt.outer u h
  obtain ⟨_,cut⟩:=outer_slot C mem u h hp hh stock.mounted_all
  have pointer := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh G P.joint.initial
    (v.emptyReserve P z width) a).1
  change v₀.shelf.stockBase=(v.stockBanks P z width).previous v.mesh (.attempt a) at pointer
  have capped : StockBound.Bounded z (CoreBoard.Stages z (2^v.W)) k v₀.shelf.stockBase (v.keepLimit*width) (trialState C mem u h) := by
    rw [pointer]
    exact (stock.slot cut).1
  have bounds:=v.activation_parent_floor P z width r banks src tab dst owners u h
  have stages : CoreBoard.Stages z (2^v.W)=2*rounds (2^v.W)+1:=template_length ..
  exact v₀.frozen_threshold v.keepLimit width C a _ payload rfl
    (stages ▸ capped) (by simpa only [stages] using bounds.1) (by simpa only [stages] using bounds.2)

set_option maxHeartbeats 1000000 in
theorem activation_flags_room (mem : Memory W) (whole : Calendar.mounted C (events v.mesh) mem)
    (u h : ℕ) (space : (G).endAddress v.mesh<2^W)
    (hp : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) :
    let v₀:=market u h
    v₀.shelf.flagsBase v.sampler z (2^v.W) k v.depth+count z (2^v.W) k*paths z v.sampler.degree v.depth<2^W := by
  intro v₀
  let a:=Attempt.outer u h
  obtain ⟨_,cut⟩:=outer_slot C mem u h hp hh whole
  have occurs : Event.attempt a∈events v.mesh:=by
    change Event.attempt a∈events (C).mesh
    rw [cut.events]
    simp [a]
  have loc:=(v.catalyst_birth_room P z width a).2.2
  have len : (f a).market.rows=count z (2^v.W) k*paths z v.sampler.degree v.depth := by
    exact StripChart.candidate_count F v.mesh G P.joint.initial s a
  rw [←len]
  change (f a).market.flags+(f a).market.rows<2^W
  exact loc.trans_lt (((G).within v.mesh (.attempt a) occurs).trans_lt space)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
