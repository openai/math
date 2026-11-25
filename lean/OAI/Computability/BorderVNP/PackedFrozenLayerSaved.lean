import OAI.Computability.BorderVNP.PackedFrozenLayerTape
import OAI.Computability.BorderVNP.PackedInheritedHookLive
import OAI.Computability.BorderVNP.PackedInheritedDenseOrder

/-! # Immutable interval tape on the represented dense saved layout

The physical endpoint table comes from the old sparse names. The single shared cut pass
furnishes the clipped operands on those same names for charged and uncharged cables.
The actual successor tile load bounds all old and new local incidences.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Views

open Crossing Shortening DirectoryCircuit CellAddressCircuit ParseBatchSort
open scoped Classical

variable {D s n np C d k w : ℕ} {P : Type*} {bits : P → ℕ} {R σ : Type*} [Fintype σ]
variable (p : Pack D P bits R) (F : Fields s n np C d k w σ)
variable (sites : p.layout.Site ↪ Fin s) (slot : p.layout.Edge ↪ Fin n) (ports : P ↪ Fin np)

omit [Fintype σ] in
/-- Stable sorting of the real cables preserves the endpoint table, all external ports,
and the zero-width conditions for holes in both physical row rectangles. -/
theorem EndpointData.dense {x : σ → Bool} (h : EndpointData p.layout F sites slot ports x) :
    EndpointData (densePack p slot).layout F sites (CutCircuit.denseRows p.layout slot) ports x := by
  have name (z) : CutCircuit.denseRows p.layout slot (Names.denseSlot p.layout slot z) = slot z := by
    simp [CutCircuit.denseRows]
  constructor
  · intro a
    obtain ⟨z,rfl⟩ := (Names.denseSlot p.layout slot).surjective a
    have hv : (densePack p slot).layout.src (Names.denseSlot p.layout slot z) = p.layout.src z :=
      Names.src_slot p.layout _ _ z
    exact (congrArg (fun r => value (x ∘ F.ptr (.inl (.inl r)))) (name z)).trans
      ((h.src z).trans (congrArg (fun v => (F.sites (sites v)).val) hv.symm))
  · intro a
    obtain ⟨z,rfl⟩ := (Names.denseSlot p.layout slot).surjective a
    have hv : (densePack p slot).layout.dst (Names.denseSlot p.layout slot z) = p.layout.dst z :=
      Names.dst_slot p.layout _ _ z
    exact (congrArg (fun r => value (x ∘ F.ptr (.inl (.inr r)))) (name z)).trans
      ((h.dst z).trans (congrArg (fun v => (F.sites (sites v)).val) hv.symm))
  · exact h.attach
  · intro a
    obtain ⟨z,rfl⟩ := (Names.denseSlot p.layout slot).surjective a
    exact (congrArg (fun r => value (x ∘ F.edgeWidth r)) (name z)).trans
      ((h.edge z).trans (dense_width p.layout slot z).symm)
  · exact h.port
  · intro i absent
    apply h.edgeHole i
    rintro ⟨z,rfl⟩
    exact absent ⟨Names.denseSlot p.layout slot z,name z⟩
  · exact h.portHole

end Packing.Inherited.Views

namespace Packing.Inherited.FrozenTape.LayerRows

open Crossing Shortening DirectoryCircuit Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open InheritedBank CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m s old np seeds C C' d d' k k' w binBits : ℕ} [NeZero D] {K : Type*} [Field K]
variable (e : PaidIdentity K D m) {σ : Type*} [Fintype σ]
variable (oldF : Fields s old np C d k w σ)
variable (newF : Fields (siteCapacity e s seeds) (edgeCapacity e old seeds) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (work extent : Fin s → Fin w → σ) (successor : Fin (edgeCapacity e old seeds) → σ)
variable {P : Type} [Fintype P] {bits : P → ℕ} {A : Type} [Fintype A]
variable (p : Pack D P bits K) (slot : p.layout.Edge ↪ Fin old)
variable (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
local notation3 "dense" => densePack p slot
local notation3 "labels" => CutCircuit.denseBin p.layout slot bin
local notation3 "oldID" => CutCircuit.denseRows p.layout slot
local notation3 "orient" => positive ∘ (Names.denseSlot p.layout slot).symm
variable (q : Counts e (densePack p slot) (CutCircuit.denseBin p.layout slot bin) perm)
variable (siteID : p.layout.Site ↪ Fin s) (portID : P ↪ Fin np) (seed : A ↪ Fin seeds)
local notation3 "G" => (output e (densePack p slot) (CutCircuit.denseBin p.layout slot bin) perm (positive ∘ (Names.denseSlot p.layout slot).symm) first q).layout
local notation3 "nextID" => outputRows e (densePack p slot) (CutCircuit.denseBin p.layout slot bin) perm (positive ∘ (Names.denseSlot p.layout slot).symm) first q (CutCircuit.denseRows p.layout slot) seed
local notation3 "nextSite" => siteRows e (densePack p slot) siteID seed
variable (states : p.layout.Site → Site) (prior payload : p.layout.Site → ℕ)
local notation3 "hist" => nextPrior e (densePack p slot) (CutCircuit.denseBin p.layout slot bin) perm (positive ∘ (Names.denseSlot p.layout slot).symm) first q prior
local notation3 "pay" => nextPayload e (densePack p slot) (CutCircuit.denseBin p.layout slot bin) perm (positive ∘ (Names.denseSlot p.layout slot).symm) first q payload

/-- The shared physical cut pass and the genuine successor tile cap supply all operands and
field-size bounds of the frozen layer on the dense save. No additional cut or address
values need to be provided at the time the nine-word emitter is chosen. -/
theorem saved_inputs (pop : PublicPopulation.Pins (Fin old) σ binBits w) (code : A ↪ Fin (2^binBits))
    (hc : InheritedHook.ComputesCuts (m := m) pop code perm cut) (name : A → ℕ) (x : σ → Bool)
    (hpop : PublicPopulation.Represents pop p.layout bin slot code x)
    (htotal : ∀ a, count p.layout bin a < 2^w) (hwidth : ∀ z,value (x ∘ pop.width (slot z)) = p.layout.width z)
    (previous : Views.EndpointData p.layout oldF siteID slot portID x)
    (current : Views.EndpointData G newF nextSite nextID portID x)
    (hw : ∀ v, value (x ∘ work (siteID v)) = (states v).work)
    (he : ∀ v, value (x ∘ extent (siteID v)) = (states v).size)
    (mask : ∀ i, x (successor i) = true ↔ i ∈ Set.range nextID)
    (hin : ∀ v, (states v).incoming = incoming p.layout v)
    (hwcap : ∀ v, (states v).work ≤ payload v)
    {T : Type*} (tile : (G).Site → T)
    (cap : ∀ t, localRecords G true hist pay (fun v => tile v = t) < 2^w) :
    Layer.RealInputs e oldF newF cut work extent successor dense labels perm name orient first q
      siteID oldID portID seed states prior payload x := by
  have hd (v : p.layout.Site) : (states v).incoming = incoming (dense).layout v :=
    (hin v).trans (dense_incoming p.layout slot v).symm
  refine ⟨previous.dense _ _ _ _ _,current,?_,?_,hw,he,?_,mask,hd,hwcap,?_⟩
  · intro v
    have h := (retained_extent_le e dense labels perm orient first q v (states v) prior payload (hd v)
      (hwcap v) (fun u => tile u = tile (.inl v)) rfl).trans_lt (cap (tile (.inl v)))
    change max 1 ((states v).work + (states v).incoming + _) < _ at h
    exact (hd v).symm.le.trans_lt (by omega)
  · intro v
    exact (Nat.le_add_left _ _).trans_lt ((payload_incoming_le G hist pay v
      (fun u => tile u = tile v) rfl).trans_lt (cap (tile v)))
  · intro a b r
    obtain ⟨z,rfl⟩ := (Names.denseSlot p.layout slot).surjective a
    have hr := (hc p.layout bin slot x hpop htotal hwidth z b r).trans
      (Layer.live_prior (m := m) p slot bin perm (fun a => (code a).val) name z b r)
    have row : oldID (Names.denseSlot p.layout slot z) = slot z := by simp [CutCircuit.denseRows]
    exact (congrArg (fun i => value fun j => cut.eval x ((i,b),r,j)) row).trans hr
  · intro v
    exact ⟨fun u => tile u = tile (.inl v),rfl,cap (tile (.inl v))⟩

end Packing.Inherited.FrozenTape.LayerRows

end BorderVNP
end Computability
end OAI
