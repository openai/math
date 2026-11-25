import OAI.Computability.BorderVNP.PackedFrozenVirtualStage
import OAI.Computability.BorderVNP.PackedBankLocalPopulation
import OAI.Computability.BorderVNP.PackedBankPrivateScalarReplay

/-! # Population and address bounds from the actual measured normalized stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Stage

open Cover Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Packing Packing.Inherited Packing.InheritedHook Packing.InheritedBank Packing.DirectoryCircuit
open CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork Epoch Epoch.Round
open scoped Classical

variable {D m k d d' sites n np C pbits kbits bbits w : ℕ} [NeZero D]
variable {I P K Bin : Type} [Fintype I] [Fintype P] [Fintype Bin] [Field K] {bits : P → ℕ}
variable {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin d' child) (e : PaidIdentity K D m)
variable (q : s.Index e) (data : ∀ i, RecordData (child i).pack.layout)
private abbrev Seed (I Bin : Type) (d' : ℕ) := (I → Deck (d'+1)) × Bin
variable {σ : Type*} [Fintype σ]
variable (pop : PublicPopulation.Pins (Fin s.rowCount) σ bbits w) (col : Columns σ s.rowCount D w)
variable (code : Seed I Bin d' ↪ Fin (2^bbits)) (seed : Seed I Bin d' ≃ Fin n)
variable (oldSite : (raw child).layout.Site ↪ Fin sites) (portID : Fin k × P ↪ Fin np)
variable (dummy : Fin (edgeCapacity e s.rowCount n) → SiteShape e s.input (Seed I Bin d'))
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e s.rowCount n) np C pbits kbits w σ)
variable (literal : Bool → σ) (counts : Frame σ (Seed I Bin d' × Option (Fin e.count) × Fin w))
variable (occupied : Fin (edgeCapacity e s.rowCount n) → σ)
local notation3 "sID" => siteRows e s.input oldSite seed.toEmbedding
local notation3 "eID" => outputRows e s.input s.label s.perm s.orient (0,false) q
  (CutCircuit.denseRows (raw child).layout s.slot) seed.toEmbedding
local notation3 "G₀" => (s.result e q).pack.layout

/-- The measured geometry discharges even the bound on empty clipped bands'
original bin ordinals. The neighborhood multiplier is fixed before the input
stage or histogram, and the stage may use a larger shared word budget. -/
theorem frozenMeasuredSourceData (radius : ℝ) (hk : 0 < k) {ν u v : ℝ} (measure : s.Measurements hk radius ν u v)
    (x : σ → Bool) (lit : ∀ b,x (literal b) = b)
    (old : Ready e pop col code seed (raw child) s.bin s.positive oldSite s.slot dummy x)
    (ends : Views.EndpointData G₀ F sID eID portID x) (enabled : ∀ r,x (occupied r) = true ↔ r ∈ Set.range eID)
    (hist : ∀ a i,value (fun j => counts.eval x (a,i,j)) = i.elim (s.matched a) (q a).val)
    {factor T M B : ℕ} (cert : s.RecordFactor e factor) (hT : 0 < T)
    (childCap : ∀ i,RecordsWithin (child i) (data i) true T)
    (recordsFit : loadMultiplier e*factor*k*T ≤ M)
    (binsFit : (measured_population_cap (I := I) (B := Bin) e radius).choose*(factor*k*T) ≤ B)
    (room : HookTape.sourceRoom e (0,false) M B < 2^w) :
    HookTape.SourceData pop code s.perm e seed.toEmbedding (Views.literalFields F literal) counts occupied
      (raw child) s.slot s.bin s.positive (0,false) q oldSite portID sID (fun _ => 0) x
      (fun v => (data v.1).prior v.2) (fun v => (data v.1).payload v.2) M B := by
  have cap := s.bankRecordData_within e q data cert true T hT childCap
  have birth := s.birthTileCap_of_children e q data cert hT childCap
  have pool := (measured_population_cap (I := I) (B := Bin) e radius).choose_spec hk child s measure q _ _ _ birth
  refine HookTape.virtualSourceData pop code s.perm e seed.toEmbedding F literal counts occupied
    (raw child) s.slot s.bin s.positive (0,false) q oldSite portID
    (fun v => productAddress d' ((s.result e q).site v)) x lit _ _ M B old.population old.widths ?_
    ends enabled hist ?_ room
  · intro a
    exact (CutCircuit.dense_count (raw child).layout s.slot s.bin a).symm.le.trans ((pool a).trans binsFit)
  · intro t
    exact (Nat.le_add_left _ 1).trans ((cap t).trans recordsFit)

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
