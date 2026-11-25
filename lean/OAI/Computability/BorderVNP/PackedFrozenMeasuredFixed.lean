import OAI.Computability.BorderVNP.PackedFrozenMeasuredNode

/-! # Running the same selected shortening-node frame at its fixed public row capacity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Stage

open Cover Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Packing Packing.Inherited Packing.InheritedHook Packing.InheritedBank Packing.DirectoryCircuit
open Epoch Epoch.Round CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m k d d' sites n np C pbits kbits bbits C₀ db₀ kb₀ w : ℕ} [NeZero D]
variable {I P K Bin : Type} [Fintype I] [Fintype P] [Fintype Bin] [Field K] {bits : P → ℕ}
variable {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin d' child) (e : PaidIdentity K D m)
variable (q : s.Index e) (data : ∀ i, RecordData (child i).pack.layout)
variable {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] (S : FrozenTape.Schema R B)
private abbrev NamedSeed (I Bin : Type) (d' : ℕ) := (I → Deck (d'+1)) × Bin
variable {rows : ℕ} (cap : s.rowCount = rows)
local notation3 "orig" => s.slot.trans (finCongr cap).toEmbedding
variable (pop : PublicPopulation.Pins (Fin rows) σ bbits w) (col : Columns σ rows D w)
variable (code : NamedSeed I Bin d' ↪ Fin (2^bbits)) (seed : NamedSeed I Bin d' ≃ Fin n)
variable (oldSite : (raw child).layout.Site ↪ Fin sites) (portID : Fin k × P ↪ Fin np)
variable (dummy : Fin (edgeCapacity e rows n) → SiteShape e (densePack (raw child) (s.slot.trans (finCongr cap).toEmbedding)) (NamedSeed I Bin d'))
variable (oldF : Fields sites rows np C₀ db₀ kb₀ w σ)
variable (F : Fields (siteCapacity e sites n) (edgeCapacity e rows n) np C pbits kbits w σ)
variable (literal : Bool → σ) (counts : Frame σ (NamedSeed I Bin d' × Option (Fin e.count) × Fin w))
variable (cut : Frame σ ((Fin rows × Band D) × CutCircuit.Result × Fin w))
variable (carried : Frame σ (FrozenTape.Pins R B pbits)) (work extent : Fin sites → Fin w → σ)
variable (ports : Fin np → Bool) (occupied : Fin (edgeCapacity e rows n) → σ)
variable (states : (raw child).layout.Site → Site) (name : NamedSeed I Bin d' → ℕ) (position : e.Entry → ℕ)
local notation3 "sID" => siteRows e s.input oldSite seed.toEmbedding
local notation3 (prettyPrint := false) "eID" => (outputRows e s.input s.label s.perm s.orient (0,false) q
  (CutCircuit.denseRows (raw child).layout s.slot) seed.toEmbedding).trans
    (finCongr (congrArg (fun t => edgeCapacity e t n) cap)).toEmbedding
local notation3 "L" => (s.result e q).pack.layout
local notation3 "key" => (sID).trans (F.sites.trans Fin.valEmbedding)
local notation3 (prettyPrint := false) "slices" => (fun v => Layer.orderedCuts s.input (CutCircuit.denseRows (raw child).layout s.slot)
  portID v e s.label s.perm name s.orient (0,false) q eID)

set_option maxHeartbeats 2100000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full immutable tape image is obtained from the selected ready table, the
old and saved endpoint pins, and the independently verified child records.
The geometric measurement bounds each population and the row-count pass bounds
every physical tile, including unused ordinal slots. -/
theorem frozen_node_fixed (hm : 0 < m) (radius : ℝ) (hk : 0 < k) {ν u v : ℝ} (measure : s.Measurements hk radius ν u v)
    (x : σ → Bool) (lit : ∀ b,x (literal b) = b)
    (ready : Ready e pop col code seed (raw child) s.bin s.positive oldSite orig dummy x)
    (cuts : ComputesCuts (m := m) pop code s.perm cut)
    (oldEnds : Views.EndpointData (raw child).layout oldF oldSite orig portID x)
    (ends : Views.EndpointData L F sID eID portID x) (enabled : ∀ r,x (occupied r) = true ↔ r ∈ Set.range eID)
    (hist : ∀ a i,value (fun j => counts.eval x (a,i,j)) = i.elim (s.matched a) (q a).val)
    (previous : S.Section (carried.eval x) key (FrozenTape.carriedRows e s.input states))
    (hw : ∀ v,value (x ∘ work (oldSite v)) = (states v).work)
    (he : ∀ v,value (x ∘ extent (oldSite v)) = (states v).size)
    (hin : ∀ v,(states v).incoming = incoming (raw child).layout v)
    (paid : ∀ v,(states v).work ≤ (data v.1).payload v.2) (hp : ∀ r,ports r = true ↔ r ∈ Set.range portID)
    {factor T M U : ℕ} (cert : s.RecordFactor e factor) (hT : 0 < T)
    (childCap : ∀ i,RecordsWithin (child i) (data i) true T)
    (recordsFit : loadMultiplier e*factor*k*T ≤ M)
    (binsFit : (measured_population_cap (I := I) (B := Bin) e radius).choose*(factor*k*T) ≤ U)
    (room : HookTape.sourceRoom e (0,false) M U < 2^w) :
    (FrozenTape.Node.schema e (0,false) (A := NamedSeed I Bin d') S rows np w).Image
      ((FrozenTape.Node.frame e (0,false) hm seed.toEmbedding carried oldF (Views.literalFields F literal) cut counts
        work extent col.occupied ports occupied).eval x) key
      (roundSites e s.input s.label s.perm s.orient (0,false) q name position sID eID portID states slices) := by
  cases cap
  exact s.frozen_node e q data S pop col code seed oldSite portID dummy oldF F literal counts cut carried work
    extent ports occupied states name position hm radius hk measure x lit ready cuts oldEnds ends enabled hist
    previous hw he hin paid hp cert hT childCap recordsFit binsFit room

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
