import OAI.Computability.BorderVNP.PackedInheritedWorkStep
import OAI.Computability.BorderVNP.PackedInheritedWorkPublicCap
import OAI.Computability.BorderVNP.PackedHistoryPrivateSites

/-! # Exact width outputs for the installed lineage and its physical record budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.PublicParallel Shortening.PublicEndpoints
open Epoch Epoch.Round Cover PackedHistoryCircuit PackedHistoryCircuit.Normalized InheritedBank
open VPVNP.VerifierNetwork
open private cuts from OAI.Computability.BorderVNP.PackedHistoryPrivateSites
open scoped Classical BorderVNP.Epoch.Cube

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {D m k V E n np w d lev : ℕ} [NeZero D] {K Bin P B σ : Type} [Field K] [Fintype Bin] [Fintype P]
variable [Fintype σ] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K (Cube D) d}
variable (e : PaidIdentity K D m) (s : Stage m Bin lev child) (q : s.Index e)
variable (old : ∀ i, Site.Programs (child i).pack.layout) (names : ∀ i, (child i).pack.layout.Site ↪ Fin V)
variable (pdir : Directory (s.result e q) (siteCapacity e (k*V) n) E)
variable (seed : ((Cube D → Deck (lev+1)) × Bin) ↪ Fin n)
variable (port : Fin k × P ↪ Fin np) (binName : ((Cube D → Deck (lev+1)) × Bin) → ℕ) (position : e.Entry → ℕ)
variable (src : NodeFields (A := ((Cube D → Deck (lev+1)) × Bin)) (k := k) (V := V) (E := E)
  (n := n) (np := np) (w := w) e B σ)
local notation3 "next" => s.privatePrograms e q old pdir.sites pdir.cables port binName position
local notation3 "saved" => ((s.result e q).dense pdir.cables).pack.layout
local notation3 "layers" => cuts e s q pdir.cables port binName
local notation3 "tape" => roundSites e s.input s.label s.perm s.orient (0,false) q binName position
  pdir.sites pdir.cables port (fun z => (old z.1 z.2).program) layers

/-- The selected node computes both actual fields of the canonical
privatePrograms lineage in stable cut order. Word room follows from
the checked physical stage's resource factor and the incoming child
record caps. -/
theorem node_installed (room : ∀ a, s.matched a < 2^w) (x : σ → Bool)
    (site : pdir.sites = siteRows e s.input (parallelName names) seed)
    (childOK : ∀ i, Covers (names i) (fun v => (old i v).program.size)
      (Frame.initial fun z => src.child (i,z)) x)
    (hist : x ∘ src.guess = NamedReceipt.word s room q)
    (ready : PublicEndpoints.Represents saved pdir.dense.sites pdir.dense.cables pdir.dummy (x ∘ src.saved))
    (attach : ∀ p, src.host (port p) = (pdir.dense.sites ((saved).attach p)).val)
    (width : ∀ p, src.width (port p) = bits p.2) (fits : ∀ i, src.width i < 2^w)
    (holes : ∀ i ∉ Set.range port, src.width i = 0)
    (data : ∀ i, RecordData (child i).pack.layout) {C T : ℕ} (hT : 0<T) (cert : s.RecordFactor e C)
    (cap : ∀ i, RecordsWithin (child i) (data i) true T)
    (charge : ∀ i v, (old i v).program.publicNodes ≤ (data i).prior v ∧ (old i v).program.expandedLoad ≤ (data i).payload v)
    (word : 2*(loadMultiplier e*C*k*T) < 2^w) :
    Covers pdir.dense.sites (fun v => (next v).program.work) (column (node e seed src) false) x ∧
      Covers pdir.dense.sites (fun v => (next v).program.size) (column (node e seed src) true) x := by
  have same (v) : (next v).program = tape v := by rcases v with v | z <;> rfl
  have bound := s.privatePrograms_bankWithin e q old pdir.sites pdir.cables port binName position data cert true hT cap charge
  have hfit (v) : (tape v).size < 2^w := by
    rw [← same v]
    exact size_lt_of_bankWithin (s.result e q) next bound word v
  simpa only [same] using node_covers e s names q pdir seed src port position binName
    (fun i v => (old i v).program) layers room x site childOK hist ready attach width fits holes hfit

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
