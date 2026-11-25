import OAI.Computability.BorderVNP.PackedBankRoundModels
import OAI.Computability.BorderVNP.PackedBankInheritedDenseCharges
import OAI.Computability.BorderVNP.PackedInheritedParallelValue
import OAI.Computability.BorderVNP.PackedInheritedDenseValue

/-! # Exact installed sparse sites on a normalized public crossing step

The selected stage sorts the parallel rectangular cable rows. A stage receipt
certifies their common capacity and occupied ordinals, so each child's program
retains the same incidence order on the normalized input. The physically ordered
layer, new birth programs and subsequent stable save all realize their actual
field tables on every assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening

/-- Reading an identically numbered public directory at an equal rectangle capacity preserves all local values. -/
theorem Site.Models.numbered {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {R : Type*} [AddCommMonoid R] (p : Pack D P bits R)
    (old : p.layout.Edge ↪ Fin m) (new : p.layout.Edge ↪ Fin n) (portID : P ↪ Fin np)
    (v : p.layout.Site) (s : Site) (hs : s.incoming = Inherited.incoming p.layout v)
    (weight : List (Bool × Option ℕ) → R) (hcap : n = m) (hnum : ∀ z, (new z).val = (old z).val)
    (model : s.Models p.layout old portID v hs weight p.table) : s.Models p.layout new portID v hs weight p.table := by
  subst n
  obtain rfl : new = old := DFunLike.ext _ _ fun z => Fin.ext (hnum z)
  exact model

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.Stage

open Crossing Shortening Shortening.PublicParallel Cover Epoch Epoch.Round Packing Packing.Inherited
open scoped Classical

variable {D m k d d' E np : ℕ} [NeZero D] {K : Type*} [Field K] {I B P : Type}
    [Fintype I] [Fintype B] [Fintype P] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (rows : ∀ i, (child i).pack.layout.Edge ↪ Fin E) (portID : P ↪ Fin np)
    (hcap : s.rowCount = k*E) (hslot : ∀ z, (s.slot z).val = (parallelName rows z).val)
    (programs : ∀ i, (child i).pack.layout.Site → Site)
    (incomingChild : ∀ i v, (programs i v).incoming = incoming (child i).pack.layout v)
    (values : ℕ → K)
    (models : ∀ i v, (programs i v).Models (child i).pack.layout (rows i) portID v
      (incomingChild i v) (fieldWeight values) (child i).pack.table)

local notation3 "nextPorts" => Parallel.portRows k portID
local notation3 "oldRows" => CutCircuit.denseRows (raw child).layout s.slot

include hcap hslot models in
/-- Parallel embedding and stable dense save preserve the child model at every physically numbered input site. -/
theorem input_models (i : Fin k) (v : (child i).pack.layout.Site) :
    (programs i v).Models s.input.layout oldRows nextPorts ⟨i,v⟩
      ((incomingChild i v).trans (s.input_incoming i v).symm) (fieldWeight values) s.input.table := by
  let t := programs i v
  have hp := Site.Models.parallelPacks (fun j => (child j).pack) rows portID i v t
    (incomingChild i v) (fieldWeight values) (models i v)
  have hin := (incomingChild i v).trans (Parallel.incoming_eq (fun j => (child j).pack.layout) i v).symm
  have hp' := Site.Models.numbered (raw child) (parallelName rows) s.slot nextPorts ⟨i,v⟩ t hin
    (fieldWeight values) hcap hslot hp
  exact Site.Models.densePack (raw child) s.slot nextPorts ⟨i,v⟩ t hin (fieldWeight values) hp'

variable (e : PaidIdentity K D m) (q : s.Index e) (binName : ((I → Deck (d'+1)) × B) → ℕ)
    (position : e.Entry → ℕ) (paid : ∀ i, values (position i) = e.entry i)
    {ns ne : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns) (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (localChild : ∀ i v, (programs i v).Local)

local notation3 "actualCuts" => fun v => Layer.orderedCuts s.input oldRows nextPorts v e s.label s.perm binName s.orient (0,false) q edgeID
local notation3 "install" => roundSites e s.input s.label s.perm s.orient (0,false) q binName position siteID edgeID nextPorts
  (fun v => programs v.1 v.2) actualCuts

include incomingChild localChild in
/-- Finite locality of all actually installed sites in the stable public descriptor order. -/
theorem installed_local (v : (s.result e q).pack.layout.Site) : (install v).Local :=
  roundSites_local e s.input s.label s.perm s.orient (0,false) q binName position oldRows siteID edgeID nextPorts
    _ actualCuts (fun u => (incomingChild u.1 u.2).trans (s.input_incoming u.1 u.2).symm) (fun u => localChild u.1 u.2)
    (fun u => Layer.ordered_perm s.input oldRows nextPorts u e s.label s.perm binName s.orient (0,false) q edgeID) v

include hcap hslot models localChild paid in
/-- Exact physical field table at every site of the selected branch, after the
children were embedded in their actual parallel slots and sorted before crossing. -/
theorem installed_models (v : (s.result e q).pack.layout.Site) :
    let hs := roundSites_incoming e s.input s.label s.perm s.orient (0,false) q binName position siteID edgeID nextPorts _ actualCuts v
    (install v).Models (s.result e q).pack.layout edgeID nextPorts v hs (fieldWeight values) (s.result e q).pack.table :=
  roundSites_models e s.input s.label s.perm s.orient (0,false) q binName position oldRows siteID edgeID nextPorts
    _ actualCuts (fun u => (incomingChild u.1 u.2).trans (s.input_incoming u.1 u.2).symm) (fun u => localChild u.1 u.2)
    (fun u => Layer.ordered_perm s.input oldRows nextPorts u e s.label s.perm binName s.orient (0,false) q edgeID)
    values paid (fun u => s.input_models rows portID hcap hslot programs incomingChild values models u.1 u.2) v

include hcap hslot models localChild paid in
/-- Saving the attained output at its stable sparse rows preserves the complete
installed programs and their physical local values for the following stage. -/
theorem installed_saved_models (v : (s.result e q).pack.layout.Site) :
    let p := (s.result e q).pack
    let saved := DirectoryCircuit.densePack p edgeID
    let hs := (roundSites_incoming e s.input s.label s.perm s.orient (0,false) q binName position siteID edgeID nextPorts _ actualCuts v).trans
      (dense_incoming p.layout edgeID v).symm
    (install v).Models saved.layout (CutCircuit.denseRows p.layout edgeID) nextPorts v hs (fieldWeight values) saved.table :=
  Site.Models.densePack (s.result e q).pack edgeID nextPorts v (install v) _ (fieldWeight values)
    (s.installed_models rows portID hcap hslot programs incomingChild values models e q binName position paid siteID edgeID localChild v)

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
