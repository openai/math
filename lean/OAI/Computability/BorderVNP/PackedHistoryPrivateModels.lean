import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedBankDenseRoundModels

/-! # Field models on the actual site-program lineage

The local values and the observation fibers live on the very same program.
A normalized stage installs its ordered interval rows and true birth programs.
The public rectangular row numbers preserve every child input on the next
dense save.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening

/-- All physical site factors equal the contraction of their current private
programs, interpreted with the actual signed field entries. -/
def Site.Programs.FieldModels {D ne np : ℕ} {K : Type*} [Field K] {P : Type*} [Fintype P] {bits : P → ℕ}
    (p : Pack D P bits K) (rows : p.layout.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (programs : Site.Programs p.layout) (values : ℕ → K) : Prop :=
  ∀ v, (programs v).program.Local ∧
    (programs v).program.Models p.layout rows ports v (programs v).size (fieldWeight values) p.table

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.Stage

open Crossing Shortening Shortening.PublicParallel Cover Epoch Epoch.Round Packing Packing.Inherited
open scoped Classical

variable {D m k d d' E np ns ne : ℕ} [NeZero D] {K P I B : Type} [Field K]
    [Fintype P] [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B d' child) (e : PaidIdentity K D m) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    (rows : ∀ j, (child j).pack.layout.Edge ↪ Fin E) (portID : P ↪ Fin np)
    (hcap : s.rowCount = k*E) (hslot : ∀ z, (s.slot z).val = (parallelName rows z).val)
    (siteID : (s.result e q).pack.layout.Site ↪ Fin ns) (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (seed : ((I → Deck (d'+1)) × B) → ℕ) (number : e.Entry → ℕ)
    (values : ℕ → K) (paid : ∀ i, values (number i) = e.entry i)
    (children : ∀ i, Site.Programs.FieldModels (child i).pack (rows i) portID (old i) values)

local notation3 "nextPorts" => Parallel.portRows k portID
local notation3 "oldRows" => CutCircuit.denseRows (raw child).layout s.slot
local notation3 "actualCuts" => fun v => Layer.orderedCuts s.input oldRows nextPorts v e s.label s.perm seed s.orient (0,false) q edgeID
local notation3 "private₀" => s.privatePrograms e q old siteID edgeID nextPorts seed number
local notation3 "prog₀" => fun i v => (old i v).program

/-- The site belonging to the lineage object is the actual executable installed program. -/
theorem privatePrograms_installed (v : (s.result e q).pack.layout.Site) :
    (private₀ v).program =
      roundSites e s.input s.label s.perm s.orient (0,false) q seed number siteID edgeID nextPorts
        (fun v => (old v.1 v.2).program) actualCuts v := by
  cases v <;> rfl

include hcap hslot paid children in
/-- Every site of this branch has its exact field model on the program whose entire
birth-to-current observation fiber is retained by the history. -/
theorem privatePrograms_models :
    Site.Programs.FieldModels (s.result e q).pack edgeID nextPorts private₀ values := by
  intro v
  have hl := s.installed_local portID prog₀ (fun i v => (old i v).size) e q seed number siteID edgeID
    (fun i v => (children i v).1) v
  have hm := s.installed_models rows portID hcap hslot prog₀ (fun i v => (old i v).size) values
    (fun i v => (children i v).2) e q seed number paid siteID edgeID (fun i v => (children i v).1) v
  cases v <;> exact ⟨hl,hm⟩

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
