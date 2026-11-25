import OAI.Computability.BorderVNP.FiniteSewnFieldLanes
import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.FiniteHistoryFieldDirectories

/-! # Actual executable field directories at the exterior-sewn terminal

The inherited original and paid programs read the old lanes reconstructed
by maximal sparse interval records. The new directory realizes the complete
fine view, interval sewing, and free-port grouping on every assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew FiniteDiagonal
open scoped Classical

variable {D : ℕ} {A P U Free Cable : Type} [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    {be bp : ℕ} (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp)
    {F : Type*} [Field F] {T : N.Tables F} (S : FieldSiteDirectory N T) (loc : ∀ v, (S.site v).Local)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "source" => sewnRead N lane B gw freeLane owner aligned S.edgeID S.portID edge port

/-- Original site's private source numbering pulled back through its true
incoming-width equality. -/
noncomputable def programRead (v : N.Site) (k : Fin (S.site v).incoming) : Option (Fin (incoming out v)) :=
  source v (Fin.cast (S.incoming v) k)

local notation "read₀" => programRead N lane B gw freeLane owner aligned edge port S

/-- The current terminal program retains every original box and scalar
visit and appends the real zero/equality interval constraints for sewing. -/
noncomputable def sewnSite (v : N.Site) : Site :=
  stage (S.site v) (incoming out v) (intervals (read₀ v))

local notation "site₀" => sewnSite N lane B gw freeLane owner aligned edge port S

include loc in
/-- At every final site, all physical staged reads lie within its own full bank. -/
theorem sewnSite_local (v : N.Site) : (site₀ v).Local :=
  stage_local (S.site v) (loc v) _ _ (intervals_cover (read₀ v))

include loc in
/-- Every actual final site's executable scalar value equals the fine-view
table with its partner wires sewn and remaining port slots grouped. -/
theorem sewnSite_models (v : N.Site) :
    (site₀ v).Models out edge port v rfl (fieldWeight S.values)
      (B.layout.externalTables gw freeLane owner aligned (B.tables (FineView.tables N lane T))) := by
  intro z x
  let input := inputWords out edge port v z x
  have reads := sewnRead_table N lane B gw freeLane owner aligned S.edgeID S.portID edge port T v z x
  obtain ⟨physical,table⟩ := reads
  change (stage (S.site v) (incoming out v) (intervals (read₀ v))).value (fieldWeight S.values) input = _
  rw [stage_value (S.site v) (loc v) _ _ (intervals_cover (read₀ v)),table]
  refine Eq.trans ?_ (S.models v _ _)
  apply congrArg ((S.site v).value (fieldWeight S.values))
  exact funext (fun k => physical (Fin.cast (S.incoming v) k))

/-- The field raw-assignment expansion's actual exterior-sewn directory,
using the true new named sparse edge and port rows. -/
noncomputable def sewnDirectory : FieldSiteDirectory out
    (B.layout.externalTables gw freeLane owner aligned (B.tables (FineView.tables N lane T))) where
  edgeCapacity := be
  portCapacity := bp
  edgeID := edge
  portID := port
  site := site₀
  values := S.values
  incoming _ := rfl
  models := sewnSite_models N lane B gw freeLane owner aligned edge port S loc

end Packing.SewnField

end BorderVNP
end Computability
end OAI
