import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels
import OAI.Computability.BorderVNP.FiniteSewnFieldLanes

/-! # Tagged observation fibers after exterior sewing

At a retained vertex each old incidence lane has a physical source in the
new edge and port directories, or is clamped to zero. Appending these checks
to its lineage retains the same birth work and complete tagged entry for
every local assignment of the sewn network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew Diagonal.CellEntries
open scoped Classical

variable {D ae ap be bp : ℕ} {A P U Free Cable : Type}
    [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (progs : Site.Programs N)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port

/-- The same vertex and birth program, with the physical sewn incidence
bank appended by the zero and copy interval records. -/
noncomputable def sewnPrograms : Site.Programs out := fun v =>
  let s := progs v
  let read := read₀ v ∘ Fin.cast s.size
  ⟨s.birth,stage s.program (incoming out v) (intervals read),.forced s.retention read,rfl⟩

/-- The complete tag at every sewn input has the predecessor's ordered
observations and scalar-ID multiplicities under the same birth predicate. -/
theorem sewnTagModels {Param Gadget : Type*} (tags : N.Tables (Entry Param Gadget))
    (number : Gadget ↪ ℕ) (pred : N.Site → (ℕ → Bool) → Prop)
    (model : Site.Programs.TagModels N oldEdge oldPort progs tags number pred) :
    Site.Programs.TagModels out edge port
      (sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port progs)
      (B.layout.externalTables gw freeLane owner aligned (B.tables (FineView.tables N lane tags))) number pred := by
  intro v z x
  obtain ⟨physical,table⟩ := sewnRead_table N lane B gw freeLane owner aligned oldEdge oldPort edge port tags v z x
  let s := progs v
  let read := read₀ v ∘ Fin.cast s.size
  let input := inputWords out edge port v z x
  change Nonempty (Site.TagRead s.birth (s.retention.readInput (oldInput s.program read input))
    (fun g => pred v (Site.Programs.extendWork g)) _ number)
  rw [table]
  exact (congrArg (fun w => Nonempty (Site.TagRead s.birth (s.retention.readInput w)
    (fun g => pred v (Site.Programs.extendWork g)) _ number))
    (funext fun k => physical (Fin.cast s.size k))).mpr (model v _ _)

end Packing.SewnField

end BorderVNP
end Computability
end OAI
