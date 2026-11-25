import OAI.Computability.BorderVNP.FiniteDiagonalCubeDirectories
import OAI.Computability.BorderVNP.PackedHistoryPrivateModels
import OAI.Computability.BorderVNP.PackedInheritedFlatValue

/-! # Reading the actual modeled site programs as field directories

A history's edge rows, port rows, scalar dictionary, and current sparse
programs supply the field directory consumed by the packet expansion. The
flat version uses the physical port reindex of the last adaptive step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldSiteDirectory

open Crossing Shortening Shortening.Adaptive Packing Packing.Inherited
open scoped Classical

variable {D ne np : ℕ} {F : Type*} [Field F] {P : Type} [Fintype P] {bits : P → ℕ}

/-- Form the raw-assignment directory from the current executable programs and
their proven field invariant at the actual row numbers. -/
noncomputable def ofPrograms (p : Pack D P bits F) (edges : p.layout.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (programs : Site.Programs p.layout) (values : ℕ → F)
    (h : Site.Programs.FieldModels p edges ports programs values) : FieldSiteDirectory p.layout p.table where
  edgeCapacity := ne
  portCapacity := np
  edgeID := edges
  portID := ports
  site v := (programs v).program
  values := values
  incoming v := (programs v).size
  models v := (h v).2

/-- Flattening the terminal port labels gives the same executable private
programs, with the flat port ordinals and the true flattened field tables. -/
noncomputable def ofFlatPrograms {k : ℕ} (n : ℕ) [Fintype (Port k P n)] (p : Pack D (Port k P n) (width bits k n) F)
    (edges : p.layout.Edge ↪ Fin ne) (ports : Port k P n ↪ Fin np)
    (programs : Site.Programs p.layout) (values : ℕ → F)
    (h : Site.Programs.FieldModels p edges ports programs values) :
    FieldSiteDirectory (flattenPack n p).layout (flattenPack n p).table where
  edgeCapacity := ne
  portCapacity := np
  edgeID := edges
  portID := Flat.portRows n ports
  site v := (programs v).program
  values := values
  incoming v := (programs v).size.trans (Flat.incoming_eq n p v).symm
  models v := Site.Models.flattenPack n p edges ports v (programs v).program (programs v).size
    (fieldWeight values) (h v).2

end FiniteDiagonal.FieldSiteDirectory

end BorderVNP
end Computability
end OAI
