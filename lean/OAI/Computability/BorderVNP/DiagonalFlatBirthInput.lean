import OAI.Computability.BorderVNP.DiagonalNativeBirthInputs

/-! # Exact physical birth input under the final flat port numbering -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Shortening Shortening.Adaptive Diagonal.CellEntries Site.Programs

variable {k D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {R : Type*} (b : ℕ)
    [Fintype (Port k P b)] (p : Pack D (Port k P b) (width bits k b) R)
    (edges : p.layout.Edge ↪ Fin ne) (ports : Port k P b ↪ Fin np) (v : p.layout.Site)
    (s : Lineage (Inherited.incoming p.layout v))

/-- Flattening the public exterior rows retains the original site checker and
its complete input vector on the true inverse row-major port labeling. -/
theorem birthInput_flat (x : PowerInput (flattenPack b p).layout) :
    birthInput (flattenPack b p).layout edges (Flat.portRows b ports) v
      (s.castWidth (Flat.incoming_eq b p v).symm) x =
      birthInput p.layout edges ports v s ⟨x.edges,nestedPorts bits k b x.ports⟩ := by
  apply congrArg (fun a => extendWork (s.retention.readInput a))
  funext j
  exact flat_inputWords b p edges ports v (fun u => x.edges u.val) (fun u => x.ports u.val) (Fin.cast s.size j)

end Packing.Inherited.Site.Lineage

end BorderVNP
end Computability
end OAI
