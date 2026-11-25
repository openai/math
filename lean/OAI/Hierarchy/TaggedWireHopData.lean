import OAI.Hierarchy.ProbeRouteOccurrences

namespace OAI
/-! # The bit and occurrence indices of a routed word -/

namespace Hierarchy.WireTelescope
variable {E I : Type}

/-- A bit of the ordinary input resources, and every occurrence of its route. -/
abbrev Bundle (bits : I→ℕ) := Σi,Fin (bits i)
abbrev Hop (route : I→List E) (bits : I→ℕ) := Σs:Bundle bits,Fin (route s.1).length

def hopEdge (route : I→List E) (bits : I→ℕ) (h : Hop route bits) : E := (route h.1.1).get h.2

end Hierarchy.WireTelescope

end OAI
