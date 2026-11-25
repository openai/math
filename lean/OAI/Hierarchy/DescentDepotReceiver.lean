import Mathlib.Data.Fin.Basic

namespace OAI
/-! # Original host coordinate of a padded ordinary resolver row -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

variable {K : ℕ}

def receiver (H pitch : ℕ) (h : Fin K) : Option (Fin H) :=
  if v : 0<pitch ∧ h.val/pitch<H then some ⟨_,v.2⟩ else none

end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route

end OAI
