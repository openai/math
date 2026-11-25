import OAI.Hierarchy.DescentOrdinaryMetaRAM

namespace OAI
/-! # Endpoint, live and width fields of the eleven-word parent key -/
namespace Hierarchy.DescentOrdinarySignedMeta
open DescentSIMDLookup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
def tests {a : ℕ} (v : Fin 11→Cell a) : Bool×Bool :=
  (decide ((v 2).val=(v 0).val ∧ (v 1).val=(v 5).val),
   decide ((v 4).val=(v 0).val ∧ (v 3).val=(v 5).val))

def activeRaw {a : ℕ} (v : Fin 11→Cell a) := decide (0<(v 10).val) && ((tests v).1 || (tests v).2)

def rawFlags {a : ℕ} (x : Cell (a*11)) (core : Cell 1) : Cell (1*4) :=
  let v:=(encode a 11).symm x
  if activeRaw v then flags true (tests v).1 (tests v).2 (decide (core.val=1)) else 0

def rawUnits {a b : ℕ} (x : Cell (a*11)) (_ : Cell 1) : Cell b :=
  let v:=(encode a 11).symm x
  if activeRaw v then (v 10).val else 0

end
end Hierarchy.DescentOrdinarySignedMeta

end OAI
