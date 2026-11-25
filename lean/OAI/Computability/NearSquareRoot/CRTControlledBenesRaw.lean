import OAI.Computability.NearSquareRoot.CRTControlledBenes

/-! # Word-table operations for one Beneš node -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes

abbrev RawTable := List (List Bool × List Bool)

/-- Separate the switch bit from the remaining port address. -/
def unconsRow (x : List Bool × List Bool) : Entry (List Bool) :=
  ((x.1.headD false, x.1.tail), (x.2.headD false, x.2.tail))

def rawLabels (t : RawTable) : Labels (Bool × List Bool) :=
  prepareControls (t.map unconsRow)

/-- Strip the switched bit from both addresses of the rows selected for a lane. -/
def childTable (t : RawTable) (b : Bool) : RawTable :=
  (t.filter (fun row => decide (((row.1.headD false) ^^
      (label (rawLabels t) (false,row.1.tail)).2) = b))).map (fun row => (row.1.tail,row.2.tail))

end Benes

end NearSquareRoot
end Computability
end OAI
