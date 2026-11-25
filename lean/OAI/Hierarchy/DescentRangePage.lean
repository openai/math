import Mathlib.Data.Fin.Basic

namespace OAI
namespace Hierarchy.DescentRetainedRangeDigits
def page (j : Fin 3) : Fin 7:=⟨4+j.val,by have:=j.isLt;omega⟩
end Hierarchy.DescentRetainedRangeDigits

end OAI
