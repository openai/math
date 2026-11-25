import OAI.Hierarchy.DescentTerminalProfileCodes
import OAI.Hierarchy.DescentPackedMatchedInput

namespace OAI
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
/-- The same profile decoder used by the selector validator supplies the
finite actual fresh menu. Invalid unselected codes emit the zero field. -/
def profileField {C : ℕ} (width : ℕ) (field : ℕ→Profile C→Fin 6→ℕ) (z code : ℕ) (q : Fin 6) : Cell width :=
  (DescentTerminalEpochFlags.decode C code).elim 0 (fun p=>word width (field z p q))

theorem profile_field {C : ℕ} (width : ℕ) (field : ℕ→Profile C→Fin 6→ℕ) (z : ℕ) (p : Profile C) (q : Fin 6)
    (room : field z p q<2^width) : (profileField width field z (DescentTerminalEpochFlags.encode p) q).val=field z p q := by
  simp only [profileField,DescentTerminalEpochFlags.decode_encode,Option.elim_some,word,Nat.mod_eq_of_lt room]


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
