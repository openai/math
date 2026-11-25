import OAI.Hierarchy.DescentOrdinaryBornInventory

namespace OAI
/-! # Numerical anchor, signed side, and raw role of a live newborn mouth -/
namespace Hierarchy.DescentOrdinaryBorn.RolePorts
open DescentSIMDLookup
noncomputable section

/-- Zero is valid for each coordinate separately. The acquired live node and
its measured arity distinguish an original anchor from a padding position. -/
def numeral (m : Mouth) (f : Fin 3) : ℕ :=
  if f.val=0 then m.anchor.val else if f.val=1 then m.rawRole else m.target.toNat

def value (bits : ℕ) (entry : Option Mouth) (f : Fin 3) : Cell bits :=
  ⟨(entry.elim 0 (fun m=>numeral m f)) % 2^bits, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem coordinates (m : Mouth) :
    numeral m 0=m.anchor.val ∧ numeral m 1=m.rawRole ∧ numeral m 2=m.target.toNat :=by
  exact ⟨rfl,rfl,rfl⟩

theorem raw_bounded (m : Mouth) : m.rawRole<11 :=by
  cases m with
  | mk r side chunk_ =>
    cases r with
    | original s=>change 0<11;decide
    | arm s=>change 1+s.val<11;have:=s.isLt;omega
    | supply s=>change 3+s.val<11;have:=s.isLt;omega

theorem value_live (bits : ℕ) (room : 11≤2^bits) (m : Mouth) (f : Fin 3) :
    (value bits (some m) f).val=numeral m f :=by
  have bounded : numeral m f<11:=by
    unfold numeral
    split
    · have: m.anchor.val<2:=m.anchor.isLt
      omega
    · split
      · exact raw_bounded m
      · cases m.target <;> decide
  exact Nat.mod_eq_of_lt (bounded.trans_le room)

end
end Hierarchy.DescentOrdinaryBorn.RolePorts

end OAI
