import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # A receiver's stem descriptor from observed endpoints and distinct neighbors -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetFieldAssembler
open scoped Classical
noncomputable section

def stemOrdinal (here : ℕ) (neighbors : Finset ℕ) (e : ℕ) :=
  ((insert here neighbors).filter (fun x=>x<e)).card

def stemWord (here : ℕ) (neighbors : Finset ℕ) (s oldHub : Bool)
    (a : Option (ℕ×ℕ)) : Meta :=
  match a with
  | none=>.blank
  | some (src,dst)=>
    if src=here ∨ dst=here then
      ⟨true,stemOrdinal here neighbors src,stemOrdinal here neighbors dst,
       stemOrdinal here neighbors here,decide (here∉neighbors),s || !oldHub,1⟩
    else .blank

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
