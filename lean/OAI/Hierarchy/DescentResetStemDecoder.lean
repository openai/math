import OAI.Hierarchy.DescentResetStemSample
import OAI.Hierarchy.DescentCommonHostEdges

namespace OAI
/-! # Both endpoints of a reset stem from its measured signed window -/
namespace Hierarchy.DescentResetStemDecoder
open DescentChosenRouter DescentCommonHost DescentContacts DescentRelativeContacts
open scoped Classical
noncomputable section

def nodes {V : Type} {n h : ℕ} (graph : NonlinearExpanders.Graph n h) (s : Bool) (v : V)
    (key : Endpoint (2^n)×Bool) :
    Option (Node V (V×Endpoint (2^n)) (DescentCommonPalette.rotor graph).Site ×
            Node V (V×Endpoint (2^n)) (DescentCommonPalette.rotor graph).Site) :=
  let z := (v,key.1)
  if key.2 then
    key.1.2.map (fun j=>(.trunk s z,.good s (v,key.1.1.2) ((DescentCommonPalette.rotor graph).attach (j,false))))
  else some (.trunk s z,.fall s z [])

/-- At a paid port the input row names the rotor cell. At the fallback port
the picked endpoint names the root of the selected binary tree. -/
theorem nodes_public {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k n h : ℕ} (P : Placement V I H A k (2^n)) (graph : NonlinearExpanders.Graph n h)
    (m : ℕ) (code : H↪V×Endpoint (2^n)) (s : Bool) (p : P.Public) :
    let z:=shortName m (publicAddress P code p)
    nodes graph s z.1 (z.2,p.isLeft)=some (.trunk s z,publicNode P graph m code s p) := by
  rcases p with ⟨g,j⟩|t <;> rfl

end
end Hierarchy.DescentResetStemDecoder

end OAI
