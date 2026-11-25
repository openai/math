import OAI.Hierarchy.DescentFallbackPacket

namespace OAI
/-! # The signed numerical stem sample in an original packed receiver row -/
namespace Hierarchy.DescentResetStemDecoder
open DescentFallbackPeriod DescentContacts
open scoped Classical
noncomputable section

/-- A missing or wrong-polarity old cable has no stem. A present cable uses the
same two exceptional bits as the rotor matrix and the fallback tree. -/
def sample {D L cap n r b : ℕ} (window : Packet D L cap n r b)
    (s : Bool) (lo : Fin L) (slot : Fin (2*cap)) : Option (Endpoint (2^n)×Bool) := do
  let pr ← arrival window s lo slot
  let own := localWord window lo
  return (DescentFallbackShapeTable.decode r (2^n) (own/2),decide (own%2=0 ∧ pr.2%2=0))

theorem empty {D L cap n r b : ℕ} (window : Packet D L cap n r b) (s : Bool)
    (lo : Fin L) (slot : Fin (2*cap)) (idle : arrival window s lo slot=none) :
    sample window s lo slot=none := by simp [sample,idle]

theorem occupied {D L cap n r b : ℕ} (window : Packet D L cap n r b) (s : Bool)
    (lo : Fin L) (slot : Fin (2*cap)) (peer : Fin D) (shape : Endpoint (2^n))
    (remote : ℕ) (badHere badThere : Bool)
    (left : localWord window lo=2*DescentFallbackShapeTable.cell r shape+badHere.toNat)
    (right : arrival window s lo slot=some (peer,2*remote+badThere.toNat))
    (depth : shape.1.1≤r) (bounded : shape.1.2<2^shape.1.1) :
    sample window s lo slot=some (shape,!(badHere || badThere)) := by
  have half : (2*DescentFallbackShapeTable.cell r shape+badHere.toNat)/2=
      DescentFallbackShapeTable.cell r shape := by cases badHere <;> simp; omega
  simp only [sample,right,left,half,DescentFallbackShapeTable.decode_cell r shape depth bounded]
  cases badHere <;> cases badThere <;> simp [Nat.add_mod]

end
end Hierarchy.DescentResetStemDecoder

end OAI
