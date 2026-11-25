import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentPinDigits
import OAI.Hierarchy.DescentExteriorSpine

namespace OAI
/-! # The true external port and its current host/block coordinate -/

namespace Hierarchy.DescentSixParty.PinCohorts
open DescentCompiler DescentGL DescentColonies DescentExterior
noncomputable section

variable {F P : Type} [Field F] {d k tail : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ}
variable {S : AtomSchedule} {W W' : MarkedWorld F d P bits}
variable {i j z z' D D' t t' h h' : ℕ}

def active (r : Reached W G q ε S k i z D t h) (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (p : P) :
    Bits (S.groupWidth k tail i+k) :=
  let v:=W.graph.attach p
  (address _).symm ((S.resetInputDigits base radix i).symm ((r.placement.pos v).1,r.placement.block v))

def host (r : Reached W G q ε S k i z D t h) (p : P) := (r.placement.pos (W.graph.attach p)).2

abbrev Step (r : Reached W G q ε S k i z D t h) (next : Reached W' G q ε S k j z' D' t' h')
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k) :=
  Spine (active r base radix) (active next base radix) (host r) (host next) k

/-- The group and block fields use the same binary places as the linear split. -/
theorem active_parts (r : Reached W G q ε S k i z D t h) (base : S.baseGroups=2^tail)
    (radix : S.radix=2^k) (p : P) :
    let u:=W.graph.attach p
    let x:=splitRows (S.groupWidth k tail i) k (active r base radix p)
    (address _ x.1).val=(r.placement.pos u).1.val ∧ address _ x.2=r.placement.block u := by
  let site := W.graph.attach p
  exact separate (S:=S) (i:=i) base radix (r.placement.pos site).1 (r.placement.block site)

end
end Hierarchy.DescentSixParty.PinCohorts

end OAI
