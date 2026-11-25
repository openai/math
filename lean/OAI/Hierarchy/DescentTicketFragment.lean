import OAI.Hierarchy.DescentOperandStateCodec

namespace OAI
/-! # Resolving the four retained operand-header words and the eight measured ordinary ticket fields -/
namespace Hierarchy
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks
open scoped Classical Fin.CommRing
noncomputable section
namespace DescentPackedOperand.Public
def fragment {b : ℕ} (marked : Bool) (peer start chunk grain : Cell (b+2)) : Fragment b :=
  ⟨.cable,0,peer,0,chunk,false,false,marked,start,grain⟩

end DescentPackedOperand.Public

namespace DescentPriorOperandColumns
variable {k : ℕ}
structure Side (k : ℕ) where
  donor : Cell (k+2)
  firstCapture : Bool
  secondCapture : Bool
  marked : Bool
  start : Cell (k+2)
  grain : Cell (k+2)

def Side.withHeader (t : Side k) (p : Pointer) (fit : ∀f,p.header f<2^(k+2)) : Fragment k :=
  ⟨match p with | .privateWord _=>.carried | .cable _ _ _=>.cable | .pin _ _=>.pin,
    t.donor,⟨p.header 1,fit 1⟩,⟨p.header 2,fit 2⟩,⟨p.header 3,fit 3⟩,
    t.firstCapture,t.secondCapture,t.marked,t.start,t.grain⟩

end DescentPriorOperandColumns

namespace DescentOrdinaryLocalFragment
variable {k : ℕ}
def route (x : Fragment k) (peer ticket : Cell (k+2)) : Fragment k :=
  {x with peer:=if x.kind=.cable then peer else x.peer, name:=if x.kind=.cable then ticket else x.name}

theorem carried (x : Fragment k) (peer ticket : Cell (k+2)) (kind : x.kind=.carried) :
    resolve (route x peer ticket)=.carried x.donor.val x.name.val :=by simp [resolve,route,kind]

theorem exterior (x : Fragment k) (peer ticket : Cell (k+2)) (kind : x.kind=.pin) :
    resolve (route x peer ticket)=.pin x.name.val x.chunk.val :=by simp [resolve,route,kind]

theorem captured (x : Fragment k) (peer ticket : Cell (k+2)) (second : Bool)
    (kind : x.kind=.cable) (firstTag : x.firstCapture=(!second)) (secondTag : x.secondCapture=second) :
    resolve (route x peer ticket)=(if second then Key.second else Key.first) x.donor.val peer.val ticket.val x.chunk.val :=by
  cases second <;> simp [resolve,route,kind,firstTag,secondTag]

theorem surviving (x : Fragment k) (peer ticket : Cell (k+2)) (kind : x.kind=.cable)
    (one : x.firstCapture=false) (two : x.secondCapture=false) :
    resolve (route x peer ticket)=resolve (Public.fragment x.marked peer x.start x.chunk x.grain) :=by
  cases marked : x.marked <;> simp [resolve,route,Public.fragment,kind,one,two,marked]

end DescentOrdinaryLocalFragment
end
end Hierarchy

end OAI
