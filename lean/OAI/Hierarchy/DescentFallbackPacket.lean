import OAI.Hierarchy.DescentSharedBookFields
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # The signed source packet and packed ranks at a predecessor host -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentSharedBookScan DescentSharedCableNames.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r field : ℕ}

abbrev Input (D L cap n r : ℕ) :=
  (Fin L ⊕ Fin D×Fin L) ⊕ ((Fin L×Fin (2*cap)) ⊕ Fin (DescentSharedBookScan.width r (2^n) D))

def inputCount (D L cap n r : ℕ) := L+D*L+((L*(2*cap))+DescentSharedBookScan.width r (2^n) D)
def number : Input D L cap n r ≃ Fin (inputCount D L cap n r) :=
  (Equiv.sumCongr ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

abbrev Packet (D L cap n r field : ℕ) := Input D L cap n r→Cell field
def encodePacket (v : Packet D L cap n r field) :=
  encode field (inputCount D L cap n r) (fun i=>v (number.symm i))
def packet (s : Cell (field*inputCount D L cap n r)) : Packet D L cap n r field :=
  fun q=>(encode field (inputCount D L cap n r)).symm s (number q)
@[simp] theorem packet_encode (v : Packet D L cap n r field) : packet (encodePacket v)=v := by
  funext i
  simp [packet,encodePacket]

def localWord (v : Packet D L cap n r field) (i : Fin L) := (v (.inl (.inl i))).val
def peer (v : Packet D L cap n r field) (j : Fin D) (i : Fin L) := (v (.inl (.inr (j,i)))).val
def signed (v : Packet D L cap n r field) (i : Fin L) (s : Fin (2*cap)) :=
  DescentSignedCableCodec.decode D cap (((v (.inr (.inl (i,s)))).val:ℕ):Cell (DescentSignedCableCodec.width D cap))
def score (v : Packet D L cap n r field) (address : Fields r (2^n) D) :=
  (v (.inr (.inr (fieldId address)))).val

def arrival (v : Packet D L cap n r field) (which : Bool) (i : Fin L) (s : Fin (2*cap)) : Option (Fin D×ℕ) := do
    let ch←signed v i s
    if ch.target=which then
      let ptr:=peer v ch.neighbor i
      if 0<ptr then some (ch.neighbor,ptr-1) else none
    else none

variable {H G : ℕ}

/-- The neighbor window is zero-filled outside the mounted old roster. Every real stencil
has its own presence bit, so a true shape zero can be sent through the same port. -/
def inputs (own : Fin H→Fin G→Fin L→ℕ) (roster : Fin H→Fin D→Option (Fin H))
    (signs : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ) (h : Fin H) (g : Fin G) :
    Packet D L cap n r field
  | .inl (.inl i)=>(own h g i:Cell field)
  | .inl (.inr (j,i))=>((roster h j).elim 0 (fun v=>own v g i+1):Cell field)
  | .inr (.inl (i,z))=>((DescentSignedCableCodec.encode (signs h g i z)).val:Cell field)
  | .inr (.inr j)=>(rank h j:Cell field)

namespace Projected
def count (L cap : ℕ) := 2*L+(2*cap)*L
abbrev Column (L cap : ℕ) := (Fin 2×Fin L) ⊕ (Fin (2*cap)×Fin L)
def column (L cap : ℕ) : Column L cap≃Fin (count L cap) :=
  (finProdFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv

end Projected

end
end Hierarchy.DescentFallbackPeriod

end OAI
