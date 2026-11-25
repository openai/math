import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! # First-grain coordinates and origin search on the retained signed cable words -/
namespace Hierarchy.DescentTerminalSignedGrainWord
open DescentSIMDLookup DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap : ℕ}

def first (u : Stage.Live D cap) : Fin (D*cap) :=
  ⟨u.neighbor.val*cap+(u.wire.val-u.within.val),by
    have low:=Nat.sub_le u.wire.val u.within.val
    calc _<u.neighbor.val*cap+cap:=Nat.add_lt_add_left (low.trans_lt u.wire.isLt) _
         _=(u.neighbor.val+1)*cap:=by rw [Nat.add_mul,Nat.one_mul]
         _≤D*cap:=Nat.mul_le_mul_right cap u.neighbor.isLt⟩

def grainId (u : Stage.Live D cap) : Fin (D*cap*cap) := finProdFinEquiv (first u,u.within)

def project (D cap : ℕ) (x : Cell (DescentSignedCableCodec.width D cap)) : Cell (Packed.bits (D*cap*cap)) :=
  Packed.token ((DescentSignedCableCodec.decode D cap x).map grainId)

def point (D cap : ℕ) (x : Cell (Packed.bits (D*cap*cap))) : Option (ℕ×ℕ) :=
  (Packed.readToken (D*cap*cap) x).map (fun t=>let p : Fin (D*cap)×Fin cap:=finProdFinEquiv.symm t;(p.1.val,p.2.val))

end
end Hierarchy.DescentTerminalSignedGrainWord

namespace Hierarchy.DescentOperandPriorIncidence
open DescentSIMDLookup DescentTerminalSignedGrainWord
open scoped Classical Fin.CommRing
noncomputable section

def sign (cap : ℕ) (s : Fin (2*cap)) : Fin 2 := (finProdFinEquiv.symm s : Fin 2×Fin cap).1

def seek {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (face : Fin 2) (x : ℕ×ℕ) :=
  (List.finRange (2*cap)).find? (fun j=>decide (sign cap j=face ∧ row j=some x))

/-- The old operand names the first grain even when it reads a later word of
the same cable. In a loop the source half of the signed census comes first. -/
def originIndex {cap : ℕ} (row : Fin (2*cap)→Option (ℕ×ℕ)) (key : ℕ×ℕ) :=
  match seek row 0 key with
  | some s=>some s
  | none=>seek row 1 key

def origin {D cap : ℕ} (words : Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) (key : ℕ×ℕ) :=
  let row s:=point D cap (project D cap (words s))
  (originIndex row key).bind (fun s=>DescentSignedCableCodec.decode D cap (words s))

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
