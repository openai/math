import OAI.Hierarchy.DescentNetworkReindex
import OAI.Hierarchy.DescentBitDescription

namespace OAI
/-! # Pure old-wire and old-port readdressing, down to each operand bit -/

namespace Hierarchy.DescentSixParty.PhysicalRename
open Computability.BorderVNP.Crossing DescentKernelHistory
open scoped Classical
noncomputable section
variable {d : ℕ} {P : Type} {bits : P→ℕ}
variable (N : Network d P bits) (s : Equiv.Perm N.Site) (e : Equiv.Perm N.Edge) (v : N.Site)
local notation "Q" => graph N s e

def incident (i : Incident N (s.symm v)) : Incident (Q) v := ⟨e i.val,by
  rcases i.property with source|target
  · exact Or.inl ((src N s e i.val).trans ((congrArg s source).trans (s.apply_symm_apply v)))
  · exact Or.inr ((dst N s e i.val).trans ((congrArg s target).trans (s.apply_symm_apply v)))⟩

def pin (p : Attached N (s.symm v)) : Attached (Q) v :=
  ⟨p.val,(congrArg s p.property).trans (s.apply_symm_apply v)⟩

def boundary : Boundary N (s.symm v) → Boundary (Q) v := Sum.map (incident N s e v) (pin N s e v)

theorem boundary_width (i : Boundary N (s.symm v)) :
    boundaryWidth (Q) v (boundary N s e v i)=boundaryWidth N (s.symm v) i := by
  cases i with
  | inl i => exact width N s e i.val
  | inr p => rfl

def boundaryBit (i : BitRef (boundaryWidth N (s.symm v))) : BitRef (boundaryWidth (Q) v) :=
  ⟨boundary N s e v i.1,Fin.cast (boundary_width N s e v i.1).symm i.2⟩

@[simp] theorem boundaryBit_digit (i : BitRef (boundaryWidth N (s.symm v))) : (boundaryBit N s e v i).2.val=i.2.val := rfl

variable {F U : Type} [Field F]

theorem represents (scalar : U→List (List Bool)→F) (T : N.Tables F) (r : ∀u,Recipe U (Boundary N u))
    (good : Represents N scalar T r) :
    Represents (Q) scalar (tables N s e T) (fun v=>rewire (r (s.symm v)) (boundary N s e v)) := by
  intro v wire p
  let oldWire (i : Incident N (s.symm v)) := fun j : Fin (N.width i.val)=>
    wire (incident N s e v i) (Fin.cast (width N s e i.val).symm j)
  let oldPin (i : Attached N (s.symm v)) := p (pin N s e v i)
  rw [rewire_value]
  change (r (s.symm v)).value scalar _=T (s.symm v) oldWire oldPin
  rw [←good (s.symm v) oldWire oldPin]
  apply congrArg ((r (s.symm v)).value scalar)
  funext ref
  cases ref with
  | inl i => exact List.ofFn_congr (width N s e i.val) (wire (incident N s e v i))
  | inr i => rfl

theorem bit_read (a : N.Assignment) (p : Ports bits) (i : BitRef (boundaryWidth N (s.symm v))) :
    bitInput (Q) (assignment N s e a) p v (boundaryBit N s e v i)=bitInput N a p (s.symm v) i := by
  rcases i with ⟨i|i,j⟩
  · have back {l t : N.Edge} (h : l=t) (b : Fin (N.width t)) :
        a l (Fin.cast (congrArg N.width h).symm b)=a t b := by subst l; rfl
    exact back (e.symm_apply_apply i.val) j
  · rfl

theorem readsBits (scalar : U→List (List Bool)→F) (T : N.Tables F) (r : SiteBits (U:=U) N)
    (good : ReadsBits N scalar r T) :
    ReadsBits (Q) scalar (fun v=>(r (s.symm v)).reroute (boundaryBit N s e v)) (tables N s e T) := by
  intro a p v
  obtain ⟨a,rfl⟩ := (assignment N s e).surjective a
  rw [BitRecipe.reroute_eval]
  exact (congrArg ((r (s.symm v)).value scalar) (funext (bit_read N s e v a p))).trans
    ((good a p (s.symm v)).trans (read N s e T a p v).symm)

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
