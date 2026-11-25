import OAI.Hierarchy.DescentFiniteWordRead
import OAI.Hierarchy.DescentQuotientHistory
import OAI.Hierarchy.DescentNetworkSubstitution
import OAI.Hierarchy.DescentLocalAdapters
import Mathlib.Data.List.GetD

namespace OAI
/-! # Local scalar requests reading actual boundary words in the installed reset -/

namespace Hierarchy.DescentResetGates
open Computability.BorderVNP.Crossing DescentKernelHistory
open scoped Classical BigOperators
noncomputable section

/-- Equality checks and reads of a shared scalar ROM are the only two field-producing operations. -/
inductive Request (Key : Type) where
  | check (agrees : Bool)
  | lookup (address : Key)

def Request.value {Key : Type} {K : Type*} [Zero K] [One K] (rom : Key→K) : Request Key→K
  | .check b => if b then 1 else 0
  | .lookup k => rom k

variable {D : ℕ} {P Key K : Type} {bits : P→ℕ} [CommSemiring K]

/-- Each vertex carries a finite collection of read-only scalar requests. Coordinates are
computed using only Boolean pins and the assignment to the actual cables. -/
structure Calls (N : Network D P bits) (Key : Type) where
  Gate : N.Site→Type
  [finite : ∀v,Fintype (Gate v)]
  request : ∀v,Gate v→N.Assignment→Ports bits→Request Key
attribute [instance] Calls.finite

def Correct (N : Network D P bits) (rom : Key→K) (S : Calls N Key) (T : N.Tables K) :=
  ∀a x v, N.read T a x v=∏i,(S.request v i a x).value rom

namespace Calls
variable {N : Network D P bits} (S : Calls N Key)

abbrev Tag := Σ v:N.Site,S.Gate v

def number [Fintype P] (v : N.Site) : Boundary N v ≃ Fin (Fintype.card (Boundary N v)) := Fintype.equivFin _

def recipe [Fintype P] (v : N.Site) : Recipe S.Tag (Boundary N v) where
  Hidden := Empty
  width := Empty.elim
  Node := S.Gate v
  tag i := ⟨v,i⟩
  arity _ := Fintype.card (Boundary N v)
  operand _ j := .inl ((number (N:=N) v).symm j)

def localWire (v : N.Site) (read : ∀ e:Incident N v,Word (N.width e.val)) : N.Assignment :=
  fun e=>if h : N.src e=v ∨ N.dst e=v then read ⟨e,h⟩ else fun _=>false

theorem localWire_incident (v : N.Site) (read : ∀e:Incident N v,Word (N.width e.val)) (e : Incident N v) :
    localWire v read e.val=read e := by simp [localWire,e.property]

def localPin (v : N.Site) (pins : ∀ p:Attached N v,Word (bits p.val)) : Ports bits :=
  fun p=>if h : N.attach p=v then pins ⟨p,h⟩ else fun _=>false

/-- Evaluate a concrete gate from the actual per-bit projections of the local wires and pins. -/
def bitRequest (v : N.Site) (i : S.Gate v) (read : ∀e:Incident N v,Word (N.width e.val))
    (pins : ∀p:Attached N v,Word (bits p.val)) : Request Key := S.request v i (localWire v read) (localPin v pins)

theorem bit_correct (rom : Key→K) (T : N.Tables K) (h : Correct N rom S T) (v : N.Site)
    (read : ∀e:Incident N v,Word (N.width e.val)) (pins : ∀p:Attached N v,Word (bits p.val)) :
    T v read pins = ∏i,(S.bitRequest v i read pins).value rom := by
  calc
    T v read pins = N.read T (localWire v read) (localPin v pins) v := by
      unfold Network.read
      congr 1 <;> funext e <;> simp [localWire,localPin,e.property]
    _ = _ := h _ _ v

def requestAt [Fintype P] (t : S.Tag) (args : List (List Bool)) : Request Key :=
  let bit (r : Boundary N t.1) (i : ℕ) := (args.getD ((number (N:=N) t.1 r).val) []).getD i false
  S.request t.1 t.2 (localWire t.1 (fun e j=>bit (.inl e) j.val))
    (localPin t.1 (fun p j=>bit (.inr p) j.val))

def scalar [Fintype P] (rom : Key→K) (t : S.Tag) (args : List (List Bool)) := (S.requestAt t args).value rom

private theorem at_number [Fintype P] (v : N.Site) (words : Boundary N v→List Bool) (r : Boundary N v) :
    (List.ofFn (fun j=>words ((number (N:=N) v).symm j))).getD ((number (N:=N) v r).val) []=words r := by
  rw [finiteWord_read,Equiv.symm_apply_apply]

/-- These recipes consume the incident operands of the real table. Their interpretation accesses
field data only via `rom`, and a failing equality contributes the additive zero. -/
theorem represents [Fintype P] (rom : Key→K) (T : N.Tables K) (h : Correct N rom S T) :
    Represents N (S.scalar rom) T S.recipe := by
  intro v read pins
  let words := input N read pins
  let args := List.ofFn (fun j=>words ((number (N:=N) v).symm j))
  have arg (r : Boundary N v) : args.getD ((number (N:=N) v r).val) []=words r := at_number v words r
  have eval (i : S.Gate v) : S.requestAt ⟨v,i⟩ args=S.request v i (localWire v read) (localPin v pins) := by
    unfold requestAt
    apply congrArg₂ (S.request v i)
    · apply congrArg (localWire v)
      funext e j
      exact (congrArg (fun row : List Bool => row.getD j.val false) (arg (.inl e))).trans
        (finiteWord_read (read e) j false)
    · apply congrArg (localPin v)
      funext p j
      exact (congrArg (fun row : List Bool => row.getD j.val false) (arg (.inr p))).trans
        (finiteWord_read (pins p) j false)
  have product : (S.recipe v).value (S.scalar rom) words = ∏i,(S.request v i (localWire v read) (localPin v pins)).value rom := by
    change (∑ _h : (i : Empty)→Word (Empty.elim i), ∏ i : S.Gate v,(S.requestAt ⟨v,i⟩ args).value rom) = _
    simp [eval]
  refine product.trans ((h _ _ v).symm.trans ?_)
  unfold Network.read
  congr 1 <;> funext e <;> simp [localWire,localPin,e.property]

variable {Q : Type}

def adapt (S : Calls N Key) (newBits : Q→ℕ) (place : Q→P) (encode : Ports newBits→Ports bits) :
    Calls (DescentLocalAdapters.graph N place newBits) Key where
  Gate := S.Gate
  finite v := S.finite v
  request v i a x := S.request v i a (encode x)

variable (newBits : Q→ℕ) (place : Q→P) (encode : Ports newBits→Ports bits)

theorem adapt_correct (rom : Key→K) (T : N.Tables K) (h : Correct N rom S T)
    (loc : DescentLocalAdapters.Local N place newBits encode) :
    Correct _ rom (S.adapt newBits place encode) (DescentLocalAdapters.tables N place newBits T encode) := by
  intro a x v
  exact (DescentLocalAdapters.read N place newBits T encode loc a x v).trans (h a (encode x) v)

end Calls

open private DescentNetworkSubstitution.read_local from OAI.Hierarchy.DescentNetworkSubstitution
variable {d : ℕ} (N : Network D P bits) (M : ∀v,Network d (DescentNetworkSubstitution.Slot N v) (DescentNetworkSubstitution.slotWidth N v))
variable (G : ∀v,Calls (M v) Key)

def substitute : Calls (DescentNetworkSubstitution.network N M) Key where
  Gate t := (G t.1).Gate t.2
  request t i a x := let z:=DescentNetworkSubstitution.assignmentEquiv N M a
    (G t.1).request t.2 i (z.2 t.1) (DescentNetworkSubstitution.visible N z.1 x t.1)

theorem substitute_correct (rom : Key→K) (T : ∀v,(M v).Tables K) (h : ∀v,Correct (M v) rom (G v) (T v)) :
    Correct _ rom (substitute N M G) (DescentNetworkSubstitution.tables N M T) := by
  rintro a x ⟨v,j⟩
  exact (DescentNetworkSubstitution.read_local N M T a x v j).trans (h v _ _ j)


end
end Hierarchy.DescentResetGates

end OAI
