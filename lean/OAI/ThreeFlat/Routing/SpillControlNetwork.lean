import OAI.ThreeFlat.Routing.SpillGreedy
import OAI.ThreeFlat.Routing.SpillPrimaryMask
import OAI.ThreeFlat.Routing.SpillReserveSelect

namespace OAI
/-! # The control-network shape of a two-pass sparse packing bank -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.Spill
open Concentrator

universe u
variable {E R V : Type u} {F : Type*} [Fintype E] [LinearOrder E] [Fintype R] [LinearOrder R]
  [Fintype V] [DecidableEq V]

abbrev ControlPin (N : E → Finset R) (slots : ℕ) := (E ⊕ Candidate N) ⊕ ReserveChoice E slots
abbrev TraceBits (E V : Type*) (cap : ℕ) := E ⊕ Round E V cap
abbrev AuditBits (N : E → Finset R) (e : E) := Fin 3 ⊕ N e

def finalRead (cap : ℕ) (e : E) : TraceBits E V cap :=
  if h : cap = 0 then .inl e else .inr (.inr (e,⟨cap-1,by omega⟩))

def auditTest (N : E → Finset R) (e : E) (w : AuditBits N e → Bool) : Prop :=
  w (.inl 1) = decide (w (.inl 0) = true ∧ ∀ r, w (.inr r) = false) ∧ w (.inl 2) = false

abbrev ControlGate (E : Type*) := Fin 3 ⊕ E
def controlPort (N : E → Finset R) (V : Type u) (slots cap : ℕ) : ControlGate E → Type u
  | .inl g => if g = 0 then E ⊕ Candidate N else if g = 1 then TraceBits E V cap
    else ReserveSelectPin E V slots cap
  | .inr e => AuditBits N e

instance controlPortFintype (N : E → Finset R) (slots cap : ℕ) :
    ∀ g : ControlGate E, Fintype (controlPort N V slots cap g)
  | .inl 0 => inferInstanceAs (Fintype (E ⊕ Candidate N))
  | .inl 1 => inferInstanceAs (Fintype (TraceBits E V cap))
  | .inl 2 => inferInstanceAs (Fintype (ReserveSelectPin E V slots cap))
  | .inr e => inferInstanceAs (Fintype (AuditBits N e))

def controlModules [Zero F] [One F] (N : E → Finset R) (G : ReserveGraph E V)
    (slots cap : ℕ) : ∀ g : ControlGate E, BitNetwork F (Fintype.card (controlPort N V slots cap g))
  | .inl 0 => greedyCheck N
  | .inl 1 => reserveCheck G slots cap
  | .inl 2 => reserveSelectNetwork G slots cap
  | .inr e => TypedWiring.localTable fun w => if auditTest N e w then 1 else 0

def controlWire (N : E → Finset R) (slots cap : ℕ) : ∀ g : ControlGate E,
    controlPort N V slots cap g → ControlPin N slots ⊕ TraceBits E V cap
  | .inl 0,k => .inl (.inl k)
  | .inl 1,k => .inr k
  | .inl 2,k => Sum.elim Sum.inr (fun c => .inl (.inr c)) k
  | .inr e,.inl k => ![.inl (.inl (.inl e)),.inr (.inl e),.inr (finalRead cap e)] k
  | .inr e,.inr r => .inl (.inl (.inr ⟨e,r⟩))

/-- The complete two-pass control is a fixed network. Its internal wires
carry the mask passed to the reserve and its unary peeling history. -/
def controlNetwork [Zero F] [One F] (N : E → Finset R) (G : ReserveGraph E V) (slots cap : ℕ) :
    BitNetwork F (Fintype.card (ControlPin N slots)) :=
  TypedWiring.glue (controlModules N G slots cap) (controlWire N slots cap)

def controlPins (N : E → Finset R) {slots : ℕ} (A : Finset E)
    (P : Candidate N → Bool) (s : ReserveChoice E slots → Bool) : ControlPin N slots → Bool :=
  Sum.elim (Sum.elim (fun e => decide (e ∈ A)) P) s

end ThreeFlat.Routing.Spill

end
end OAI
