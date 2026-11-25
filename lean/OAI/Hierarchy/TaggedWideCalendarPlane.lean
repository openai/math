import OAI.Hierarchy.TaggedWideLeafContraction
import OAI.Hierarchy.TaggedWideControlBoard

namespace OAI
/-! # The decoded output plane on the fixed shared physical pin ordering -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ThreeFlat Routing
open TaggedShorterBudget ProtocolStackContraction WideControlJoin
open scoped Classical BigOperators
set_option quotPrecheck false

variable {F : Type*} [Field F] {T Ex Se E H : Type} [Fintype T] [Fintype E] [Fintype Ex]
    [Fintype Se] [Fintype H] {ports lanes groups view w : ℕ} (key : T ↪ ℕ×ℕ) (cap : E→ℕ) (gate : Gate)
local notation "W" => fun t:T=>⌈dyadic (key t).2*w⌉₊
local notation "A" => OutputData T (Fin groups) ports lanes W
local notation "P" => (Fin groups×Fin ports)×Fin view
local notation "D" => A ⊕ ((Bool × ((e:E) × Fin (cap e))) ⊕ (H ⊕ P))
local notation "V" => SitePins Ex Se D gate

def planePin : (A⊕P)→V :=
  Sum.elim (fun a=>.inr (.inr (.inl (.inl a)))) (fun p=>.inr (.inr (.inl (.inr (.inr (.inr p))))))

def planeNet : BitNetwork F (Fintype.card V) :=
  WideHost.onPins (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes) (view:=view) (w:=w) key)
    (planePin (Ex:=Ex) (Se:=Se) (H:=H) key cap gate)

theorem planeNet_cost :
    let net:=planeNet (F:=F) (Ex:=Ex) (Se:=Se) (H:=H) (groups:=groups) (ports:=ports) (lanes:=lanes)
      (view:=view) (w:=w) key cap gate
    net.cells+net.internal≤Fintype.card P*(48*(2*Fintype.card T)+98) := by
  dsimp only
  exact output_cost (F:=F) W Prod.fst (fun p:P=>p.2.val) (Sum.inr : P→A⊕P) Sum.inl

variable {m n : ℕ} {records : T→Fin n→ProtocolRAMEmit.Row}
    (b : ∀t,Installed F groups ports lanes w m (key t).2 (records t))

theorem planeNet_value (ext : Ex→Bool) (selector : Se→Bool) (seen : gate.Seen→Bool)
    (z : ∀t,(banks b t).Slots) (y : PrivatePorts cap) (h : H→Bool) (p : P→Bool) :
    TypedWiring.value (planeNet (Ex:=Ex) (Se:=Se) (H:=H) (groups:=groups) (ports:=ports) (lanes:=lanes)
      (view:=view) (w:=w) key cap gate) (Sum.elim ext (Sum.elim selector (Sum.elim (write (banks b) cap z y h p) seen))) =
    TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes) (view:=view) (w:=w) key)
      (Sum.elim (voltage (banks b) z) p) := by
  rw [planeNet,WideHost.onPins_value]
  apply congrArg (TypedWiring.value _)
  funext i
  cases i <;> rfl

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
