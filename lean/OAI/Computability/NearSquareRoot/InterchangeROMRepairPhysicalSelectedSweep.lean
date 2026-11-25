import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRealize
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankLedger

/-! # Native forward and backward transitions on a selected numeric template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax InterchangeROM
  Interchange.Template InterchangeSpectralFibre
open InterchangeROMTable (numeral)

abbrev sweepCalls (x : Data) := 2*(x.labels*checks x)*x.m

abbrev ChildOK (x : Data) (P G S : Tape) (f w : ℕ) {D : Type} (pay : Series D) (q : Request x.b) :=
  (allowed (fun _ : Unit => f) (fun _ => (SweepBank.layout P G S x.a x.m x.b f).count)
    (fun _ => w) () q ∧
    ∀ k, InterchangePayloadBank.Good (fun _ : Unit => pay)
      (fun z : ZMod (x.modulusIndex+1) => numeral z.val) () (q.contents k)) ∧ inherited x.b P G S q

def childCharges {b : ℕ} (base : Allowance) (child : Request b → Allowance) (qs : List (Request b)) : Allowance :=
  ⟨base.time + (qs.map fun q => (child q).time).sum,
    base.cap + (qs.map fun q => (child q).cap).foldr max 0,
    base.depth + (qs.map fun q => (child q).depth).foldr max 0⟩

variable (x : Data) [Fact (x.modulusIndex+1).Prime] {P G S : Tape} {f w : ℕ} {D : Type}

local notation "X" => Positions P G S x.a x.m x.b f
local notation "R" => ZMod (x.modulusIndex+1)
local notation "H" => send (header f P G S)
local notation "L" => SweepBank.layout P G S x.a x.m x.b f

/-- Parameters common to the actual correction, sweep and matrix transitions. -/
abbrev sweepTransition (pay : Series D) (tag : X × D → Fin x.m → Bool)
    (adv : Bank R (Fin x.labels) (X × D) (Fin (rows x)) → Bank R (Fin x.labels) (X × D) (Fin (rows x))) :=
  Transition (Raw.decode x.modulusIndex (rows x) (checks x) x.m x.repair) (half x : R) tag
    (lift (directions false (half x : R))) (lift (directions true (half x : R))) adv
    (SweepBank.packed L pay) (SweepBank.packed L pay)

theorem one_sweep (pay : Series D) (hb : 2 ≤ x.b) (hp : solid P) (hg : solid G) (hs : solid S)
    (hw : pay.count ≤ w) (parent : Cmd) (env : Env) (child : Request x.b → Allowance)
    (hc : ∀ q, ChildOK x P G S f w pay q →
      Sweep.Run (parent::env) parent ((Request.job x.b).issue q) ((Request.job x.b).reply q) (child q))
    (inv : Bool) (a b : Bank R (Fin x.labels) (X × D) (Fin (checks x))) :
    let qs := SweepBank.emitted w pay (half x) inv a b
    let z := SweepBank.charge w (half x) inv pay (fun _ => SweepBank.noneCost) a b
    qs.length = sweepCalls x ∧ (∀ q ∈ qs, ChildOK x P G S f w pay q) ∧
    Sweep.Run (parent::env) (sweepLeaf x inv) (packet H (SweepBank.packed L pay a ++ SweepBank.packed L pay b))
      (packet H (SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) a) ++
        SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) b)))
      (childCharges z child qs) := by
  intro qs z
  refine ⟨?_,SweepBank.emitted_typed w pay (half x) inv a b,?_⟩
  · simpa only [sweepCalls,Nat.mul_assoc] using SweepBank.emitted_length w pay (half x) inv a b
  have run := SweepBank.command_bounded hb hp hg hs pay hw parent env child
    (by intro j g; apply hc; exact ⟨⟨Sweep.child_allowed ..,fun k => ⟨_,rfl⟩⟩,Sweep.child_inherited _ _ _ _ _ _ _ _ _⟩)
    (half x) inv a b
  intro r base hr
  have bounds := SweepBank.charge_split w (half x) inv pay child a b
  exact (run r base hr).mono bounds.1.le (Nat.add_le_add_left bounds.2.1 _) bounds.2.2

/-- A transition-level certificate. The local allowance depends only on the input banks
and the selected command; callback costs occur only in the emitted ledger. -/
theorem sweep_transition_ledger (pay : Series D) (hb : 2 ≤ x.b)
    (hp : solid P) (hg : solid G) (hs : solid S) (hw : pay.count ≤ w)
    (parent : Cmd) (env : Env) (child : Request x.b → Allowance)
    (hc : ∀ q, ChildOK x P G S f w pay q →
      Sweep.Run (parent::env) parent ((Request.job x.b).issue q) ((Request.job x.b).reply q) (child q))
    {tag adv a u v} (tr : sweepTransition (P:=P) (G:=G) (S:=S) (f:=f) x pay tag adv a u v) (ha : a=.forward ∨ a=.backward) :
    ∃ (qs : List (Request x.b)) (z : Allowance), qs.length = sweepCalls x ∧
      (∀ q ∈ qs, ChildOK x P G S f w pay q) ∧
      Sweep.Run (parent::env) (commands x a) (packet H u) (packet H v) (childCharges z child qs) := by
  rcases ha with rfl | rfl
  · cases tr with
    | forward a b => exact ⟨_,_,one_sweep x pay hb hp hg hs hw parent env child hc false a b⟩
  · cases tr with
    | backward a b => exact ⟨_,_,one_sweep x pay hb hp hg hs hw parent env child hc true a b⟩

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
