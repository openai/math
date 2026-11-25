import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedSweep
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankPrice
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolume

/-! # Recursive charges and uniform time/space for the two selected sweep leaves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
set_option maxRecDepth 2600
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress InterchangeROM
  Interchange.Template InterchangeSpectralFibre

def sweepPrice (x : Data) (inv : Bool) :=
  SweepBank.price x.a x.m x.labels (checks x) x.b x.modulusIndex (half x) inv

def sweepFactor (x : Data) :=
  max (max (sweepPrice x false).1 (sweepPrice x false).2)
    (max (sweepPrice x true).1 (sweepPrice x true).2)

theorem computable_sweepFactor : Computable sweepFactor := by
  have h (inv : Bool) : Computable (fun x : Data => sweepPrice x inv) :=
    SweepBank.computable_price (Data.primrec_header 3).to_comp (Data.primrec_header 2).to_comp
      (Data.primrec_header 4).to_comp ((Raw.primrec_checkCount.comp (Data.primrec_header 2)).to_comp)
      (Data.primrec_header 1).to_comp Data.primrec_modulusIndex.to_comp
      ((Raw.primrec_halfCode.comp Data.primrec_modulusIndex).to_comp) (Computable.const inv)
  have bound (k : Bool) := Primrec.nat_max.to_comp.comp (Computable.fst.comp (h k)) (Computable.snd.comp (h k))
  exact Primrec.nat_max.to_comp.comp (bound false) (bound true)

private theorem sweepPrice_le (x : Data) (inv : Bool) :
    (sweepPrice x inv).1 ≤ sweepFactor x ∧ (sweepPrice x inv).2 ≤ sweepFactor x := by
  unfold sweepFactor
  cases inv <;> omega

variable (x : Data) [Fact (x.modulusIndex+1).Prime] {P G S : Tape} {f w : ℕ} {D : Type}

local notation "X" => Positions P G S x.a x.m x.b f
local notation "R" => ZMod (x.modulusIndex+1)
local notation "H" => send (header f P G S)
local notation "L" => SweepBank.layout P G S x.a x.m x.b f

theorem one_sweep_priced (pay : Series D) (hm : 0 < x.m) (hb : 2 ≤ x.b)
    (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ x.b) (hw : pay.count ≤ w)
    (parent : Cmd) (env : Env) (child : Request x.b → Allowance) (hc : ∀ q, ChildOK x P G S f w pay q →
      Sweep.Run (parent::env) parent ((Request.job x.b).issue q) ((Request.job x.b).reply q) (child q))
    (inv : Bool) (a b : Bank R (Fin x.labels) (X × D) (Fin (checks x))) :
    let qs := SweepBank.emitted w pay (half x) inv a b
    let M := InterchangeROMStageVolume.mass H (L).count w
    qs.length = sweepCalls x ∧ (∀ q ∈ qs, ChildOK x P G S f w pay q) ∧
    Sweep.Run (parent::env) (sweepLeaf x inv) (packet H (SweepBank.packed L pay a ++ SweepBank.packed L pay b))
      (packet H (SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) a) ++
        SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) b)))
      (childCharges (Sweep.uniformCost (sweepFactor x*M)) child qs) := by
  intro qs M
  refine ⟨?_,SweepBank.emitted_typed w pay (half x) inv a b,?_⟩
  · simpa only [sweepCalls,Nat.mul_assoc] using SweepBank.emitted_length w pay (half x) inv a b
  let C := (L).count*(w+1)+1
  have cm : C ≤ M := by dsimp [C,M,InterchangeROMStageVolume.mass]; omega
  have kt : (sweepPrice x inv).1*C ≤ sweepFactor x*M := Nat.mul_le_mul (sweepPrice_le x inv).1 cm
  have ks : (sweepPrice x inv).2*C ≤ sweepFactor x*M := Nat.mul_le_mul (sweepPrice_le x inv).2 cm
  intro deck base hr
  have r := SweepBank.command_priced hm hb ok pay hw parent env child hc (half x) inv a b deck base hr
  exact r.mono (Nat.add_le_add_right kt _) (Nat.add_le_add_left (Nat.add_le_add_right ks _) _)
    (Nat.add_le_add_right ks _)

/-- The supplied typed transition determines two packed check banks and a single ordered list
of recursive calls. The local factor is computable on the selected template alone. -/
theorem sweep_transition (pay : Series D) (hm : 0 < x.m) (hb : 2 ≤ x.b)
    (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ x.b) (hw : pay.count ≤ w)
    (parent : Cmd) (env : Env) (child : Request x.b → Allowance) (hc : ∀ q, ChildOK x P G S f w pay q →
      Sweep.Run (parent::env) parent ((Request.job x.b).issue q) ((Request.job x.b).reply q) (child q))
    {tag adv a u v} (tr : sweepTransition (P:=P) (G:=G) (S:=S) (f:=f) x pay tag adv a u v) (ha : a=.forward ∨ a=.backward) :
    let M := InterchangeROMStageVolume.mass H (L).count w
    ∃ qs : List (Request x.b), qs.length = sweepCalls x ∧ (∀ q ∈ qs, ChildOK x P G S f w pay q) ∧
      Sweep.Run (parent::env) (commands x a) (packet H u) (packet H v)
        (childCharges (Sweep.uniformCost (sweepFactor x*M)) child qs) := by
  dsimp only
  rcases ha with rfl | rfl
  · cases tr with
    | forward a b => exact ⟨_,one_sweep_priced x pay hm hb ok hw parent env child hc false a b⟩
  · cases tr with
    | backward a b => exact ⟨_,one_sweep_priced x pay hm hb ok hw parent env child hc true a b⟩

private theorem const_sum {A : Type*} (xs : List A) (n : ℕ) :
    (xs.map (fun _ => n)).sum = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs _ => simp [Nat.succ_mul,Nat.add_comm]

private theorem const_peak {A : Type*} (xs : List A) (n : ℕ) :
    (xs.map (fun _ => n)).foldr max 0 ≤ n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa using ih

/-- A direct certificate for either of the forward/backward fields of `Selected.Cases`. -/
theorem sweep_case (pay : Series D) (hm : 0 < x.m) (hb : 2 ≤ x.b)
    (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ x.b) (hw : pay.count ≤ w)
    (parent : Cmd) (env : Env) (child : Allowance) (hc : ∀ q, ChildOK x P G S f w pay q →
      Sweep.Run (parent::env) parent ((Request.job x.b).issue q) ((Request.job x.b).reply q) child)
    (inv : Bool) (a b : Bank R (Fin x.labels) (X × D) (Fin (checks x))) :
    let M := InterchangeROMStageVolume.mass H (L).count w
    let Z := sweepFactor x*M
    Sweep.Run (parent::env) (sweepLeaf x inv) (packet H (SweepBank.packed L pay a ++ SweepBank.packed L pay b))
      (packet H (SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) a) ++
        SweepBank.packed L pay (sweep (lift (directions inv (half x : R))) b)))
      ⟨Z+sweepCalls x*child.time,Z+child.cap,Z+child.depth⟩ := by
  intro M Z deck base hd
  let qs := SweepBank.emitted w pay (half x) inv a b
  have main := one_sweep_priced x pay hm hb ok hw parent env (fun _ => child) hc inv a b
  have len : qs.length = sweepCalls x := main.1
  apply (main.2.2 deck base hd).mono
  · change Z+(qs.map (fun _ => child.time)).sum ≤ Z+sweepCalls x*child.time
    rw [const_sum,len]
  · exact Nat.add_le_add_left (Nat.add_le_add_left (const_peak qs child.cap) Z) base
  · exact Nat.add_le_add_left (const_peak qs child.depth) Z

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
