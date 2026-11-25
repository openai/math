import OAI.Hierarchy.DescentTerminalBundledFieldSize
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Ordinary terminal calendar and the primitive alphabet on the normalized branch -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentSixParty DescentCompiler DescentPrimitivePalette DescentResetGates
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec) (q p drift : ℕ)
local notation "T" => S.epochPower
local notation "K" => NativeBranch.privateSlotCapacity G S drift
local notation "count" => T^S.localTokenExponent
local notation "base" => colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "rootArity" => max 8 (2^S.capGain)
local notation "alphabet" => DescentBundleTagKeys.capacity base rootArity K p drift

theorem normalized_spans {h B e r : ℕ} (hb : 0<B) (chosen : S.height=Nat.log 2 h/(2*B)) (age : 0<S.height)
    (branch : G.b≤2^S.capGain) (word : p≤h) (qword : q≤h) (driftFit : drift+2≤(2*T)^r)
    (degree : r+operandExponent G S+S.localTokenExponent≤e) (price : S.capGain+3≤e)
    (late : Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)+
      8*(2*B*(S.height+1)+S.height*(S.capGain*(S.rounds+1))+1)≤(2*T)^e) :
    span q alphabet K count K p+1≤(2*T)^(6*(e+1)+19) ∧
    DescentBundleTagKeys.width (Nat.clog 2 (base+1)) rootArity K p drift*count+1≤(2*T)^(6*(e+1)+19) := by
  let d:=(2*T)^e
  have tp : 0<T := by unfold AtomSchedule.epochPower;positivity
  have stepUp (a b : ℕ) (ab : a≤b) : (2*T)^a≤(2*T)^b:=Nat.pow_le_pow_right (by omega) ab
  have pos : 0<d:=by dsimp [d];positivity
  have privateFit : K≤d := by
    unfold NativeBranch.privateSlotCapacity
    calc
      _ ≤ (2*T)^r*(2*T)^(operandExponent G S+S.localTokenExponent) :=
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (show T≤2*T by omega) _)
      _ ≤ d := by rw [←pow_add];apply stepUp;omega
  have nodeFit : count≤d := (Nat.pow_le_pow_left (show T≤2*T by omega) _).trans (stepUp _ _ (by omega))
  have arityFit : rootArity≤d := by
    apply max_le
    · exact (Nat.pow_le_pow_left (show 2≤2*T by omega) 3).trans (stepUp _ _ (by omega))
    · exact (Nat.pow_le_pow_left (show 2≤2*T by omega) _).trans (stepUp _ _ (by omega))
  have raw:=paletteBits G S (p:=p) branch op hb chosen age word
  have baseFit : Nat.clog 2 base≤d := (Nat.clog_mono_right 2 (Nat.le_succ _)).trans (raw.trans late)
  have digit (x : ℕ) (hx : x≤h) : Nat.clog 2 (x+1)≤d := by
    have cap : x≤2^(2*B*(S.height+1)) := by rw [chosen];exact DescentPrimitiveRolePrice.payload h B x hx hb
    have room : x+1≤2^(2*B*(S.height+1)+1) := by rw [pow_succ];have:=Nat.two_pow_pos (2*B*(S.height+1));omega
    have hlog:=(Nat.clog_le_iff_le_pow (by decide)).mpr room
    omega
  have up : d≤(2*T)^(e+1):=stepUp _ _ (by omega)
  have pointer : Nat.clog 2 (q+K+1)≤(2*T)^(e+1) := by
    have bits : Nat.clog 2 (q+K+1)≤Nat.clog 2 (q+1)+Nat.clog 2 (K+1) := by
      apply (Nat.clog_le_iff_le_pow (by decide)).mpr
      rw [pow_add]
      exact (show q+K+1≤(q+1)*(K+1) by nlinarith).trans
        (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
    have small : Nat.clog 2 (K+1)≤K := (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
    have big : 2*d≤(2*T)^(e+1) := by rw [pow_succ];exact (by simpa [d,Nat.mul_comm] using Nat.mul_le_mul_right d (show 2≤2*T by omega))
    have:=digit q qword;omega
  have driftBits : Nat.clog 2 (drift+2)≤d :=
    ((Nat.clog_le_iff_le_pow (by decide)).mpr (show drift+2≤2^(drift+2) from Nat.lt_two_pow_self.le)).trans
      (driftFit.trans (stepUp _ _ (by omega)))
  constructor
  · exact bundled_span (s:=e+1) (coeff:=base) (seed:=0) tp (by simp) (privateFit.trans up) (nodeFit.trans up)
      (privateFit.trans up) ((digit q qword).trans up) ((digit p word).trans up) pointer
      (baseFit.trans up) (by simp) (arityFit.trans up) (privateFit.trans up) (driftBits.trans up)

  · have clogSucc (x:ℕ) : Nat.clog 2 (x+1)≤x :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
    have head:Nat.clog 2 (base+1)≤d:=raw.trans late
    have one:1≤d:=pos
    have linear:d≤d*d:=by simpa using Nat.mul_le_mul_left d one
    have rr:DescentBundleTagKeys.width (Nat.clog 2 (base+1)) rootArity K p drift≤d+d+d*d+d*(d+2*d):=by
      unfold DescentBundleTagKeys.width
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add head ((clogSucc _).trans arityFit))
        (Nat.mul_le_mul arityFit ((clogSucc _).trans privateFit))) (Nat.mul_le_mul privateFit
          (Nat.add_le_add (digit p word) (Nat.mul_le_mul_left 2 driftBits)))
    have small:DescentBundleTagKeys.width (Nat.clog 2 (base+1)) rootArity K p drift≤6*d^2:=by
      nlinarith [rr,linear]
    have p3:0<d^3:=pow_pos pos _
    calc
      _≤(6*d^2)*d+1:=Nat.add_le_add_right (Nat.mul_le_mul small nodeFit) 1
      _≤8*d^3:=by
        have term : (6*d^2)*d=6*d^3 := by ring
        rw [term]
        omega
      _≤(2*T)^3*d^3:=Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (show 2≤2*T by omega) 3)
      _=(2*T)^(3+e*3):=by rw [pow_add,pow_mul]
      _≤_:=stepUp _ _ (by omega)

theorem normalized_span {h B e r : ℕ} (hb : 0<B) (chosen : S.height=Nat.log 2 h/(2*B)) (age : 0<S.height)
    (branch : G.b≤2^S.capGain) (word : p≤h) (qword : q≤h) (driftFit : drift+2≤(2*T)^r)
    (degree : r+operandExponent G S+S.localTokenExponent≤e) (price : S.capGain+3≤e)
    (late : Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)+
      8*(2*B*(S.height+1)+S.height*(S.capGain*(S.rounds+1))+1)≤(2*T)^e) :
    span q alphabet K count K p+1≤(2*T)^(6*(e+1)+19) :=
  (normalized_spans G S op q p drift hb chosen age branch word qword driftFit degree price late).1

end
end Hierarchy.DescentTerminalVertexFields

end OAI
