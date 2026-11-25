import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentSeedPrintedPitch
import OAI.Hierarchy.DescentSeedNumberRates
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Address bounds for the concrete seed lane choices -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSIMDLookup
open DescentDatedAddressBook DescentPrimitivePalette Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (D : PoweredGadget F)

theorem venuePitch_le (S : AtomSchedule) (payload gain k tail p f quota : ℕ) :
    venuePitch D S payload gain k tail p f quota ≤ payload+1 :=by
  unfold venuePitch
  split
  · let m:=S.groupWidth k tail 0+k
    let b:=firstPrecision S k tail p f quota
    let ratio:=payload/(8*b)
    change 2^(min m (Nat.log 2 ratio)-k) ≤ payload+1
    have le : min m (Nat.log 2 ratio)-k ≤ Nat.log 2 ratio :=
      (Nat.sub_le ..).trans (Nat.min_le_right ..)
    apply (Nat.pow_le_pow_right (by decide : 0<2) le).trans
    by_cases z : ratio=0
    · simp [z]
    · exact (Nat.pow_log_le_self 2 z).trans ((Nat.div_le_self ..).trans (Nat.le_succ _))
  · exact (Nat.div_le_self ..).trans (Nat.le_succ _)

variable {ι : ℕ→Type*}
variable (op : RotorSpec) (S : ∀h,ι h→AtomSchedule)
  (payload k tail gain p drift degree f quota base field wire history Z : ∀h,ι h→ℕ)
local notation "L" => fun h i => selectedLayout D (S h i) (payload h i) (k h i) (tail h i) (gain h i)
  (p h i) (drift h i) (degree h i) (f h i) (quota h i) (base h i) (field h i) (wire h i) (history h i)
local notation "pitch" => fun h i => Primitive.paletteLanes D op ((L h i).seedWidth) (Z h i) (payload h i) (k h i)

theorem selected_rates (t K : ℕ)
    (rounds : ∀ᶠ h in atTop,∀i,(S h i).rounds ≤ t)
    (ages : ∀ᶠ h in atTop,∀i,(S h i).height ≤ h)
    (physical : ∀ᶠ h in atTop,∀i,payload h i ≤ K*h) :
    Bounded (fun h i=>(L h i).packedLanes) ∧ Bounded (fun h i=>(L h i).operandLanes) ∧
    Bounded (fun h i=>(L h i).groupsPerNode) ∧ Bounded pitch ∧
    (∀ᶠ h in atTop,∀i,(DescentPackedSeed.Primitive.roleBits ((L h i).seedWidth)*2^(k h i))*(pitch h i) ≤ K*h) :=by
  have word : Bounded payload := (Bounded.pow_of_linear physical).of_le (fun h i=>Nat.lt_two_pow_self.le)
  refine ⟨(word.add (Bounded.const 1)).of_le (fun h i=>venuePitch_le D (S h i) ..),
    word.of_le (fun _ _=>Nat.div_le_self ..),?_,word.of_le (fun _ _=>Nat.div_le_self ..),?_⟩
  · let a:=Nat.clog 2 D.b*(t+1)
    refine ⟨2*a,?_⟩
    filter_upwards [rounds,ages,eventually_ge_atTop 1] with h hr ha one
    intro i
    change (S h i).firstWidth D.b (p h i)/(p h i) ≤ 2^((2*a)*h)
    by_cases z : p h i=0
    · simp [z]
    rw [first_argument_count _ _ _ (Nat.pos_of_ne_zero z)]
    have exp := Nat.mul_le_mul (hr i) (ha i)
    have pos : 0<D.b := by have bound:=D.paid;omega
    apply (Nat.mul_le_mul_right D.b (Nat.pow_le_pow_right pos exp)).trans
    apply (grainRate D.b t h).trans
    change 2^(a*(h+1)) ≤ 2^((2*a)*h)
    apply Nat.pow_le_pow_right (by decide)
    calc
      a*(h+1) ≤ a*(2*h) := Nat.mul_le_mul_left _ (by omega)
      _ = (2*a)*h := by ring
  · filter_upwards [physical] with h hp i
    exact (Primitive.chosen_roles_half D op _ _ _ _).trans ((Nat.div_le_self ..).trans (hp i))

end
end Hierarchy.DescentDatedSeedStartup

end OAI
