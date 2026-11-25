import OAI.Hierarchy.DescentUniformRetainedControls
import OAI.Hierarchy.DescentDatedOperandSetupRate

namespace OAI
/-! # Uniform workspace for the native reset operand setup -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset D drift : ℕ) {ι : ℕ→Type*}
    (index : ℕ→ℕ) (tailCost chosenJ sites age size degree root previous nextM base : ∀h,ι h→ℕ)
    (old : ∀h,ι h→Prior)
local notation "sample" h:arg i:arg => originalSample G op t f g reset (tailCost h i) D drift (chosenJ h i)
  (sites h i) (age h i) (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i)
  (base h i) (old h i)
local notation "z" => fun h i=>sample h i
local notation "out_" => fun h i=>(sample h i).output G board D f g op.C op.w

local notation "S_" h:arg i:arg => (sample h i).sched
local notation "k_" h:arg i:arg => (sample h i).k
local notation "tail_" h:arg i:arg => (sample h i).tail
local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h i) (tail_ h i) (age h i)
local notation "A_" h:arg i:arg => (out_ h i).setup.retained
local notation "T_" h:arg i:arg => (out_ h i).roleTransfer.transfer

/-- The complete native operand setup and separate prior primitive move fit over the same
family, allowing the height divisor and frozen epoch to vary with each index. -/
theorem uniform_operand_setup (cal : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(S_ h i).hostSize (age h i))
    (newH : Bounded fun h i=>(S_ h i).hostSize (age h i+1))
    (oldG : Bounded fun h i=>2^(c_ h i))
    (newG : Bounded fun h i=>(S_ h i).groupCount (age h i+1))
    (M : Bounded fun h i=>2^(root h i))
    (matrices : Bounded fun h i=>2^((c_ h i+k_ h i)*(c_ h i+k_ h i)))
    (before : ∀h i,age h i<(S_ h i).length)
    (caps : ∀ᶠ h:ℕ in atTop,∀i,(old h i).nodes≤(S_ h i).retainedNodes ∧
      (old h i).arguments≤(S_ h i).retainedArgumentsAt G drift)
    (priorLanes : Bounded (fun h i=>(old h i).operandLanes))
    (roleLanes : Bounded (fun h i=>(old h i).primitiveLanes))
    (archive : ∀ᶠ h:ℕ in atTop,∀i,(A_ h i).wholeWord*(old h i).operandLanes≤h/2 ∧
      (T_ h i).wholeWord*(old h i).primitiveLanes≤h/2)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out_ h i).groupWidth≤h) (priced : Installed (out_)) :
    DescentResetOperandSetup.Chart.ScalarRoom (fun h i=>(out_ h i).setup) ∧
    DescentRetainedHomeMover.Layout.ScalarRoom (fun h i=>(out_ h i).roleTransfer) :=by
  let p:=out_
  let C:=fun h (i:ι h)=>(p h i).setup
  let P:=fun h (i:ι h)=>(C h i).packets
  obtain ⟨prior,token⟩:=uniform_retained G board op t f g reset D drift index tailCost chosenJ sites age size degree root previous nextM base old cal level
    oldH oldG matrices before caps priorLanes roleLanes archive selected
  obtain ⟨ready,role,packed,rolePacked,signed⟩:=uniform_retained_controls G board op t f g reset D drift index tailCost chosenJ sites age size degree root previous nextM base old cal level
    oldH newH newG M before priced selected prior token
  have loc:=from_calendar_inputs G board D f g op.C op.w index z cal
  let range (b : ∀h,ι h→ℕ) (member : ∀h i,b h i∈(p h i).rootUnits ∨ b h i∈(p h i).receiverUnits) :
      ∀ᶠ h:ℕ in atTop,∀i,b h i*(p h i).receiver.lanes≤h/2 :=
    priced.mono (fun _ ok i=>ok i _ (member _ i))
  let weak (b : ∀h,ι h→ℕ) (member : ∀h i,b h i∈(p h i).rootUnits ∨ b h i∈(p h i).receiverUnits) :
      ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,b h i*(p h i).receiver.lanes≤K*h :=
    ⟨1,(range b member).mono fun h x i=>by rw [Nat.one_mul];exact (x i).trans (Nat.div_le_self ..)⟩
  have front (f : Bool) :=range (fun h i=>(P h i).oldBits*((P h i).stage 0 f).fields) (fun h i=>by
    left;cases f <;> simp [P,C,rootUnits])
  have fcap (h : ℕ) (i : ι h) : 0<(P h i).oldBits :=by
    exact (Nat.succ_pos (k_ h i)).trans_le ((Nat.le_max_left ..).trans (Nat.le_max_right ..))
  have pages (f : Bool) : Bounded (fun h i=>((P h i).stage 0 f).fields) :=by
    refine ⟨1,(front f).mono fun h q i=>?_⟩
    have a:=Nat.le_mul_of_pos_left ((P h i).stage 0 f).fields (fcap h i)
    have b:=Nat.le_mul_of_pos_right ((P h i).oldBits*((P h i).stage 0 f).fields) (Nat.two_pow_pos (root h i))
    exact (a.trans (b.trans (q i))).trans ((Nat.div_le_self ..).trans (by rw [Nat.one_mul];exact Nat.lt_two_pow_self.le))
  have pulls : DescentOperandRootPull.Pair.ScalarRoom P :=
    ⟨packed.oldHosts,packed.newHosts,packed.groups,packed.blocks,packed.lanes,packed.lanes,pages,
      fun f=>weak (fun h i=>(P h i).oldBits*((P h i).stage 0 f).fields)
        (fun h i=>by left;cases f <;> simp [P,C,rootUnits]),
      fun f=>weak (fun h i=>((P h i).oldBits*((P h i).stage 0 f).fields)*(p h i).sheets.blocks)
        (fun h i=>by right;cases f <;> simp [P,C,receiverUnits]),fun _ _=>Nat.two_pow_pos _⟩
  refine ⟨⟨weak (fun h i=>(C h i).publicCasts.bound) (fun h i=>Or.inr (by simp [C,receiverUnits])),pulls,prior,ready,packed,signed,?_,
    prior.args.mul prior.nodes,loc.packetSize.bounded level,1,?_⟩,⟨token,role,rolePacked⟩⟩
  · exact (Bounded.const 6).add ((Bounded.const 2).mul signed.fields)
  · filter_upwards [priced] with h q
    intro i
    let small (x : ℕ) (mem : x∈(p h i).receiverUnits) :
        x*(p h i).receiver.lanes≤1*h :=by rw [Nat.one_mul];exact (q i _ (Or.inr mem)).trans (Nat.div_le_self ..)
    exact ⟨small ((C h i).sourceWidth) (by simp [C,receiverUnits]),small ((C h i).fieldBits*(C h i).inputs+(C h i).fieldBits) (by simp [C,receiverUnits]),small ((C h i).fieldBits+2) (by simp [C,receiverUnits]),
      small ((C h i).rotorBits*4+(C h i).rotorBits) (by simp [C,receiverUnits]),small ((C h i).fallbackBits*(C h i).fallbackInputs+(C h i).fallbackBits) (by simp [C,receiverUnits])⟩


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
