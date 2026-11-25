import OAI.Hierarchy.DescentOriginalReceiverWidth

namespace OAI
/-! # The actual dated receiver attains its uniform local-width bound -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentCompiler DescentSixParty DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Filter
noncomputable section

private theorem width_at_selected {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank) (floor : ℕ) :
    (selected G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes
      printedBits venue addr roster floor).successor.groupWidth =
      (ResetOutput.fromBoard G S board k tail age p f g drift degree h 0 previous 1 nextM C packet
        (ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue) 0).groupWidth := by
  have inventory := selected_inventory G S board k tail age p f g drift degree h previous nextM C packet
    oldLanes primitiveLanes printedBits venue addr roster floor
  exact congrArg₂ (fun (a b : List ℕ) => 1+(a++b).sum) inventory.1 inventory.2.1

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift : ℕ)
local notation "E₀" => ResetOutput.receiverRate G board op t f g reset D

theorem scheduled_scale (B : ℕ) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree : ℕ, let S:=stageNumbers G t j f g reset sites (tail τ j)
    let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
    ∀(original : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (operandLanes primitiveLanes base : ℕ)
      (addr : ℕ→ℕ→Bank) (roster : Bank),
      p≤h→degree≤coefficientDegree→ old.degree=D→ old.cap=((capCalendar G.b t g j).take age).prod*256→
      old.paidBits=S.censusBits p→
      let a:=scheduled G S board k (tail τ j) age p f g drift degree h original op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      a.successor.groupWidth≤ scale j (E₀) :=by
  filter_upwards [ResetOutput.original_digit_scale G board op t f g reset τ D drift B positive branch coefficientDegree] with h receipts
  dsimp only
  intro sites age p degree original old operandLanes primitiveLanes base addr roster hp hd hD hcap hpOld
  let j:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t j f g reset sites (tail τ j)
  let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
  let T:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  let previous:=NativePitch.resetCut S k (tail τ j) p f h age
  let nextM:=NativePitch.incoming S k (tail τ j) p f h original (age+1)
  let prior:=ResetOutput.Prior.atDate G S age p drift operandLanes primitiveLanes T old
  have small:=receipts sites age p degree 0 previous 1 nextM 0 prior hp hd
  have canon : ({old with
      degree := D
      cap := ((capCalendar G.b t g j).take age).prod*256
      paidBits := S.censusBits p} : StageVenueTail.Date)=old :=by
    rw [←hD,←hcap,←hpOld]
  unfold ResetOutput.originalSample ResetOutput.Sample.output at small
  change (ResetOutput.fromBoard G S board k (tail τ j) age p f g drift degree h 0 previous 1 nextM op.C op.w
    {prior with
      venue := {({old with
        degree := D
        cap := ((capCalendar G.b t g j).take age).prod*256
        paidBits := S.censusBits p} : StageVenueTail.Date) with degree := D}
      printedBits := T} 0).groupWidth≤_ at small
  rw [canon] at small
  exact (width_at_selected G S board k (tail τ j) age p f g drift degree h previous nextM op.C op.w
    operandLanes primitiveLanes T old addr roster base).le.trans small

theorem scheduled_short (B : ℕ) (positive : 0<B) (bought : 2*(E₀)≤B)
    (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree : ℕ, let S:=stageNumbers G t j f g reset sites (tail τ j)
    let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
    ∀(original : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (operandLanes primitiveLanes base : ℕ)
      (addr : ℕ→ℕ→Bank) (roster : Bank),
      p≤h→degree≤coefficientDegree→ old.degree=D→ old.cap=((capCalendar G.b t g j).take age).prod*256→
      old.paidBits=S.censusBits p→
      let a:=scheduled G S board k (tail τ j) age p f g drift degree h original op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      8*a.successor.groupWidth≤h :=by
  filter_upwards [scheduled_scale G board op t f g reset τ D drift B positive branch coefficientDegree,
    eventually_home 0 0 (E₀) B positive (by simpa using bought)] with h small room
  dsimp only
  intro sites age p degree original old operandLanes primitiveLanes base addr roster hp hd hD hc hP
  have bound:=small sites age p degree original old operandLanes primitiveLanes base addr roster hp hd hD hc hP
  have ticket:=room.2 0 1 _ (by simp [tail]) (by simp) bound
  omega

theorem scheduled_tables (B : ℕ) (positive : 0<B) (bought : 2*(E₀)≤B)
    (branch : G.b≤2^(capRate G t g)) (coefficientDegree : ℕ := D) :
    ∀ᶠ h : ℕ in atTop,let j:=Nat.log 2 h/(2*B);
    ∀sites age p degree : ℕ, let S:=stageNumbers G t j f g reset sites (tail τ j)
    let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
    ∀(original : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (operandLanes primitiveLanes base : ℕ)
      (addr : ℕ→ℕ→Bank) (roster : Bank),
      p≤h→degree≤coefficientDegree→ old.degree=D→ old.cap=((capCalendar G.b t g j).take age).prod*256→
      old.paidBits=S.censusBits p→
      let a:=scheduled G S board k (tail τ j) age p f g drift degree h original op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      ∀bits,bits∈a.successor.rootUnits ∨ bits∈a.successor.receiverUnits →
        bits*a.successor.receiver.lanes≤h/2 :=by
  filter_upwards [scheduled_short G board op t f g reset τ D drift B positive bought branch coefficientDegree] with h priced
  dsimp only
  intro sites age p degree ordinary old A M base addr roster hp hd hD hc hP bits used
  let j:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t j f g reset sites (tail τ j)
  let k:=groupBits t j S.hostGain S.capGain (cutRate t f g)
  let previous:=NativePitch.resetCut S k (tail τ j) p f h age
  let nextM:=NativePitch.incoming S k (tail τ j) p f h ordinary (age+1)
  let role:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  exact selected_room G S board k (tail τ j) age p f g drift degree h previous nextM op.C op.w A M role
    old addr roster base bits ((Nat.mul_le_mul_left 8 (width_at_selected G S board k (tail τ j) age p f g drift degree h
      previous nextM op.C op.w A M role old addr roster base).ge).trans
        (priced sites age p degree ordinary old A M base addr roster hp hd hD hc hP)) used

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
