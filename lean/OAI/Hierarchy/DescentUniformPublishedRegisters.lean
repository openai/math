import OAI.Hierarchy.DescentPublishedRegisterShape

namespace OAI
/-! # Returned register bounds over a common family of selected reset schedules -/
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
local notation "p" => fun h i=>(sample h i).output G board D f g op.C op.w

theorem uniform_published (calend : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(sample h i).sched.hostSize (age h i))
    (newH : Bounded fun h i=>(sample h i).sched.hostSize (age h i+1))
    (newG : Bounded fun h i=>(sample h i).sched.groupCount (age h i+1))
    (lanes : Bounded fun h i=>2^(root h i))
    (priced : Installed p) : PublishedRegisters p :=by
  let c (j:ℕ):=Bounded.const (ι:=ι) j
  have positiveM (h) (i:ι h) : 0<(p h i).receiver.lanes:=Nat.two_pow_pos _
  have L:=calend.sheets.block.bounded level
  have nodes:=calend.nodes.bounded level
  have args:=calend.arguments.bounded level
  have roots:=((c 2).mul (L.mul (c (2^n))))
  have key {u : ResetOutput→ℕ} (inside:∀h i,u (p h i)∈(p h i).receiverUnits ∨ u (p h i)∈(p h i).rootUnits) :
      ∀ᶠ h:ℕ in atTop,∀i,u (p h i)*(p h i).receiver.lanes≤h :=
    priced.mono fun h w i=>(w i _ (Or.comm.mp (inside h i))).trans (Nat.div_le_self _ _)
  have node:=key (u:=fun v=>v.nodeBits*v.nodes+v.nodeBits) (fun _ _=>.inl (by simp [receiverUnits]))
  have role:=key (u:=fun v=>v.primitive.chart.bits*v.primitive.chart.nodes+v.primitive.chart.bits)
    (fun _ _=>.inl (by simp [receiverUnits]))
  have gates:=key (u:=fun v=>v.primitive.rawBits) (fun _ _=>.inl (by simp [receiverUnits]))
  have rotor:=key (u:=fun v=>v.setup.rotorBits+1) (fun _ _=>.inl (by simp [receiverUnits]))
  have pitch:=rotor.mono fun h w i=>(Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (w i)
  have head:=key (u:=fun v=>max v.metadata.paidBits (v.metadata.spanBits+v.metadata.chart.bits))
    (fun _ _=>.inl (by simp [receiverUnits]))
  have amount:=key (u:=fun v=>v.rootOutputBits) (fun _ _=>.inr (by simp [rootUnits]))
  have realRoot : ∀ᶠ h:ℕ in atTop,∀i,let birth:=(p h i).birth;birth.rootBits*birth.stop*birth.sourceLanes≤h :=by
    filter_upwards [amount] with h w
    intro i
    let birth:=(p h i).birth
    have lo:birth.rootBits*birth.stop≤(p h i).rootOutputBits:=(Nat.le_max_right ..).trans (Nat.le_max_left ..)
    exact (Nat.mul_le_mul_right _ lo).trans (w i)
  have fresh:=key (u:=fun v=>v.birth.aperture) (fun _ _=>.inl (by simp [receiverUnits]))
  have shift:=key (u:=fun v=>v.birth.rootBits*v.sheets.blocks) (fun _ _=>.inl (by simp [receiverUnits]))
  have charts:DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(p h i).birth.placement)
      (fun h i=>(p h i).birth.batch) :=
    ⟨oldH,newH,calend.sheets.shapes.bounded level,newG,L,lanes,roots.mul nodes,lanes,
      ⟨1,by simp only [Nat.one_mul]; exact gates⟩,⟨1,by simp only [Nat.one_mul]; exact shift⟩⟩
  have primitive : DescentResetPrimitiveCheckpoint.Shape.ScalarRoom (fun h i=>(p h i).primitive) :=
    ⟨⟨L,nodes,newH,newG,lanes,⟨1,by simp only [Nat.one_mul]; exact role⟩⟩,
      ⟨1,by filter_upwards [gates,pitch] with h g m;intro i;simp only [Nat.one_mul]; exact max_le (g i) (m i)⟩⟩
  have metadataRoom : MetadataReturn.ScalarRoom (fun h i=>(p h i).metadata) :=
    ⟨⟨L,nodes,newH,newG,lanes,⟨1,by simp only [Nat.one_mul]; exact node⟩⟩,
      ⟨1,by simp only [Nat.one_mul]; exact head⟩⟩
  refine ⟨primitive,⟨charts,nodes,args,roots,⟨1,by simp only [Nat.one_mul]; exact realRoot⟩,
    ⟨1,by simp only [Nat.one_mul]; exact fresh⟩⟩,metadataRoom,args,(((c 7).mul args).mul L).mul nodes,
    (c (2^g)).mul (calend.previousCap.bounded level),?_,?_,?_,?_,?_⟩
  · exact key (u:=fun v=>v.setup.fieldBits) (fun _ _=>.inl (by simp [receiverUnits]))
  · have paid:=key (u:=fun v=>v.sheets.metaBits) (fun _ _=>.inr (by simp [rootUnits]))
    exact Bounded.pow_of_linear (K:=1) (paid.mono fun h w i=>by
      simpa only [Nat.one_mul] using (Nat.le_mul_of_pos_right _ (positiveM h i)).trans (w i))
  · filter_upwards [rotor] with h w
    intro i
    have fit:=w i
    have good:=positiveM h i
    change (p h i).setup.rotorBits+(p h i).receiver.lanes≤h
    rw [Nat.add_mul,Nat.one_mul] at fit
    exact (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ good) _).trans fit
  · exact key (u:=fun v=>v.sheets.metaBits*5+v.sheets.metaBits*5) (fun _ _=>.inl (by simp [receiverUnits]))
  · filter_upwards [priced] with h w
    intro i
    let v:=p h i
    have lower (a:ℕ) (mem : a∈v.rootUnits ∨ a∈v.receiverUnits) :
        a*v.receiver.lanes≤h :=(w i a mem).trans (Nat.div_le_self _ _)
    have sq:=lower ((v.middle.signedBits+v.middle.signedBits)*2^v.middle.rootDepth) (.inl (by simp [rootUnits]))
    have blocks:0<v.middle.oldBlocks:=Nat.two_pow_pos _
    have previous:v.middle.signedBits*v.middle.oldBlocks+v.middle.signedBits≤
        (v.middle.signedBits+v.middle.signedBits)*2^v.middle.rootDepth :=by
      rw [Nat.add_mul]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ blocks) _
    exact ⟨(Nat.mul_le_mul_right _ previous).trans sq,lower v.middle.projectBits (.inl (by simp [rootUnits])),
      lower (8*v.sheets.metaBits+v.sheets.metaBits) (.inr (by simp [receiverUnits])),
      lower (v.receiver.queryBits+v.receiver.signedBits) (.inr (by simp [receiverUnits])),
      lower (v.ticketBits*5+v.ticketBits*5) (.inr (by simp [receiverUnits])),
      lower (v.sheets.metaBits*7+v.sheets.metaBits) (.inr (by simp [receiverUnits])),
      lower (v.sheets.metaBits*7+v.ticketBits) (.inr (by simp [receiverUnits])),
      lower (DescentResetSourceSeekRAM.keyBits 4 v.sheets.candidates+v.sheets.metaBits) (.inr (by simp [receiverUnits]))⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
