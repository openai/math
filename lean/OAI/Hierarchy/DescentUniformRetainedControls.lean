import OAI.Hierarchy.DescentUniformRetainedSpace
import OAI.Hierarchy.DescentRetainedCalendarAperture

namespace OAI
/-! # Uniform room for both home selections and dense placements -/
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

set_option maxHeartbeats 800000 in
/-- Each target shares the measured source fields and installed lookup pages. -/
theorem uniform_retained_controls (cal : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(S_ h i).hostSize (age h i))
    (newH : Bounded fun h i=>(S_ h i).hostSize (age h i+1))
    (newG : Bounded fun h i=>(S_ h i).groupCount (age h i+1))
    (M : Bounded fun h i=>2^(root h i))
    (before : ∀h i,age h i<(S_ h i).length)
    (priced : Installed (out_))
    (selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out_ h i).groupWidth≤h)
    (previous_ : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>A_ h i))
    (roles : DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>T_ h i)) :
    DescentRetainedControl.Layout.ScalarRoom (fun h i=>(out_ h i).setup.seven.control) ∧
    DescentRetainedControl.Layout.ScalarRoom (fun h i=>(out_ h i).roleTransfer.control) ∧
    DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(out_ h i).setup.placement)
      (fun h i=>(out_ h i).setup.retainedFields) ∧
    DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(out_ h i).roleTransfer.placement)
      (fun h i=>(out_ h i).roleTransfer.batch) ∧
    DescentResetRetainedPlacement.Chart.ScalarRoom (fun h i=>(out_ h i).setup.placement)
      (fun h i=>(out_ h i).setup.signedFields) :=by
  let p:=out_
  let A:=fun h i=>A_ h i
  let T:=fun h i=>T_ h i
  let shape:=cal.sheets.shapes.bounded level
  have geomA (h : ℕ) (i : ι h) : (A h i).CalendarPitch (c_ h i) (k_ h i) h (p h i).retainedUnit :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have geomT (h : ℕ) (i : ι h) : (T h i).CalendarPitch (c_ h i) (k_ h i) h (p h i).retainedRoleUnit :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have gatherA (h : ℕ) (i : ι h) (q : 8*(p h i).groupWidth≤h) :
      ((A h i).stripWord+(A h i).donors*Nat.clog 2 ((A h i).donors+1))*(A h i).decodedLanes≤h/2 :=by
    apply DescentSixParty.AtomSchedule.retainedSelectorAperture (S_ h i) G (k_ h i) (tail_ h i) drift (degree h i)
      (size h i) (age h i) h (old h i).nodes (old h i).arguments (old h i).operandLanes rfl rfl (before h i)
    exact (Nat.mul_le_mul_left 8 ((p h i).groupWidth_fit (t:=(p h i).retainedUnit)
      (Or.inr (by simp [receiverUnits])))).trans q
  have gatherT (h : ℕ) (i : ι h) (q : 8*(p h i).groupWidth≤h) :
      ((T h i).stripWord+(T h i).donors*Nat.clog 2 ((T h i).donors+1))*(T h i).decodedLanes≤h/2 :=by
    let v:=T h i
    let u:=(p h i).retainedRoleUnit
    have g:=geomT h i
    have geo:=DescentResetRetainedSetup.Layout.CalendarPitch.geometry v g
    have charged:=DescentPackedWalsh.keys_fit (m:=c_ h i) (b:=u) (h:=h) (Nat.le_max_left 1 _)
      ((Nat.mul_le_mul_left 8 ((p h i).groupWidth_fit (t:=u) (Or.inr (by simp [u,receiverUnits])))).trans q)
    change 1+(u+u)*2^(DescentPackedWalsh.laneBits (c_ h i) h u)≤h/2 at charged
    change (v.bits*v.donors+v.donors*Nat.clog 2 (v.donors+1))*v.decodedLanes≤h/2
    rw [geo.2.1,g.decoded,g.gather]
    have l : v.bits*v.blocks+v.blocks*Nat.clog 2 (v.blocks+1)≤u:=
      (Nat.le_max_right ..).trans (Nat.le_max_right ..)
    apply (Nat.mul_le_mul_right _ l).trans
    change u * 2^(DescentPackedWalsh.laneBits (c_ h i) h u) ≤ h/2
    rw [Nat.add_mul] at charged
    omega
  let W (v : DescentResetRetainedSetup.Layout) (h : ℕ) (i : ι h) : DescentRetainedControl.Layout :=
    ⟨v.hosts,v.grouped,(p h i).setup.placement.shapes,v.donors,D,(p h i).setup.oldCap,
      (p h i).middle.rootField,v.bits,2^(root h i),v.decodedLanes⟩
  have controls (v : ∀h,ι h→DescentResetRetainedSetup.Layout) (old : DescentResetRetainedSetup.Layout.ScalarRoom v)
      (d : ∀h i,(v h i).donors=2^(k_ h i))
      (key : ∀h i,8*(p h i).groupWidth≤h→((v h i).stripWord+(v h i).donors*Nat.clog 2 ((v h i).donors+1))*(v h i).decodedLanes≤h/2) :
      DescentRetainedControl.Layout.ScalarRoom (fun h i=>W (v h i) h i) :=by
    refine ⟨old.hosts,old.grouped,shape,M,old.decodedLanes,1,?_⟩
    filter_upwards [priced,selected] with h w s
    intro i
    rw [Nat.one_mul]
    apply le_trans _ (Nat.div_le_self h 2)
    have raw:=w i ((p h i).setup.packets.oldBits*((p h i).setup.packets.stage 0 true).fields)
      (Or.inl (by
        change (p h i).setup.packets.oldBits*((p h i).setup.packets.stage 0 true).fields ∈ (p h i).rootUnits
        simp [rootUnits]))
    have select:=w i (2^(k_ h i)*Nat.clog 2 (2^(k_ h i)+1)) (Or.inl (by
      let L:=2^(p h i).middle.rootDepth
      change L*Nat.clog 2 (L+1) ∈ (p h i).rootUnits
      simp [rootUnits,L]))
    have dpos : 0<(v h i).donors:=by rw [d];exact Nat.two_pow_pos _
    refine max_le ?_ (max_le ?_ ?_)
    · change ((p h i).middle.rootField*DescentRotorWindowArchive.count D (v h i).donors (p h i).setup.oldCap)*2^(root h i)≤h/2
      rw [d];exact raw
    · change (Nat.clog 2 ((v h i).donors+1)*(v h i).donors)*2^(root h i)≤h/2
      rw [d,Nat.mul_comm (Nat.clog 2 _)];exact select
    · change (max (v h i).bits ((v h i).bits*(v h i).donors)+Nat.clog 2 ((v h i).donors+1)*(v h i).donors)*(v h i).decodedLanes≤h/2
      rw [max_eq_right (Nat.le_mul_of_pos_right _ dpos),Nat.mul_comm (Nat.clog 2 _)]
      exact key h i (s i)
  let widths (b : ∀h,ι h→ℕ) (present : ∀h i,b h i∈(p h i).rootUnits ∨ b h i∈(p h i).receiverUnits) :
      ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,b h i*(p h i).receiver.lanes≤K*h :=
    ⟨1,priced.mono fun h pricedAt i=>by rw [Nat.one_mul];exact (pricedAt i _ (present h i)).trans (Nat.div_le_self ..)⟩
  obtain ⟨Ka,wa⟩:=previous_.packed
  obtain ⟨Kt,wt⟩:=roles.packed
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  have Afields:=(((c (2*7)).mul previous_.args).mul previous_.nodes).add previous_.nodes
  have donorA (h : ℕ) (i : ι h) : (A h i).donors=2^(k_ h i):=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry _ (geomA h i)).2.1
  have donorT (h : ℕ) (i : ι h) : (T h i).donors=2^(k_ h i):=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry _ (geomT h i)).2.1
  have strips:=((cal.sheets.block.bounded level).of_le fun h i=>(donorA h i).le).mul ((c 2).mul (cal.previousCap.bounded level))
  have signedRoom := widths (fun h i=>(p h i).setup.signedFields.bits*(p h i).sheets.blocks)
    (fun h i=>Or.inr (by simp [receiverUnits]))
  refine ⟨controls A previous_ donorA gatherA,controls T roles donorT gatherT,
    ⟨oldH,newH,shape,newG,previous_.blocks,M,Afields,previous_.decodedLanes,
      ⟨Ka,wa.mono fun _ q i=>(q i).2.2.2.2.2.2.2⟩,
      widths (fun h i=>(p h i).setup.retainedFields.bits*(p h i).sheets.blocks) (fun h i=>Or.inr (by simp [receiverUnits]))⟩,
    ⟨oldH,newH,shape,newG,roles.blocks,M,roles.nodes,roles.decodedLanes,
      ⟨Kt,wt.mono fun _ q i=>(q i).2.2.2.2.2.2.2⟩,
      widths (fun h i=>(p h i).roleTransfer.transfer.bits*(p h i).sheets.blocks) (fun h i=>Or.inr (by simp [receiverUnits]))⟩,
    ⟨oldH,newH,shape,newG,previous_.blocks,M,strips,M,?_,
      signedRoom⟩⟩
  obtain ⟨Ks,lim⟩:=signedRoom
  refine ⟨Ks,lim.mono (fun h ok i=>?_)⟩
  change (p h i).setup.signedFields.bits*(p h i).receiver.lanes ≤ Ks*h
  have pos : 0<(p h i).sheets.blocks := Nat.two_pow_pos _
  exact (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ pos)).trans (ok i)


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
