import OAI.Hierarchy.DescentOriginalPeerRegions
import OAI.Hierarchy.DescentDatedRetainedPitches
import OAI.Hierarchy.DescentRetainedCalendarAperture
import OAI.Hierarchy.DescentInitialArgumentCapacity

namespace OAI
/-! # Retained archive address bounds for varying structural heights -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g reset D drift : ℕ) {ι : ℕ→Type*}
    (index : ℕ→ℕ) (tailCost chosenJ sites age size degree root previous nextM base : ∀h,ι h→ℕ)
    (old : ∀h,ι h→Prior)
set_option hygiene false
set_option quotPrecheck false
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

set_option hygiene true
set_option quotPrecheck true
private theorem bounded_eventually_below {b a : ∀h,ι h→ℕ} (upper : Bounded b)
    (le : ∀ᶠ h:ℕ in atTop,∀i,a h i≤b h i) : Bounded a :=by
  obtain ⟨K,ok⟩:=upper
  exact ⟨K,(le.and ok).mono fun _ q i=>(q.1 i).trans (q.2 i)⟩

/-- Both prior archive transfers use their actual lane pitches on every indexed reset. -/
theorem uniform_retained (cal : CalendarInputs G board D f g op.C op.w index z)
    (level : ∀ᶠ h:ℕ in atTop,index h≤h)
    (oldH : Bounded fun h i=>(S_ h i).hostSize (age h i))
    (oldG : Bounded fun h i=>2^(c_ h i))
    (matrices : Bounded fun h i=>2^((c_ h i+k_ h i)*(c_ h i+k_ h i)))
    (before : ∀h i,age h i<(S_ h i).length)
    (caps : ∀ᶠ h:ℕ in atTop,∀i,(old h i).nodes≤(S_ h i).retainedNodes ∧
      (old h i).arguments≤(S_ h i).retainedArgumentsAt G drift)
    (priorLanes : Bounded (fun h i=>(old h i).operandLanes))
    (roleLanes : Bounded (fun h i=>(old h i).primitiveLanes))
    (archive : ∀ᶠ h:ℕ in atTop,∀i,(A_ h i).wholeWord*(old h i).operandLanes≤h/2 ∧
      (T_ h i).wholeWord*(old h i).primitiveLanes≤h/2)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out_ h i).groupWidth≤h) :
    DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>A_ h i) ∧
    DescentResetRetainedSetup.Layout.ScalarRoom (fun h i=>T_ h i) :=by
  let p:=out_
  have groups : Bounded (fun h i=>(S_ h i).groupCount (age h i)):=oldG.of_le fun h i=>
    ((S_ h i).group_power (k:=k_ h i) rfl rfl _).symm.le
  obtain ⟨K,area⟩:=matrices
  have square : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(c_ h i+k_ h i)*(c_ h i+k_ h i)≤K*h :=by
    refine ⟨K,area.mono fun h rows i=>?_⟩
    by_contra! large
    exact (not_lt_of_ge (rows i)) (Nat.pow_lt_pow_right (by decide) large)
  have ns : Bounded (fun h i=>(S_ h i).retainedNodes):=cal.nodes.bounded level
  have args : Bounded (fun h i=>(S_ h i).retainedArgumentsAt G drift):=cal.arguments.bounded level
  have oldNodes:=bounded_eventually_below ns (caps.mono fun _ q i=>(q i).1)
  have oldArgs:=bounded_eventually_below args (caps.mono fun _ q i=>(q i).2)
  have blocks : Bounded (fun h (i:ι h)=>2^(k_ h i)):=cal.sheets.block.bounded level
  have seven (h : ℕ) (i : ι h) : (A_ h i).CalendarPitch (c_ h i) (k_ h i) h (p h i).retainedUnit :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have token (h : ℕ) (i : ι h) : (T_ h i).CalendarPitch (c_ h i) (k_ h i) h (p h i).retainedRoleUnit :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have unit (h : ℕ) (i : ι h) : (p h i).retainedUnit≤(p h i).groupWidth ∧
      (p h i).retainedRoleUnit≤(p h i).groupWidth :=by
    constructor <;> apply (p h i).groupWidth_fit <;> right <;> simp [receiverUnits]
  constructor
  · apply DescentResetRetainedSetup.Layout.calendar_room_of_matrix _ _ _ _ seven oldH groups blocks
      ns args oldNodes oldArgs priorLanes oldG (archive.mono fun _ q i=>(q i).1) square
    filter_upwards [caps,selected] with h nc enough
    intro i
    let S:=S_ h i
    let k:=k_ h i
    let l:=tail_ h i
    let a:=age h i
    let v:=A_ h i
    have all:=S.previousWidth G k l drift (degree h i) (size h i) a h (old h i).nodes
      (old h i).arguments (old h i).operandLanes (nc i).1 (nc i).2 rfl rfl (before h i)
    have sel:=S.selector_width G k l drift (degree h i) (size h i) a h (old h i).nodes
      (old h i).arguments (old h i).operandLanes rfl rfl (before h i)
    refine ⟨Nat.le_max_left 1 _,(Nat.mul_le_mul_left 8 (unit h i).1).trans (enough i),?_⟩
    exact max_le all.1 (max_le ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
      (max_le all.2 sel))
  · let zero:=Bounded.const (ι:=ι) 0
    apply DescentResetRetainedSetup.Layout.calendar_room_of_matrix _ _ _ _ token oldH groups blocks
      ns zero oldNodes zero roleLanes oldG (archive.mono fun _ q i=>(q i).2) square
    filter_upwards [caps,selected] with h nc enough
    intro i
    let v:=T_ h i
    let b:=v.bits
    let N:=(S_ h i).retainedNodes
    let X:=2^(k_ h i)
    have nonzero : 0<X:=Nat.two_pow_pos _
    have donors : v.donors=X:=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry v (token h i)).2.1
    let core:=(b*(2*N+1)+b)*X
    let sel:=b*X+X*Nat.clog 2 (X+1)
    have width : (p h i).retainedRoleUnit=max 1 (max core sel):=rfl
    refine ⟨Nat.le_max_left 1 _,(Nat.mul_le_mul_left 8 (unit h i).2).trans (enough i),?_⟩
    rw [width]
    apply le_trans _ (Nat.le_max_right 1 _)
    apply max_le
    · apply le_trans _ (Nat.le_max_left core sel)
      have n:=(nc i).1
      change b*(old h i).nodes≤(b*(2*N+1)+b)*X
      exact ((Nat.mul_le_mul_left b (n.trans (by dsimp [N];omega))).trans (Nat.le_add_right ..)).trans
        (Nat.le_mul_of_pos_right _ nonzero)
    · apply max_le
      · apply le_trans _ (Nat.le_max_left core sel)
        change b*X+b≤(b*(2*N+1)+b)*X
        have bh : b≤b*X:=Nat.le_mul_of_pos_right _ nonzero
        have mid : b*X≤(b*(2*N+1))*X:=Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
        rw [Nat.add_mul]
        exact Nat.add_le_add mid bh
      · apply max_le
        · apply le_trans _ (Nat.le_max_left core sel)
          change (b*v.donors)*((2+7*0)*(old h i).nodes)+b*v.donors≤core
          rw [donors]
          have n:=Nat.mul_le_mul_left (b*X*2) (nc i).1
          dsimp [core,N] at *
          nlinarith only [n,Nat.zero_le (b*X)]
        · apply le_trans _ (Nat.le_max_right core sel)
          change b*v.donors+v.donors*Nat.clog 2 (v.donors+1)≤ sel
          rw [donors]


end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
