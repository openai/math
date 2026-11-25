import OAI.Hierarchy.DescentOriginalReceiverWidth
import OAI.Hierarchy.DescentDatedScheduleSpace
import OAI.Hierarchy.DescentNamedFrontWords
import OAI.Hierarchy.DescentFundedSetupRate

namespace OAI
/-! # Uniform tariff of the signed and paid census setup on every original dated reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSIMDLookup Filter
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
local notation "out_" h:arg i:arg => (a_ h i).output G board D f g op.C op.w
local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i)

/-- The two packed GL lookups use the same selected payer precision as the
old-stage input. The sign mask uses the true previous cable width on every
one of the broadcast donor digits. -/
theorem original_funded_room (seed : Bounded sites)
    (earlier : ∀h i,age h i≤(S_ h i).length)
    (current : ∀h i,root h i≤c_ h i)
    (host : ∀h i,(old h i).venue.hosts=(S_ h i).hostSize (age h i))
    (group : ∀h i,(old h i).venue.groups=(S_ h i).groupCount (age h i))
    (block : ∀h i,(old h i).venue.k=k_ h)
    (paid : ∀ᶠ h:ℕ in atTop,∀i,((S_ h i).censusBits (size h i))*(old h i).venue.lanes≤h/2 ∧
      (old h i).venue.lanes≤h)
    (priced : Installed (fun h i=>out_ h i)) :
    DescentFundedCensus.Setup.ScalarRoom (fun h i=>(out_ h i).funded):=by
  let p:=fun h i=>out_ h i
  have axes:=schedule_space G t f g reset τ B sites age seed earlier
  obtain ⟨K,matrix⟩:=axes.matrices
  have square : ∀ᶠ h:ℕ in atTop,∀i,(c_ h i+k_ h)*(c_ h i+k_ h)≤K*h :=by
    filter_upwards [matrix] with h room
    intro i
    have upper : 2^((c_ h i+k_ h)*(c_ h i+k_ h))≤2^(K*h):=room i
    by_contra! larger
    exact (not_lt_of_ge upper) (Nat.pow_lt_pow_right (by decide) larger)
  have masks : Bounded (fun h i=>2^(root h i)):=axes.oldGroup.of_le fun h i=>
    (Nat.pow_le_pow_right (by decide) (current h i)).trans ((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  refine ⟨axes.oldHost.of_le (fun h i=>(host h i).le),axes.oldGroup.of_le (fun h i=>(group h i).le),?_,?_,masks,?_⟩
  · refine ⟨K,?_⟩
    filter_upwards [square] with h room
    intro i
    change 2^(old h i).venue.k≤_
    rw [block h i]
    apply Nat.pow_le_pow_right (by decide)
    let m:=c_ h i+k_ h
    have sub:k_ h≤ m:=Nat.le_add_left ..
    have sq:m≤ m*m:=by
      by_cases h0:m=0
      · simp [h0]
      · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)
    exact sub.trans (sq.trans (room i))
  · refine ⟨1,?_⟩
    filter_upwards [paid] with h before
    intro i
    exact (before i).2.trans (by simpa only [Nat.one_mul] using (Nat.lt_two_pow_self (n:=h)).le)
  · refine ⟨max 1 K,?_⟩
    filter_upwards [paid,priced,square] with h initial issued matrices
    intro i
    let v:=p h i
    let e:=root h i
    let c:=c_ h i
    let k:=k_ h
    let b:=(S_ h i).censusBits (size h i)
    have rootWidth (j : ℕ) (mem:j∈v.rootUnits):j*2^e≤h/2:=issued i j (.inl mem)
    have mixed:((b*2^k)+b)*2^e≤h/2:=rootWidth (v.funded.precision*2^v.middle.rootDepth+v.funded.precision) (by simp [rootUnits])
    have shuffle:((b+b)*2^k)*2^e≤h/2:=rootWidth ((v.funded.precision+v.funded.precision)*2^v.middle.rootDepth) (by simp [rootUnits])
    have flags:(v.middle.signedBits*2^k)*2^e≤h/2:=rootWidth (v.middle.signedBits*2^v.middle.rootDepth) (by simp [rootUnits])
    have epochView:e≤c:=current h i
    have dims:c-e+(e+k)=c+k:=by omega
    have donor:c-e+(e+k)-c=k:=by omega
    have half:h/2≤ max 1 K*h:=(Nat.div_le_self ..).trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right h (Nat.le_max_left 1 K))
    have matrixRoom := (matrices i).trans (Nat.mul_le_mul_right h (Nat.le_max_right 1 K))
    change b*(old h i).venue.lanes≤_ ∧ (b*2^(old h i).venue.k+b)*2^e≤_ ∧
      (b+b)*2^(e+k)≤_ ∧ (c-e+(e+k))*(c-e+(e+k))≤_ ∧
      (v.middle.signedBits*2^(c-e+(e+k)-c))*2^e≤_
    rw [block h i,dims]
    have bit : (c+k)-c=k:=by omega
    rw [bit]
    refine ⟨(initial i).1.trans half,mixed.trans half,?_,matrixRoom,flags.trans half⟩
    simpa only [Nat.pow_add,Nat.mul_assoc,Nat.mul_comm (2^e) (2^k)] using shuffle.trans half

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
