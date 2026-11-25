import OAI.Hierarchy.DescentCalendarRootLaw
import OAI.Hierarchy.DescentOriginalPeerRegions

namespace OAI
/-! # Exponential address room for the selected root book, including original reservations -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
set_option hygiene false
set_option quotPrecheck false
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w


set_option hygiene true
set_option quotPrecheck true
theorem bank_space {H K M : ∀h,ι h→ℕ} (hosts : Bounded H) (groups : Bounded K) (lanes : Bounded M) :
    Bounded (fun h i=>ResetMiddle.bankBound h (H h i) (K h i) (M h i)) :=by
  have page : Bounded (ι:=ι) (fun h _=>2^h) :=⟨1,Eventually.of_forall (by simp)⟩
  have batch : Bounded (fun h i=>DescentSIMDLookup.chunks (K h i) (M h i)) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  let two:=Bounded.const (ι:=ι) 2
  let one:=Bounded.const (ι:=ι) 1
  exact (one.add (((page.mul (two.mul page)).add page).add (hosts.mul batch).padded)).add
    (page.max' (((page.add page).add hosts.padded).add hosts.padded))

/-- The old estimator and the root catalogue use the same selected physical lanes.
The preceding count header and the original stage geometry suffice for all address bounds. -/
theorem original_root_law (seed : Bounded sites) (earlier : ∀h i,age h i≤(S_ h i).length)
    (next : ∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (priced : Installed (out_)) : Bounded (fun h i=>(out_ h i).middle.rootLawWidth) := by
  have axes:=schedule_space G t f g reset τ B sites age seed earlier
  let H:=fun h i=>(S_ h i).hostSize (age h i)
  let K:=fun h i=>2^((S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i))
  let M:=fun h i=>2^(root h i)
  have gBound : Bounded K:=axes.oldGroup.of_le (fun h i=>((S_ h i).group_power (k:=k_ h) rfl rfl _).le)
  have mBound : Bounded M:=axes.newGroup.of_le fun h i=>
    (Nat.pow_le_pow_right (by decide) (next h i)).trans ((S_ h i).group_power (k:=k_ h) rfl rfl _).le
  obtain ⟨ex,banks⟩:=bank_space (H:=H) axes.oldHost gBound mBound
  refine ⟨ex,?_⟩
  filter_upwards [banks,priced] with h area keys
  intro i
  let v:=out_ h i
  let m:=v.middle
  let N:=DescentFallbackPeriod.Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
  have packed : m.rootField*(N+1)*v.receiver.lanes≤h/2 := keys i _ (.inl (by simp [rootUnits,N,m,v]))
  have cmp : m.stencil.n*v.receiver.lanes≤h/2 := keys i _ (.inl (by simp [rootUnits,m,v]))
  exact (ResetMiddle.calendar_law_bound (S_ h i) (k_ h) (tail τ (J_ h)) (age h i) (size h i) f D h
    (root h i) (previous h i) n (GroupStage.depthBound D n f g) (capCalendar G.b t g (J_ h)) packed cmp).trans (area i)

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
