import OAI.Hierarchy.DescentOriginalRootLawRegion

namespace OAI
/-! # The original root-law allocation for a varying family of reset schedules -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (D f g C packet : ℕ) {ι : ℕ→Type*} (z : ∀h,ι h→Sample)
local notation "out_" => fun h i=>(z h i).output G board D f g C packet

/-- The exponent covers all samples in the same fiber, including different cutoffs. -/
theorem uniform_sample_root_law
    (payload : ∀h i,(z h i).payload=h) (pitch : ∀h i,(z h i).lanes=2^(z h i).root)
    (hosts : Bounded (fun h i=>let s:=z h i;s.sched.hostSize s.age))
    (groups : Bounded (fun h i=>let s:=z h i;2^(s.sched.groupWidth s.k s.tail s.age)))
    (lanes : Bounded (fun h i=>2^(z h i).root))
    (priced : Installed (out_)) : Bounded (fun h i=>(out_ h i).middle.rootLawWidth) :=by
  obtain ⟨A,room⟩:=bank_space hosts groups lanes
  refine ⟨A,?_⟩
  filter_upwards [room,priced] with h banks keys
  intro i
  let s:=z h i
  let v:=out_ h i
  let m:=v.middle
  let args:=DescentFallbackPeriod.Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth)
    v.front.donor.cap m.rotorBits m.rootDepth
  have native : v.receiver.lanes=m.rootLanes :=pitch h i
  have law : m.rootField*(args+1)*v.receiver.lanes≤h/2 :=keys i _ (.inl (by simp [rootUnits,args,m,v]))
  have cmp : m.stencil.n*v.receiver.lanes≤h/2 :=keys i _ (.inl (by simp [rootUnits,m,v]))
  rw [native] at law cmp
  have half : h/2=s.payload/2 :=congrArg (fun u : ℕ=>u/2) (payload h i).symm
  have bound := ResetMiddle.calendar_law_bound s.sched s.k s.tail s.age s.p f D s.payload s.root s.previous n
    (GroupStage.depthBound D n f g) (capCalendar G.b s.sched.rounds g s.sched.height) (law.trans_eq half) (cmp.trans_eq half)
  change m.rootLawWidth≤ResetMiddle.bankBound s.payload (s.sched.hostSize s.age)
    (2^(s.sched.groupWidth s.k s.tail s.age)) (2^s.root) at bound
  have eqn : s.payload=h :=payload h i
  rw [eqn] at bound
  exact bound.trans (banks i)

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
