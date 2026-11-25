import OAI.Hierarchy.DescentFundedCensusRoles
import OAI.Hierarchy.DescentFundedSetupRate
import OAI.Hierarchy.DescentFundedCensusRate
import OAI.Hierarchy.DescentDatedResetMiddle
import OAI.Hierarchy.DescentStageVenueChange

namespace OAI
/-! # The charged reset atlas and its remix are fixed by the earlier public date -/
namespace Hierarchy.DescentNamedFundedChart
open DescentDatedAddressBook DescentSixParty DescentSIMDLookup DescentFundedCensus
open DescentDenseHostOrder DescentContacts DescentCommonHost DescentResetHostSize
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section

variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (old : StageVenueTail.Date) (middle : ResetMiddle)

def setup : DescentFundedCensus.Setup :=
  ⟨old.hosts,old.groups,2^old.k,old.lanes,middle.signedLanes,old.paidBits,
   middle.high,middle.low,middle.stencil.c,old.degree,old.cap,middle.rootLanes⟩

def lowCount := 2^middle.rootDepth
def operandWidth :=
  max (1+old.paidBits) (max ((middle.stencil.t+old.paidBits)*lowCount middle)
    (1+middle.rootField*DescentFallbackPeriod.inputCount old.degree (lowCount middle) old.cap n middle.rootDepth))
def shape (f gain : ℕ) : Shape :=
  ⟨(roster board middle.rootDepth (GroupStage.depthBound old.degree n f gain)).card,old.hosts,middle.rootGroups,
    middle.rootLanes,old.paidBits,operandWidth (n:=n) old middle⟩

def shapes (f gain : ℕ) (j : Fin (shape board old middle f gain).jobs) :=
  let e:=localRank board middle.rootDepth (GroupStage.depthBound old.degree n f gain)
  let eqv:=Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card _).mpr ⟨e.injective,by simp⟩)
  (eqv.symm j).val

theorem fits_operation (C packet batch f gain : ℕ) (io : Ports middle.rootDepth n) (has : ProtocolRAM.Expr)
    (actor : Node Unit (Unit×Endpoint (2^n)) (DescentCommonPalette.rotor board).Site) :
    let job:=compile (Ht:=GroupStage.depthBound old.degree n f gain) board C packet batch old.paidBits old.cap f
      old.degree old.cap middle.rootField middle.stencil.t io has actor
    job.left+job.right≤operandWidth (n:=n) old middle :=by
  intro job
  rcases actor with ⟨s,⟨_,label⟩⟩|⟨s,t,a⟩|⟨s,⟨_,label⟩,path⟩
  · simp [job,compile,trunk,operandWidth,lowCount,Nat.add_mul]
  · change 1+0≤operandWidth (n:=n) old middle
    exact (Nat.le_add_right ..).trans (Nat.le_max_left ..)
  · dsimp only [job,compile]
    split
    · exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    · exact Nat.zero_le _

theorem masks (f gain : ℕ) : 1+(shape board old middle f gain).bits≤(shape board old middle f gain).broadcast :=
  Nat.le_max_left ..

variable {ι : ℕ→Type*}
open Filter
theorem paid_rate (old : ∀h,ι h→StageVenueTail.Date) (middle : ∀h,ι h→ResetMiddle)
    (hosts : Bounded (fun h i=>(old h i).hosts)) (groups : Bounded (fun h i=>(old h i).groups))
    (blocks : Bounded (fun h i=>2^(old h i).k)) (previous : Bounded (fun h i=>(old h i).lanes))
    (pitch : Bounded (fun h i=>(middle h i).signedLanes))
    (widths : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀i,let d:=old h i; let a:=middle h i;
      d.paidBits*d.lanes≤K*h ∧ (d.paidBits*2^d.k+d.paidBits)*a.signedLanes≤K*h ∧
      (d.paidBits+d.paidBits)*2^a.low≤K*h ∧ (a.high+a.low)*(a.high+a.low)≤K*h ∧
      (DescentSignedCableCodec.width d.degree d.cap*2^(a.high+a.low-a.stencil.c))*a.rootLanes≤K*h) :
    DescentFundedCensus.Setup.ScalarRoom (fun h i=>setup (old h i) (middle h i)) :=
  ⟨hosts,groups,blocks,previous,pitch,widths⟩

theorem atlas_rate {nd gd : ℕ→ℕ} (boards : ∀h,NonlinearExpanders.Graph (nd h) (gd h))
    (old : ∀h,ι h→StageVenueTail.Date) (middle : ∀h,ι h→ResetMiddle) (f gain : ∀h,ι h→ℕ)
    (hosts : Bounded (fun h i=>(old h i).hosts)) (groups : Bounded (fun h i=>(middle h i).rootGroups))
    (lanes : Bounded (fun h i=>(middle h i).rootLanes))
    (Y : Bounded (ι:=ι) fun h _=>2^nd h) (steps : Bounded (ι:=ι) fun h _=>gd h)
    (height : Bounded (fun h i=>2^(GroupStage.depthBound (old h i).degree (nd h) (f h i) (gain h i)+1)))
    (blocks : Bounded (fun h i=>2^((middle h i).rootDepth+1)))
    (width : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=middle h i; let d:=old h i
      (1+d.paidBits)*a.rootLanes≤K*h ∧ ((a.stencil.t+d.paidBits)*2^a.rootDepth)*a.rootLanes≤K*h ∧
      (1+a.rootField*DescentFallbackPeriod.inputCount d.degree (2^a.rootDepth) d.cap (nd h) a.rootDepth)*a.rootLanes≤K*h) :
    Shape.ScalarRoom (fun h i=>shape (boards h) (old h i) (middle h i) (f h i) (gain h i)) :=by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  have rotor:=(((c 2).mul steps).add (c 4)).mul Y
  have tree:=(Y.add (c 1)).mul height
  have rosterRoom:=((c 2).mul ((Y.add (c 1)).add (rotor.add tree))).mul blocks
  refine ⟨rosterRoom.of_le (fun h i=>roster_bound (boards h) _ _),hosts,groups,lanes,?_⟩
  obtain ⟨K,hK⟩:=width
  refine ⟨K,hK.mono fun h h₀ i=>?_⟩
  rcases h₀ i with ⟨a,b,c⟩
  dsimp only [shape,operandWidth,lowCount]
  simp only [max_def]
  split_ifs <;> assumption

end
end Hierarchy.DescentNamedFundedChart

end OAI
