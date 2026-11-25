import OAI.Hierarchy.DescentMatcherRoomCalendar
import OAI.Hierarchy.DescentNamedSignedUnit
import OAI.Hierarchy.DescentNamedPrimitiveCharge
import OAI.Hierarchy.DescentProfiledSnapshotWordRoom
import OAI.Hierarchy.DescentChosenGrainRoom
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentSenderBoardHeight

namespace OAI
/-! # Simultaneous operand and snapshot widths on the selected original register -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale Chronology DescentDatedAddressBook
open DescentDatedSeedStartup Filter
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (t f g rate drift limit n d:ℕ)
set_option quotPrecheck false
variable (τ β h M w:ℕ)
local notation "age_" => Nat.log 2 h/(2*β)
local notation "tail_" => tail τ age_
local notation "sched_" => stageNumbers G t age_ f g rate M tail_
local notation "k_" => groupBits t age_ (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p_" => headGrain G sched_ k_ h

/-- These are the numeric inputs of the funded ballot at its original, split head grain. -/
structure StageDateResources : Prop where
  matcher : MatcherRoom G sched_ k_ p_ h
  signed : ∀i H,i≤(sched_).length→2*(SignedStage.atDate G sched_ g k_ i H).unit≤h
  palette : OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift limit (drift+1) h
  snapshot : SnapshotWordRoom sched_ n d k_ tail_ p_ f g h w
  degree : maximumDegree (t+1)+1<2^w
  walks : (maximumDegree (t+1)+1)^4≤2^k_

/-- One bus divisor pays the term matcher, the signed field, the original primitive lookup,
and all archived reset words. The word ratio may be fixed before this divisor. -/
theorem cofinal_stage_date_resources :
    ∃β₀:ℕ,∀β≥β₀,∀ᶠ h:ℕ in atTop,∀M w,2^h≤M→M≤(2^h)^2→9*h≤w→
      StageDateResources G op t f g rate drift limit n d τ β h M w :=by
  let matchRate:=2*((2+hostRate t rate*(t+1)+
    ((donorRates G t f g rate).amount+(donorRates G t f g rate).work)+1+1)+5+0)
  let snapRate:=2*(1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g)
  let signedRate:=SignedStage.unitRate G t f g rate
  let primitiveRate:=OrdinaryBooks.primitiveLaneRate G t f g rate (drift+1)
  refine ⟨matchRate+snapRate+signedRate+primitiveRate+3,?_⟩
  intro β bound
  have pos:0<β:=by omega
  filter_upwards [matcher_room_at G t f g rate 0 τ β pos (by change matchRate≤β; omega),
    SignedStage.unitRate_cofinal G t f g rate β (by change signedRate<β;omega),
    OrdinaryBooks.eventual_primitive_calendar G op t f g rate τ β drift limit (drift+1)
      (by change primitiveRate+2≤β; omega),
    profiled_snapshot_word_room G t f g rate τ β n d pos (by change snapRate≤β; omega),
    eventually_ge_atTop (maximumDegree (t+1)+1),
    ResetMiddle.sender_board_at t β (hostRate t rate) (capRate G t g) (cutRate t f g)
      ((maximumDegree (t+1)+1)^4) pos] with h matchAt signAt primitiveAt resetsAt degreeAt walkAt
  intro M w low high bus
  let S:=stageNumbers G t (Nat.log 2 h/(2*β)) f g rate M (tail τ (Nat.log 2 h/(2*β)))
  let k:=groupBits t (Nat.log 2 h/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)
  let p:=headGrain G S k h
  have native : S.firstWidth G.b p≤h:=S.split_first_width G.b h (NativeBranch.binLimit (k:=k) S)
    (2^headChunk G S) (Nat.two_pow_pos _)
  have grain : p≤h:=S.grain_le_payload G.b p h G.base_pos native
  refine ⟨matchAt M p (by omega) grain,?_,primitiveAt,resetsAt M p w ?_ grain bus,?_,walkAt⟩
  · intro i H hi
    apply signAt M _ i H
    exact hi
  · simpa [←pow_mul,Nat.mul_comm] using high
  · exact (show maximumDegree (t+1)+1≤w by omega).trans_lt Nat.lt_two_pow_self

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
