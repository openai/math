import OAI.Hierarchy.DescentDatedArchiveWidths
import OAI.Hierarchy.DescentOrdinaryHostShelfRoom
import OAI.Hierarchy.DescentPublicDegreeNumbers
import OAI.Hierarchy.DescentDyadicHostDates

namespace OAI
/-! # Actual padded host axes at each of the three chronological register constructors -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedAddressBook DescentDatedSeedStartup DescentPacking.PackedMatch.Local.Stage
open DescentPrimitivePalette DescentDatedOperandReadPipeline ProtocolRAM
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)


open DescentCompiler.TerminalScale DescentHostDegree
structure Population (ports : DatePorts) (i : ℕ) : Prop where
  groups : ports.venue.groups=S.groupCount i
  venue_low : S.hostSize i ≤ ports.venue.hosts
  venue_high : ports.venue.hosts ≤ hostRows (S.hostSize i)
  positive : 0<ports.operandHosts
  earlier : ports.operandHosts≤ports.venue.hosts

theorem Population.venue_eq {ports : DatePorts} {i d k : ℕ} (pop : Population S ports i)
    (base : S.initialSites=2^d) (radix : S.radix=2^k) : ports.venue.hosts=S.hostSize i :=
  le_antisymm (pop.venue_high.trans_eq (NativePitch.hostRows_at_date base radix i)) pop.venue_low

theorem seed_population {c nP p : ℕ} (X : Catalyst.Approximation F c nP) (R h k tail gain drift degree f quota base field wire hist H : ℕ)
    (positive : 0<H) (lo : S.hostSize 0≤H) (hi : H≤hostRows (S.hostSize 0)) :
    let l:=selectedLayout G S h k tail gain p drift degree f quota base field wire hist
    Population S (initial G op X R l k H (S.groupCount 0) h (S.grainAt G.b p 0)) 0 :=
  ⟨rfl,lo,hi,positive,le_rfl⟩

private theorem found_lt (target t j : ℕ) (hit : OrdinaryLink.roundFor target t=some j) : j<t:=by
  induction t with
  | zero => simp [OrdinaryLink.roundFor] at hit
  | succ t ih =>
    unfold OrdinaryLink.roundFor at hit
    split at hit
    · simp only [Option.some.injEq] at hit;omega
    · exact (ih hit).trans (Nat.lt_succ_self _)

theorem public_slot_room {t : ℕ} (active : 0<t) (reset branch fee : ℕ) :
    4*DescentOrdinaryVenueReturn.shapeSlots (OrdinaryLink.publicDegree t branch fee) ≤ 2^hostRate t reset :=by
  unfold OrdinaryLink.publicDegree
  cases hit:OrdinaryLink.roundFor (degreeClass branch fee) t with
  | none =>
    have small : DescentOrdinaryVenueReturn.shapeSlots 0≤DescentOrdinaryVenueReturn.shapeSlots (atRound 0):=by
      exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
        (by decide : packExponent 20 0≤packExponent 20 3)) _
    exact (Nat.mul_le_mul_left 4 small).trans (OrdinaryBooks.round_slots reset active)
  | some j => exact OrdinaryBooks.round_slots reset (found_lt _ _ j hit)

section Ordinary
variable {P : Type} {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (gain tail p f drift degree h seats root : ℕ) (ordinary : ℕ→Dated.Ordinary)
theorem ordinary_population {t reset J M : ℕ} (scheduled : S=stageNumbers G t J f gain reset M tail)
    (live : 0<S.hostSize i) (radix : S.radix=2^k) :
    let out:=ordinaryPorts prior ticket op gain tail p f drift degree h seats root ordinary
    Population S out (i+1) ∧ out.venue.hosts=NativePitch.incomingHosts S (i+1) :=by
  intro out
  have timed:=ticket.hubRows.choose
  have tPos : 0<t:=by
    have h₀:=ticket.degreeSlot
    obtain ⟨j,jt,_⟩:=h₀
    rw [scheduled] at jt
    exact (Nat.zero_le _).trans_lt jt
  let date:=DonorDate.atDate G S gain k i p
  have bound : 4*DescentOrdinaryVenueReturn.shapeSlots date.degree≤2^S.hostGain:=by
    change 4*DescentOrdinaryVenueReturn.shapeSlots (OrdinaryLink.publicDegree S.rounds G.b _)≤2^S.hostGain
    rw [scheduled]
    exact public_slot_room tPos reset G.b _
  have room:=OrdinaryBooks.compact_host_room S live timed radix bound
  have hosts:=NativePitch.hosts_bounds S (i+1) timed
  have low : 0<((2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots date.degree):=by
    have big : 2≤2^(k+1):=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 1≤k+1 by omega)
    have positive : 0 < 2^(k+1)-1 := by omega
    exact Nat.mul_pos positive (Nat.zero_lt_succ _)
  exact ⟨⟨rfl,hosts.1,hosts.2,Nat.mul_pos (Nat.two_pow_pos _) low,room⟩,rfl⟩

end Ordinary

section Reset
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (oldOperand oldPrimitive : ℕ) (old : StageVenueTail.Date)
    (wire : ℕ→ℕ→Bank) (roster : Bank) (floor : ℕ)
local notation "tag" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "a" => PhysicalReset.scheduled G S board k tail age p f g drift degree h ordinary op
  (S.firstWidth G.b p) (S.grainAt G.b p 0) oldOperand oldPrimitive old wire roster floor


theorem reset_population {w : ℕ} (inputs : (a).DateInputs ((a).stageStart floor) w) (hi : 0<S.hostSize (age+1)) :
    let out:=reset (a) ((a).stageStart floor) inputs
    Population S out (age+1) ∧ out.venue.hosts=S.hostSize (age+1) :=
  ⟨⟨rfl,le_rfl,hostPad _,hi,le_rfl⟩,rfl⟩

end Reset
end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
