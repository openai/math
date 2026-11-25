import OAI.Hierarchy.DescentResetCoarseGroups
import OAI.Hierarchy.DescentCanonicalFallback
import OAI.Hierarchy.DescentGoodPortCoherence
import OAI.Hierarchy.DescentOldTerminalFan
import OAI.Hierarchy.DescentInstalledEpoch

namespace OAI
/-! # Re-enter the reset through its actual grouped old terminal tables -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty DescentChosenRouter DescentMixedRouter DescentRouterBank DescentResetAttachments Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F H P Q : Type} [Field F] [Fintype H] [Fintype Q] {d n : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)

def install {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (S : R.Tables F) : MarkedWorld F d P bits := by
  subst w
  exact world A home group R S hub

omit [Fintype Q] in
theorem read_install {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (S : R.Tables F) (bank : ∀p,R.value S p=if publicRows group w p false=publicRows group w p true then 1 else 0)
    (ordinary : ∀e∈A.core,hub (home (A.graph.src e))=false ∧ hub (home (A.graph.dst e))=false)
    (outside : ∀e∉A.core,hub (home (A.graph.src e))≠hub (home (A.graph.dst e))) :
    let out := install A home group hub same R S
    let old := DescentResetAttachments.mount A (hub ∘ home) group same R S
    (∀x,out.value x=A.value x) ∧ out.tetherWidth=A.tetherWidth ∧
      out.liveWidth=old.liveWidth+A.liveWidth+A.tetherWidth := by
  subst w
  refine ⟨world_value A home group R S hub bank,tether A home group R S hub ordinary outside,?_⟩
  rw [show (install A home group hub rfl R S).liveWidth=(∑e,R.width e)+3*A.liveWidth+2*A.tetherWidth from
    live A home group R S hub ordinary outside]
  let old := resetWorld A group R S (hub ∘ home)
  have ht : old.tetherWidth=A.tetherWidth := reset_tether A group R S _ ordinary outside
  have full := Finset.sum_add_sum_compl old.core old.graph.width
  change old.liveWidth+old.tetherWidth=∑e,(DescentResetAttachments.network A.graph group R).width e at full
  rw [ht,DescentResetAttachments.total_width] at full
  have orig := Finset.sum_add_sum_compl A.core A.graph.width
  change A.liveWidth+A.tetherWidth=_ at orig
  change _=old.liveWidth+A.liveWidth+A.tetherWidth
  omega

theorem installed_neighbors {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (S : R.Tables F) (role : A.graph.Edge→Bool)
    (recv : ∀s e j,group s e=group s j→home (ends A.graph s e)=home (ends A.graph s j))
    (send : ∀s e j,home (ends A.graph s e)=home (ends A.graph s j)→ role e=role j → group s e=group s j)
    (bound : ∀v,R.bitDegree v≤3) :
    let out := install A home group hub same R S
    ∃near : out.graph.Site→Finset out.graph.Site,(∀v,(near v).card≤3) ∧
      ∀e,out.graph.dst e∈near (out.graph.src e) ∧ out.graph.src e∈near (out.graph.dst e) := by
  subst w
  exact ⟨near A.graph home group R role,degree A.graph home group R role bound,
    adjacent A.graph home group R role recv send⟩

omit [Fintype Q] in
theorem installed_divides {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
    (S : R.Tables F) (u : ℕ) (oldWidth : ∀e,u∣w e) (deviceWidth : ∀e,u∣R.width e) :
    ∀e,u∣(install A home group hub same R S).graph.width e := by
  subst w
  exact preserves_quantum A home group R S hub u oldWidth deviceWidth

end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentResetAttachments DescentRotor DescentContacts DescentResetTrunks
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits} {price ε : ℝ} {h C Ht : ℕ}
variable (Z : ResetInput A price ε h C Ht)
local notation "R" => Z.placement

/-- Common physical terminal names retained with the selected rotor receipt. -/
structure Terminals where
  home : A.graph.Site→Z.Fallback
  hub : Z.Fallback→Bool
  commonDepth : ℕ
  joined : (R).CommonOutputs commonDepth
  columns : (R).ColumnRoster commonDepth
  tag : ∀v,hub (home v)=Z.hub v
  attach : ∀s i,home (ends A.graph s i)=(R).fall s ((R).old s i)
  code : Z.Fallback↪Z.V×Endpoint (2^Z.n)
  hubShape : ∀t,hub t=true ↔ (code t).2.2=none
  hubCover : ∀t,hub t=true→∀c : DescentColonies.Block commonDepth,∃z,hub z=true ∧
    coarseName commonDepth (code z)=c.val ∧
    DescentRelativeContacts.shortName commonDepth (code z)=DescentRelativeContacts.shortName commonDepth (code t)
  commonLow : ∀v,commonDepth≤(R).b v
  codeLegal : ∀t,commonDepth≤(code t).2.1.1 ∧ (code t).2.1.1≤Z.k ∧ (code t).2.1.2<2^(code t).2.1.1
  bookHeight : ∀s t,((R).fallbackBook s t).height≤Ht
  coarseLinks : (R).CommonGroups commonDepth code
  fallbackCoherent : (R).CommonFallback (fun t=>DescentRelativeContacts.shortName commonDepth (code t))
  leaves : (R).LeafRoster columns.host (fun t=>DescentRelativeContacts.shortName commonDepth (code t))
  source : ∀s i (m : useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old i),
    code ((R).fall s ((R).old s i))=goodAddress (R).b (R).keys (R).hub
        (base (R).b (R).depth (R).L (R).keys (R).hub (R).old ⟨i,m⟩ s,(R).row s ((R).old s i))

variable (T : Terminals Z)
def reenter := DescentResetTrunks.install A T.home (R).input T.hub (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables
local notation "W" => reenter Z T

theorem read_reentry (hp : 0≤price) (he : 0≤ε) :
    (∀x,(W).value x=A.value x) ∧ (W).tetherWidth=A.tetherWidth ∧
      (W).liveWidth=(Z.world hp he).liveWidth+A.liveWidth+A.tetherWidth := by
  have sameHub : T.hub ∘ T.home=Z.hub := funext T.tag
  simpa only [world,reenter,sameHub] using read_install A T.home (R).input T.hub (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables
    (DescentMixedRouter.value (K:=F) (C₀:=C) Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align
      (selected R Z.graph Z.positive Z.pay Z.circuit)) (by simpa only [T.tag] using Z.inside)
    (by simpa only [T.tag] using Z.outside)

theorem reentry_neighbors :
    ∃near : (W).graph.Site→Finset (W).graph.Site,(∀v,(near v).card≤3) ∧
      ∀e,(W).graph.dst e∈near ((W).graph.src e) ∧ (W).graph.src e∈near ((W).graph.dst e) := by
  apply installed_neighbors A T.home (R).input T.hub (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables (mode R)
  · intro s e j eq
    simpa only [T.attach] using shared_receive R T.code T.source s e j eq
  · intro s e j eq me
    exact shared_send R T.code T.source s e j (by simpa only [T.attach] using eq) me
  · exact DescentMixedRouter.degree (K:=F) (C₀:=C) Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align
      (selected R Z.graph Z.positive Z.pay Z.circuit)

theorem reentry_divides (e : (W).graph.Edge) : Z.unit∣(W).graph.width e :=
  installed_divides A T.home (R).input T.hub (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables Z.unit (fun _=>dvd_refl _)
    (DescentMixedRouter.quantum (K:=F) (C₀:=C) Z.graph Z.positive Z.unit (R).contact (R).input (R).site (R).owner (R).align
      (selected R Z.graph Z.positive Z.pay Z.circuit)) e

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
