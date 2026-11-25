import OAI.Hierarchy.DescentRotorWindowScore
import OAI.Hierarchy.DescentSignedChartAddress

namespace OAI
/-! # Recovering the physical good bases and signed fields from compact old-window entries -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentResetAttachments DescentRelativeContacts DescentFallbackShapeTable DescentCanonicalPorts
open DescentRotorWindowScore DescentPackedTicketChronology DescentSIMDLookup DescentPacking
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "use" => useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "wireWord" => peerShapeWord A S ready digits Z T frm

theorem rotorCode (p : {e : E // use e}) (s : Bool) :
    T.code (T.home (endAt s p.val))=goodAddress (R).b (R).keys (R).hub
      (headAt p s,(R).row s ((R).old s p.val)) := by
  have ident : endAt s p.val=ends (Wold).graph s p.val:=by cases s <;> rfl
  exact (congrArg T.code ((congrArg T.home ident).trans (T.attach s p.val))).trans (T.source s p.val p.property)

/-- The high-coordinate receipt is common to all wires in one source window.
The short encoded interval retains the relative low digits and omits the row. -/
theorem rotorInterval (p : {e : E // use e}) (s : Bool) :
    DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s p.val)))=
      (Z.goodLabel T (headAt p s)).val.1*2^r+(Z.goodLabel T (headAt p s)).val.2 := by
  let z:=shortName c (T.code (T.home (endAt s p.val)))
  have shape : (chartShape A S ready Z T (fallbackCell A S ready digits Z T frm s (home A (endAt s p.val)))).val=
      cell r z.2 :=
    congrArg (fun t => (chartShape A S ready Z T t).val) (cell_home A S ready digits Z T frm s p.val)
  have bit (v : Bool) : (2*(cell r z.2)+v.toNat)/2=cell r z.2 := by
    cases v <;> simp [Bool.toNat]
    all_goals omega
  have unpack : cell r z.2 / (2^Z.n+1) = z.2.1.1*2^r+z.2.1.2 := by
    unfold cell
    rw [Nat.mul_comm (z.2.1.1*2^r+z.2.1.2),Nat.mul_add_div (Nat.zero_lt_succ _),
      Nat.div_eq_of_lt (option_fit _),Nat.add_zero]
  simp only [DescentRotorWindowScore.interval,peerShapeWord,shape,bit,unpack]
  dsimp only [z]
  rw [rotorCode A S ready Z T]
  rfl

theorem rotorHigh (p : {e : E // use e}) (s : Bool) :
    coarse (m:=c) (R).b (headAt p s).val=
      group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt s p.val))) := by
  exact (congrArg (coarseName c) (rotorCode A S ready Z T p s)).symm.trans (frm.homeHigh (endAt s p.val))

theorem rotorHost (p : {e : E // use e}) (s : Bool) :
    (headAt p s).val.1=frm.host (A.pos (endAt s p.val)).2 := by
  exact (congrArg Prod.fst (rotorCode A S ready Z T p s)).symm.trans (frm.homeHost (endAt s p.val))

theorem rotorInterval_eq (p t : {e : E // use e}) (s : Bool)
    (sameGroup : group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt s p.val)))=
      group c (rearrange frm.basis (StarKeys.filled W.graph A.pos A.block digits (endAt s t.val)))) :
    headAt p s=headAt t s ↔
      (A.pos (endAt s p.val)).2=(A.pos (endAt s t.val)).2 ∧
      DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s p.val)))=
      DescentRotorWindowScore.interval Z.n (wireWord s (home A (endAt s t.val))) := by
  rw [rotorInterval,rotorInterval]
  have h₁:=rotorHost A S ready digits Z T frm p s
  have h₂:=rotorHost A S ready digits Z T frm t s
  constructor
  · intro eqn
    rw [eqn] at h₁ ⊢
    exact ⟨frm.host.injective (h₁.symm.trans h₂),rfl⟩
  · rintro ⟨hv,words⟩
    have rem (z : (R).Good) : (Z.goodLabel T z).val.2<2^r :=
      (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right ((R).depth _) c))
    have low:=congrArg (fun z=>z%2^r) words
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (rem _)] at low
    apply Subtype.ext
    apply recover (m:=c) (R).b
    · rwa [rotorHigh A S ready digits Z T frm,rotorHigh A S ready digits Z T frm]
    · exact Prod.ext (h₁.trans ((congrArg frm.host hv).trans h₂.symm)) low

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
