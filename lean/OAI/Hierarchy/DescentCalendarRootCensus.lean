import OAI.Hierarchy.DescentCalendarPrimarySpans
import OAI.Hierarchy.DescentScheduledPrimaryCensus

namespace OAI
/-! # Previous node census on arbitrary physical GL rows of the scheduled receiver -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput DescentKernelHistory
open DescentCompiler DescentColonies DescentGL DescentResetLocalNodes DescentOrdinaryAtomFieldRAM
open DescentPaidResidentCount.Reset DescentLocalArchiveOrder DescentSIMDLookup DescentIssuedFallbackPanel
open DescentPlainTerminal DescentChosenRouter DescentFallbackShapeTable DescentRelativeContacts
open DescentRetainedControl DescentResetHostSize Reached.NodeCells
open DescentRetainedRangeDigits
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentSixParty.PackedFlow.Channels
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (a : Archive W) (early : Local a.bit)
local notation "A" => cap.placement
local notation "T" => b.terminals
local notation "dim" => (T).commonDepth
local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation:max "ix" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation "small" => b.frame.enough.trans (Nat.sub_le ..)
local notation:max "Node" u:arg => (a.bit.recipe u).Node
variable (chart : DescentResetOperandSetup.Chart)
local notation "rootLayout" => chart.retained
variable (total:(rootLayout).high+(rootLayout).low=wide) (axis:(rootLayout).cut=dim)
  (blocks:(rootLayout).blocks=2^k) (groups:(rootLayout).groups=S.groupCount i)
  (size:2^((rootLayout).high+(rootLayout).low)=(rootLayout).groups*(rootLayout).blocks) (fits:(rootLayout).cut≤(rootLayout).high+(rootLayout).low)
  (L:DescentGL.Layout ((rootLayout).high+(rootLayout).low)) (won:HEq L b.frame.basis)
  (room:Fintype.card cap.V≤(rootLayout).hosts)
   (nodeRoom:∀u,Fintype.card (Node u)≤(rootLayout).previousNodes)
local notation "hl" => congrArg (fun k:ℕ=>2^k) axis
local notation "ll" => congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total axis)
local notation "coords" => finCongr ll
local notation "hostName" => cap.vertex.trans (Fin.castLEEmb room)
variable (prev : cap.V) (hi:Block dim)
local notation "carrier" => hostName prev
local notation "coarse" => hi.cast (hl).symm
local notation:max "source" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation:max "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (rootLayout).groups×Fin (rootLayout).blocks)
local notation:max "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=prev ∧ ix u=source lo then Fintype.card (Node u) else 0
variable (input : (rootLayout).Values)
local notation "strips" => (fun j=>blockValues fits ((rootLayout).before size input j) L)
local notation "wrd" => (rootLayout).site strips carrier coarse
open DescentDatedAddressBook.PhysicalReset
variable (counts: OriginalRootCounts (input:=cap) (oldA:=a) (rootLayout) input size fits L room groups blocks)

include won counts in
theorem calendar_row_census (lo:Block (wide-dim)) : (rootLayout).originalCount wrd ((coords).symm lo)=census lo:=by
  classical
  refine (counts carrier coarse ((coords).symm lo)).trans ?_
  apply Finset.sum_congr rfl
  intro u _
  have highEq:(coarse).cast hl=hi:=Fin.ext rfl
  have lowEq:((coords).symm lo).cast ll=lo:=Fin.ext rfl
  have here:((pos lo).1.cast groups,(pos lo).2.cast blocks)=digits (source lo):=by
    simpa only [highEq,lowEq] using
      moved_position S ctl.base ctl.radix total groups blocks size fits L axis b.frame.basis won small coarse ((coords).symm lo)
  have eqn : DescentPaidResidentCount.occupies (A) (Equiv.refl _) hostName carrier
      ((pos lo).1.cast groups) ((pos lo).2.cast blocks) u ↔ ((A).pos u).2=prev ∧ ix u=source lo:=by
    constructor
    · rintro ⟨hostEq,groupEq,blockEq⟩
      refine ⟨(hostName).injective hostEq,?_⟩
      apply (digits).injective
      simpa only [StarKeys.filled,Equiv.apply_symm_apply] using (Prod.ext groupEq blockEq).trans here
    · rintro ⟨hostEq,addr⟩
      have where_:=((congrArg digits addr).trans here.symm)
      simp only [StarKeys.filled,Equiv.apply_symm_apply] at where_
      exact ⟨congrArg hostName hostEq,congrArg Prod.fst where_,congrArg Prod.snd where_⟩
  by_cases live : DescentPaidResidentCount.occupies A (Equiv.refl _) hostName carrier
      ((pos lo).1.cast groups) ((pos lo).2.cast blocks) u
  · simp only [ite_eq_left live,ite_eq_left (eqn.mp live)]
  · simp only [ite_eq_right live,ite_eq_right (fun yes => live (eqn.mpr yes))]

end
end Hierarchy.DescentPrimitivePalette

end OAI
