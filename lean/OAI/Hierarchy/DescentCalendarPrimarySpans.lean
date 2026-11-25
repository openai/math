import OAI.Hierarchy.DescentDecodedEmptyPrimary
import OAI.Hierarchy.DescentRetainedOriginalDigits
import OAI.Hierarchy.DescentPrimaryOriginalRange
import OAI.Hierarchy.DescentResetOriginRangeShape
import OAI.Hierarchy.DescentScheduledDonorCensus
import OAI.Hierarchy.DescentPrimaryTokenCoordinates
import OAI.Hierarchy.DescentRecordedStencilCell

namespace OAI
/-! # Retained range fields at the node number of the actual reset origin -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput DescentKernelHistory
open DescentCompiler DescentColonies DescentGL DescentResetLocalNodes DescentOrdinaryAtomFieldRAM
open DescentPaidResidentCount.Reset DescentLocalArchiveOrder DescentSIMDLookup DescentIssuedFallbackPanel
open DescentPlainTerminal DescentChosenRouter DescentFallbackShapeTable DescentRelativeContacts
open DescentRetainedControl DescentResetHostSize Reached.NodeCells
open DescentRetainedRangeDigits DescentSixParty.PackedFlow.Channels
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (a : Archive W) (early : Local a.bit)
local notation "A" => cap.placement
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "dim" => (T).commonDepth
local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation:max "ix" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation "oldId" => (A).site cap.vertex cap.valid.coordinates
local notation "small" => b.frame.enough.trans (Nat.sub_le ..)
local notation "roster" => ClosedReset.Recorded.old_roster (reset:=b)
local notation "safe" => (roster).2.2.2.2.2.choose
local notation:max "Node" u:arg => (a.bit.recipe u).Node
variable (chart : DescentResetOperandSetup.Chart)
local notation "ret" => chart.retained
variable (total:(ret).high+(ret).low=wide) (axis:(ret).cut=dim)
  (blocks:(ret).blocks=2^k) (groups:(ret).groups=S.groupCount i)
  (size:2^((ret).high+(ret).low)=(ret).groups*(ret).blocks) (fits:(ret).cut≤(ret).high+(ret).low)
  (L:DescentGL.Layout ((ret).high+(ret).low)) (won:HEq L b.frame.basis)
  (room:Fintype.card cap.V≤(ret).hosts)
   (nodeRoom:∀u,Fintype.card (Node u)≤(ret).previousNodes)
local notation "hl" => congrArg (fun k:ℕ=>2^k) axis
local notation "ll" => congrArg (fun k:ℕ=>2^k) (congrArg₂ Nat.sub total axis)
local notation "coords" => finCongr ll
local notation "hostName" => cap.vertex.trans (Fin.castLEEmb room)
variable (t : (Z).Fallback)
local notation "u₀" => b.frame.host.symm ((T).code t).1
local notation "carrier" => hostName u₀
local notation "hi" => (Z).rootBlock T (.inr t)
local notation "coarse" => (hi).cast (hl).symm
local notation:max "source" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation:max "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (ret).groups×Fin (ret).blocks)
local notation:max "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=u₀ ∧ ix u=source lo then Fintype.card (Node u) else 0

variable (hp : 0<p) (whole : p∣(Z).unit)
local notation "after_" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "order_" => DescentLocalArchiveOrder.reset b p hp whole a early
variable (which : chart.seven.control.Targets) (window : chart.seven.Packets) (shape : Fin chart.placement.shapes)
variable (input : (ret).Values)
local notation "strips" => (fun j=>blockValues fits ((ret).before size input j) L)
local notation "wrd" => (ret).site strips carrier coarse
variable (word : Block (wide-dim)→ℕ)
local notation "code" => cell ((Z).k-dim) (shortName dim ((T).code t)).2
variable (owns : ownerAt chart which window shape carrier coarse=(fun i=>decide (word (coords i)/2=code)))
variable (compared : priorAt chart window carrier coarse=(fun i j=>decide (source (coords i)<source (coords j))))
variable (stencil : ∀lo,word lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode (wide-dim)
  (2^(Z).n) (DescentPlainTerminal.Suffix.fieldsRelative dim (ClosedReset.Recorded.originalCell (reset:=b) u₀ (source lo))))
variable (counts : ∀lo,(ret).originalCount wrd ((coords).symm lo)=∑u:W.graph.Site,
    if DescentPaidResidentCount.occupies (A) (Equiv.refl _) hostName carrier ((pos lo).1.cast groups)
      ((pos lo).2.cast blocks) u then Fintype.card (Node u) else 0)

include won in
private theorem original_coordinates (lo : Block (wide-dim)) :
    ((pos lo).1.cast groups,(pos lo).2.cast blocks)=digits (source lo):=by
  have highEq:(coarse).cast hl=hi:=Fin.ext rfl
  have lowEq:((coords).symm lo).cast ll=lo:=Fin.ext rfl
  simpa only [highEq,lowEq] using
    moved_position S ctl.base ctl.radix total groups blocks size fits L axis b.frame.basis won small coarse ((coords).symm lo)

include won groups blocks in
/-- The row gathered for each actual donor has that donor's original host, group and block. -/
theorem calendar_donor_place (u : DescentNamedContact.Fibre (T).home t) :
    let lo:=low («c»:=dim) (rearrange b.frame.basis (ix u.val))
    (carrier).val=(Reached.NodeCells.coordinate cap u.val).1.val ∧
    (pos lo).1.val=(Reached.NodeCells.coordinate cap u.val).2.1.val ∧
    (pos lo).2.val=(Reached.NodeCells.coordinate cap u.val).2.2.val :=by
  intro lo
  have atHost:=b.frame.homeHost u.val
  rw [u.property] at atHost
  have nativeHost : u₀=((A).pos u.val).2 :=by
    apply b.frame.host.injective
    simpa only [Equiv.apply_symm_apply] using atHost
  have nativeDigit:=original_coordinates b chart total axis blocks groups size fits L won t lo
  have original : ix u.val=source lo:=old_home_digit b.frame t u
  rw [←original] at nativeDigit
  simp only [StarKeys.filled,Equiv.apply_symm_apply] at nativeDigit
  refine ⟨?_,congrArg (fun p=>(Prod.fst p).val) nativeDigit,congrArg (fun p=>(Prod.snd p).val) nativeDigit⟩
  change (cap.vertex u₀).val=(cap.vertex ((A).pos u.val).2).val
  rw [nativeHost]

include won counts in
private theorem original_census (lo : Block (wide-dim)) : (ret).originalCount wrd ((coords).symm lo)=census lo:=by
  classical
  rw [counts]
  apply Finset.sum_congr rfl
  intro u _
  have here:=original_coordinates b chart total axis blocks groups size fits L won t lo
  have eqn : DescentPaidResidentCount.occupies (A) (Equiv.refl _) hostName carrier
      ((pos lo).1.cast groups) ((pos lo).2.cast blocks) u ↔ ((A).pos u).2=u₀ ∧ ix u=source lo:=by
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

include won owns stencil counts in
theorem calendar_primary_original (d₀ : Fin (ret).donors) (n₀ : Fin (ret).previousNodes)
    (active : ownerAt chart which window shape carrier coarse d₀=true)
    (occupied : n₀.val<(ret).originalCount wrd d₀) :
    ∃u : DescentNamedContact.Fibre (T).home t,∃z : Node u.val,
      ((A).pos u.val).2=u₀ ∧ ix u.val=source (coords d₀) ∧ (early u.val z).val=n₀.val :=by
  let _ : ∀ u : (W.granular b.count (z*G.b) b.fit).graph.Site, Fintype (a.bit.recipe u).Node := fun u => inferInstance
  exact primary_donor_original b.frame _ _ _ _ _ _ _ _ _ _ roster _ word stencil chart coords shape _ _
    which window strips owns oldId (GroupStage.scheduled_site_order S A ctl.base ctl.radix cap.vertex cap.valid.coordinates)
    (fun u=>Node u) early (original_census b a chart total axis blocks groups size fits L won room _ input counts)
    d₀ n₀ active occupied

include won nodeRoom owns compared stencil counts in
theorem calendar_primary_donor (x : NodeOrder.All after_) (y : NodeOrder.All a.bit)
    (retained : names x=Sum.inl y) (home : (T).home y.1=t)
    (nextRoom : Fintype.card ((after_).recipe x.1).Node≤(ret).nodes) :
    let oldNode:=(early y.1 y.2).castLE (nodeRoom y.1)
    let nextNode:=(order_ x.1 x.2).castLE nextRoom
    let d:=(coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix y.1)))
    let order:=physicalDonorOrder b.frame t ret coords
    ownerAt chart which window shape carrier coarse d=true ∧
      oldNode.val<(ret).originalCount wrd d ∧
      nextNode.val=(ret).offset ((ret).routedWord (ownerAt chart which window shape carrier coarse)
        (priorAt chart window carrier coarse) wrd) (order d)+oldNode.val ∧
      ∀i,neighbors (priorAt chart window carrier coarse) i=(order i).val :=by
  let _ : ∀ u : (W.granular b.count (z*G.b) b.fit).graph.Site, Fintype (a.bit.recipe u).Node := fun u => inferInstance
  subst t
  intro oldNode nextNode d order
  have numeric:=retained_local_ordinal b hp whole a early x y retained
  exact primary_donor_receipt b.frame _ _ _ _ _ _ _ _ _ _ roster _ word stencil chart coords shape _ _
    which window strips owns compared oldId (GroupStage.scheduled_site_order S A ctl.base ctl.radix cap.vertex cap.valid.coordinates)
    (fun u=>Node u) early (original_census b a chart total axis blocks groups size fits L won room _ input counts)
    ⟨y.1,rfl⟩ y.2 oldNode rfl nextNode numeric


include won nodeRoom owns compared stencil counts in
theorem calendar_primary_spans (x : NodeOrder.All after_) (y : NodeOrder.All a.bit)
    (retained : names x=Sum.inl y) (home : (T).home y.1=t)
    (nextRoom : Fintype.card ((after_).recipe x.1).Node≤(ret).nodes) :
    let oldNode:=(early y.1 y.2).castLE (nodeRoom y.1)
    let nextNode:=(order_ x.1 x.2).castLE nextRoom
    let d:=(coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix y.1)))
    (∀(arg : Fin (ret).args) (j : Fin (ret).previousArgs) (f₀ : Fin 3),arg.val=j.val →
       j.val<((ret).entry wrd d oldNode (ret).arityField).val →
       chart.seven.decoded which window strips ((ret).outputID 1 (page f₀) arg nextNode) shape carrier coarse=
         (ret).entry wrd d oldNode ((ret).operandField (page f₀) j)) ∧
    (∀(arg : Fin (ret).args) (f₀ : Fin 3),((ret).entry wrd d oldNode (ret).arityField).val≤arg.val →
       chart.seven.decoded which window strips ((ret).outputID 1 (page f₀) arg nextNode) shape carrier coarse=0) :=by
  let _ : ∀ u : (W.granular b.count (z*G.b) b.fit).graph.Site, Fintype (a.bit.recipe u).Node := fun u => inferInstance
  subst t
  intro oldNode nextNode d
  have numeric:=retained_local_ordinal b hp whole a early x y retained
  exact primary_seven_spans b.frame _ _ _ _ _ _ _ _ _ _ roster _ word stencil chart coords shape _ _
    which window strips owns compared oldId (GroupStage.scheduled_site_order S A ctl.base ctl.radix cap.vertex cap.valid.coordinates)
    (fun u=>Node u) early (original_census b a chart total axis blocks groups size fits L won room _ input counts)
    ⟨y.1,rfl⟩ y.2 oldNode rfl nextNode numeric

private theorem reindex_donor_totals {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (tag : β → ℕ) (value : α → ℕ) (target : ℕ) :
    (∑ d, if decide (tag (e d) = target) = true then value d else 0) =
      ∑ lo, if tag lo = target then value (e.symm lo) else 0 := by
  rw [← e.sum_comp (fun lo => if tag lo = target then value (e.symm lo) else 0)]
  simp only [decide_eq_true_eq, Equiv.symm_apply_apply]

include won owns compared stencil counts in
/-- Unoccupied scalar slots beyond the complete original node census include nullary
and unpaid predecessors in their cutoff. Every native range column vanishes there. -/
theorem calendar_empty_primary (slot : Fin (ret).nodes)
    (absent : (∑u:DescentNamedContact.Fibre (T).home t,Fintype.card (Node u.val))≤ slot.val)
    (operand : Fin (ret).args) (f₀ : Fin 3) :
    chart.seven.decoded which window strips ((ret).outputID 1 (page f₀) operand slot) shape carrier coarse=0:=by
  let order:=physicalDonorOrder b.frame t (ret) (coords)
  have cmp i j : priorAt chart window carrier coarse i j=decide ((order i).val<(order j).val):=by
    rw [compared]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (physicalDonorOrder_lt b.frame t ret coords i j).symm
  apply decoded_empty chart which window strips shape carrier coarse order ((ret).original_rank _ order cmp)
    slot _ operand f₀
  rw [owns]
  apply le_trans _ absent
  have together:=window_sum b.frame _ _ _ _ _ _ _ _ _ _ roster t word stencil id (fun u=>Fintype.card (Node u))
    (fun lo=>(ret).originalCount wrd ((coords).symm lo)) (original_census b a chart total axis blocks groups size fits L won room t input counts)
  exact ((reindex_donor_totals coords (fun lo => word lo / 2) ((ret).originalCount wrd) code).trans together).le

end
end Hierarchy.DescentPrimitivePalette

end OAI
