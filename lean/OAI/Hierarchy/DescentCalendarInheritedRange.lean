import OAI.Hierarchy.DescentCalendarPrimarySpans
import OAI.Hierarchy.DescentRetainedResetRangeOrigin
import OAI.Hierarchy.DescentCalendarPrimaryDonorWords

namespace OAI
/-! # The inherited three range fields on the true returned primary shelf -/
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
variable {R:ℕ} (hp : 0<p) (whole : p∣(Z).unit) (one:1≤R) (posUnit:0<(Z).unit)
  (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (sh:DescentBundleHistory.WorldShape p R a.bit)
local notation "nextBit" => (resetArchive b p hp whole a).bit
variable (xx : NodeOrder.All nextBit) (yy : NodeOrder.All a.bit)
  (origin : resetOrigin b hp whole a xx=Sum.inl yy)
local notation "term" => (T).home yy.1
local notation "u₀" => b.frame.host.symm ((T).code term).1
local notation "carrier" => hostName u₀
local notation "hi" => (Z).rootBlock T (.inr term)
local notation "coarse" => (hi).cast (hl).symm
local notation:max "origAddr" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation:max "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation:max "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (ret).groups×Fin (ret).blocks)
local notation:max "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=u₀ ∧ ix u=origAddr lo then Fintype.card (Node u) else 0

local notation "after_" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "order_" => DescentLocalArchiveOrder.reset b p hp whole a early
variable (which : chart.seven.control.Targets) (window : chart.seven.Packets) (shape : Fin chart.placement.shapes)
variable (input : (ret).Values)
local notation "strips" => (fun j=>blockValues fits ((ret).before size input j) L)
local notation "wrd" => (ret).site strips carrier coarse
variable (word : Block (wide-dim)→ℕ)
local notation "code" => cell ((Z).k-dim) (shortName dim ((T).code term)).2
variable (owns : ownerAt chart which window shape carrier coarse=(fun i=>decide (word (coords i)/2=code)))
variable (compared : priorAt chart window carrier coarse=(fun i j=>decide (origAddr (coords i)<origAddr (coords j))))
variable (stencil : ∀lo,word lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode (wide-dim)
  (2^(Z).n) (DescentPlainTerminal.Suffix.fieldsRelative dim (ClosedReset.Recorded.originalCell (reset:=b) u₀ (origAddr lo))))
variable (counts : ∀lo,(ret).originalCount wrd ((coords).symm lo)=∑u:W.graph.Site,
    if DescentPaidResidentCount.occupies (A) (Equiv.refl _) hostName carrier ((pos lo).1.cast groups)
      ((pos lo).2.cast blocks) u then Fintype.card (Node u) else 0)


open DescentBundleHistory DescentSixParty.ClosedReset DescentRetainedRangeDigits
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ posUnit) (b.unit ▸ whole)
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals (DescentOrderedReset.grains W b.count b.order)
  _ hp fit_ (resetMenu b) one widthBound
local notation "sh₁" => WorldShape.follow hp posUnit whole b.reblock b.cuts installed

local notation "old" => sh.sites yy.1
local notation "new" => (sh₁).sites xx.1
local notation "arity_" => ((old).recipe hp).arity yy.2
local notation "d₀" => (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix yy.1)))
local notation "last_" => (early yy.1 yy.2).castLE (nodeRoom yy.1)
variable (nextRoom : Fintype.card ((after_).recipe xx.1).Node≤(ret).nodes)
local notation "current_" => (order_ xx.1 xx.2).castLE nextRoom
local notation:max "observed" arg:arg f₀:arg => chart.seven.decoded which window strips ((ret).outputID 1 (page f₀) arg current_) shape carrier coarse
local notation:max "prior_" j:arg f₀:arg => ((ret).entry wrd d₀ last_ ((ret).operandField (page f₀) j)).val

include origin in
private theorem inherited_occurrences : occurrences new xx.2=occurrences old yy.2 :=by
  have shape:=reset_range_origin b hp whole a sh one posUnit widthBound xx
  rw [origin] at shape
  change (new).sliceFields xx.2=(old).sliceFields yy.2 at shape
  exact (DescentRetainedRangeDigits.layout new xx.2).symm.trans
    ((congrArg (fun slices : List (List SliceCode) => DescentTerminalSliceRuns.repeatFields slices.flatten) shape).trans
      (DescentRetainedRangeDigits.layout old yy.2))

include won nodeRoom owns compared stencil counts origin in
/-- Installed old operand fields are decoded on the exact elected old owner, in its real
new scalar ordinal. This includes count padding and the zero result at every absent argument. -/
theorem calendar_inherited_range (arg : Fin (ret).args) (f₀ : Fin 3)
    (fitsArgs : arity_≤(ret).previousArgs)
    (arityRead : ((ret).entry wrd d₀ last_ (ret).arityField).val=arity_)
    (original : ∀j : Fin (ret).previousArgs,j.val=arg.val → j.val<arity_ →
      prior_ j f₀=atSlot old yy.2 j.val f₀) :
    (observed arg f₀).val=atSlot new xx.2 arg.val f₀ :=by
  have inherited:=inherited_occurrences (b:=b) (a:=a) (hp:=hp) (whole:=whole) (one:=one)
    (posUnit:=posUnit) (widthBound:=widthBound) (sh:=sh) (xx:=xx) (yy:=yy) (origin:=origin)
  have laid:=calendar_primary_spans (b:=b) (a:=a) (early:=early) («chart»:=chart) (total:=total)
    (axis:=axis) (blocks:=blocks) (groups:=groups) (size:=size) (fits:=fits) (L:=L) (won:=won)
    (room:=room) (nodeRoom:=nodeRoom) (t:=term) (hp:=hp) (whole:=whole) (which:=which) (window:=window)
    (shape:=shape) (input:=input) (word:=word) (owns:=owns) (compared:=compared) (stencil:=stencil)
    (counts:=counts) xx yy origin rfl nextRoom
  change (observed arg f₀).val=((occurrences new xx.2)[arg.val]?).elim 0 (fun q=>value q f₀)
  rw [inherited]
  by_cases active : arg.val<arity_
  · let j : Fin (ret).previousArgs:=⟨arg.val,active.trans_le fitsArgs⟩
    have yes : j.val<((ret).entry wrd d₀ last_ (ret).arityField).val:=by rw [arityRead];exact active
    rw [laid.1 arg j f₀ rfl yes]
    exact original j rfl active
  · have oldLength : (occurrences old yy.2).length≤arg.val:=by
      rw [DescentRetainedRangeDigits.length _ _ hp];omega
    have no : ((ret).entry wrd d₀ last_ (ret).arityField).val≤arg.val:=by rw [arityRead];omega
    rw [laid.2 arg f₀ no,List.getElem?_eq_none oldLength]
    rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
