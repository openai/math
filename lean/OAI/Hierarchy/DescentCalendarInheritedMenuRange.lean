import OAI.Hierarchy.DescentCalendarInheritedRange
import OAI.Hierarchy.DescentResetSelectedPrimaryRange
import OAI.Hierarchy.DescentRetainedAssignedDigits

namespace OAI
/-! # The acquired reset menu emits the inherited original range digits -/
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
variable {F P : Type} [Field F] {d : ℕ} {bits₀ : P→ℕ} {W : MarkedWorld F d P bits₀}
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
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSIMDLookup DescentResetPublicOperandBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.BorderVNP.Crossing DescentResetOperandSetup DescentDenseHostOrder
variable {machine : PhysicalReset} {atlas : machine.Atlas} {roots : machine.RootInputs} (menu : OperandMenu atlas roots)
local notation "chart" => machine.successor.setup
local notation "ret" => (chart).retained
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
variable (which : (chart).seven.control.Targets) (window : (chart).seven.Packets) (shape : Fin (chart).placement.shapes)
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


open DescentBundleHistory DescentOperandStateBanks
open DescentResetTrunks DescentRotorWindowArchive
open DescentSixParty.ClosedReset
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
local notation:max "observed" arg:arg f₀:arg => (chart).seven.decoded which window strips ((ret).outputID 1 (page f₀) arg current_) shape carrier coarse
local notation:max "prior_" j:arg f₀:arg => ((ret).entry wrd d₀ last_ ((ret).operandField (page f₀) j)).val


variable {U : ℕ} (namesAt : Fin U→Fin (chart).placement.sparse)
local notation "cfg" => publicOperands atlas roots menu.payload
variable (hostEq : (chart).placement.oldHosts=(ret).hosts) (groupEq : (chart).placement.groups*(chart).placement.blocks=(ret).grouped)
    (block : Fin (chart).placement.blocks) (rack : Fin (chart).placement.newHosts) (g₁ : Fin (chart).placement.groups)
    (alive : rack.val<U) (arg : Fin (ret).args) (f₀ : Fin 3)
local notation "key_" => (ret).outputID 1 (page f₀) arg current_
local notation "idx_" => (finProdFinEquiv (arg,current_) : Fin (cfg).mouths)
local notation "what" => namesAt ⟨rack.val,alive⟩
variable (compactShape : (chart).placement.shape what=shape) (compactHost : ((chart).placement.previous what).cast hostEq=carrier)
    (compactGroup : (finProdFinEquiv (g₁,block)).cast groupEq=coarse) (keep : menu.keep shape=true)
    (data : (cfg).Data machine.successor.middle.rotorBits)
    (blank : ((cfg).oldConfig.header ((cfg).basic data) 0).val=0 → ((cfg).reg data 1).val=0)
    (physical : ∀within:rack.val<U,((cfg).oldConfig.header ((cfg).basic data) 0).val≠0 →
      ((cfg).reg data 3).val=((chart).placement.shape (namesAt ⟨rack.val,within⟩)).val)
local notation "Y" => (chart).assignedDigits hostEq groupEq which window strips
local notation "paid_" => menu.spanValue namesAt Y key_ block rack g₁ data idx_ (page f₀) blank physical

include won owns compared stencil counts origin compactShape compactHost compactGroup keep in
theorem calendar_inherited_span_cast (outBits : ℕ) (outRoom : (ret).bits≤outBits) (enough : (ret).bits≤(chart).fieldBits)
    (fitsArgs : arity_≤(ret).previousArgs)
    (arityRead : ((ret).entry wrd d₀ last_ (ret).arityField).val=arity_)
    (original : ∀j:Fin (ret).previousArgs,j.val=arg.val → j.val<arity_ → prior_ j f₀=atSlot old yy.2 j.val f₀) :
    ((paid_).val : Cell outBits).val=atSlot new xx.2 arg.val f₀:=by
  have digit:=calendar_inherited_range (b:=b) (a:=a) (early:=early) («chart»:=chart) (total:=total) (axis:=axis)
    (blocks:=blocks) (groups:=groups) (size:=size) (fits:=fits) (L:=L) (won:=won) (room:=room)
    (nodeRoom:=nodeRoom) (hp:=hp) (whole:=whole) (one:=one) (posUnit:=posUnit) (widthBound:=widthBound)
    (sh:=sh) (xx:=xx) (yy:=yy) (origin:=origin) (which:=which) (window:=window) (shape:=shape) (input:=input)
    (word:=word) (owns:=owns) (compared:=compared) (stencil:=stencil) (counts:=counts) (nextRoom:=nextRoom)
    arg f₀ fitsArgs arityRead original
  have source:=menu.selected_primary_decoded namesAt which window strips hostEq groupEq block rack g₁ alive
    arg current_ f₀ data blank physical (compactShape.symm ▸ keep)
  change (paid_) = (((chart).seven.decoded which window strips key_
    ((chart).placement.shape what) (((chart).placement.previous what).cast hostEq)
    ((finProdFinEquiv (g₁,block)).cast groupEq)).val : Cell (chart).fieldBits) at source
  have address : ((chart).placement.shape what, ((chart).placement.previous what).cast hostEq,
      (finProdFinEquiv (g₁,block)).cast groupEq) = (shape,carrier,coarse) :=
    Prod.ext compactShape (Prod.ext compactHost compactGroup)
  have aligned := congrArg (fun ij : Fin (chart).placement.shapes × Fin (ret).hosts × Fin (ret).grouped =>
    ((chart).seven.decoded which window strips key_ ij.1 ij.2.1 ij.2.2).val) address
  have castDigit : paid_ = ((observed arg f₀).val : Cell (chart).fieldBits) :=
    source.trans (congrArg (fun x : ℕ => (x : Cell (chart).fieldBits)) aligned)
  have size_ : (observed arg f₀).val<2^(chart).fieldBits:=(observed arg f₀).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) enough)
  refine (congrArg (fun x : Cell (chart).fieldBits => (x.val : Cell outBits).val) castDigit).trans ?_
  change (((observed arg f₀).val%2^(chart).fieldBits)%2^outBits)=_
  rw [Nat.mod_eq_of_lt size_,Nat.mod_eq_of_lt ((observed arg f₀).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) outRoom))]
  exact digit

include won owns compared stencil counts origin compactShape compactHost compactGroup keep in
theorem calendar_inherited_span_value (enough : (ret).bits≤(chart).fieldBits)
    (fitsArgs : arity_≤(ret).previousArgs)
    (arityRead : ((ret).entry wrd d₀ last_ (ret).arityField).val=arity_)
    (original : ∀j:Fin (ret).previousArgs,j.val=arg.val → j.val<arity_ → prior_ j f₀=atSlot old yy.2 j.val f₀) :
    (paid_).val=atSlot new xx.2 arg.val f₀ :=by
  have decoded:=calendar_inherited_span_cast (b:=b) (a:=a) (early:=early) (menu:=menu) (total:=total)
    (axis:=axis) (blocks:=blocks) (groups:=groups) (size:=size) (fits:=fits) (L:=L) (won:=won)
    (room:=room) (nodeRoom:=nodeRoom) (hp:=hp) (whole:=whole) (one:=one) (posUnit:=posUnit)
    (widthBound:=widthBound) (sh:=sh) (xx:=xx) (yy:=yy) (origin:=origin) (which:=which) (window:=window)
    (shape:=shape) (input:=input) (word:=word) (owns:=owns) (compared:=compared) (stencil:=stencil)
    (counts:=counts) (nextRoom:=nextRoom) (namesAt:=namesAt) (hostEq:=hostEq) (groupEq:=groupEq)
    (block:=block) (rack:=rack) (g₁:=g₁) (alive:=alive) (arg:=arg) (f₀:=f₀) (compactShape:=compactShape)
    (compactHost:=compactHost) (compactGroup:=compactGroup) (keep:=keep) (data:=data) (blank:=blank)
    (physical:=physical) (chart).fieldBits enough enough fitsArgs arityRead original
  change (paid_).val%2^(chart).fieldBits=_ at decoded
  simpa only [Nat.mod_eq_of_lt (paid_).isLt] using decoded

end
end Hierarchy.DescentPrimitivePalette

end OAI
