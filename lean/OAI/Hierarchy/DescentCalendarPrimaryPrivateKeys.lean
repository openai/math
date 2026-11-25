import OAI.Hierarchy.DescentCalendarPrimarySpans
import OAI.Hierarchy.DescentRetainedPrivateKeyRaster

namespace OAI
/-! Reached retained-node coordinates completed to a private-key raster. -/
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
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "dim" => (T).commonDepth
local notation "wide" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "ix" u:arg => StarKeys.filled W.graph (A).pos (A).block digits u
local notation "oldId" => (A).site cap.vertex cap.valid.coordinates
local notation "small" => b.frame.enough.trans (Nat.sub_le ..)
local notation "roster" => ClosedReset.Recorded.old_roster (reset:=b)
local notation "safe" => (roster).2.2.2.2.2.choose
local notation "Node" u:arg => (a.bit.recipe u).Node
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
local notation "name" => cap.vertex.trans (Fin.castLEEmb room)
variable {R:ℕ} (hp : 0<p) (whole : p∣(Z).unit) (one:1≤R) (posUnit:0<(Z).unit)
  (widthBound:max 1 (max (Z).width (C*(Z).width))≤R) (sh:DescentBundleHistory.WorldShape p R a.bit)
local notation "nextBit" => (resetArchive b p hp whole a).bit
variable (xx : NodeOrder.All nextBit) (yy : NodeOrder.All a.bit)
  (origin : resetOrigin b hp whole a xx=Sum.inl yy)
local notation "term" => (T).home yy.1
local notation "u₀" => b.frame.host.symm ((T).code term).1
local notation "carrier" => name u₀
local notation "hi" => (Z).rootBlock T (.inr term)
local notation "coarse" => (hi).cast (hl).symm
local notation "source" lo:arg => (rearrange b.frame.basis).symm (join small hi lo)
local notation "rail" lo:arg => (rearrange L).symm (join fits coarse ((coords).symm lo))
local notation "pos" lo:arg => (finProdFinEquiv.symm (Fin.cast size (rail lo)):Fin (ret).groups×Fin (ret).blocks)
local notation "census" lo:arg => ∑u:W.graph.Site,if ((A).pos u).2=u₀ ∧ ix u=source lo then Fintype.card (Node u) else 0

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
variable (compared : priorAt chart window carrier coarse=(fun i j=>decide (source (coords i)<source (coords j))))
variable (stencil : ∀lo,word lo/2=DescentPlainTerminal.Suffix.Stencil.shapeCode (wide-dim)
  (2^(Z).n) (DescentPlainTerminal.Suffix.fieldsRelative dim (ClosedReset.Recorded.originalCell (reset:=b) u₀ (source lo))))
variable (counts : ∀lo,(ret).originalCount wrd ((coords).symm lo)=∑u:W.graph.Site,
    if DescentPaidResidentCount.occupies (A) (Equiv.refl _) name carrier ((pos lo).1.cast groups)
      ((pos lo).2.cast blocks) u then Fintype.card (Node u) else 0)


open DescentRetainedPrivateSlotBook DescentBundleHistory DescentLocalPrivateNames DescentOperandStateBanks
open DescentRetainedResetPinPointer DescentPackedResetDonors DescentResetTrunks DescentRotorWindowArchive
open DescentSixParty.ClosedReset
local notation "D₀" => reached b hp one posUnit whole widthBound a sh xx yy origin
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ posUnit) (b.unit ▸ whole)
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals (DescentOrderedReset.grains W b.count b.order)
  _ hp fit_ (resetMenu b) one widthBound
local notation "sh₁" => WorldShape.follow hp posUnit whole b.reblock b.cuts installed
local notation "r" => ((sh₁).sites xx.1).recipe hp
local notation "fibre" => DescentNamedContact.Fibre (T).home term
local notation "src" u:arg => (sh.sites (u:fibre).val).recipe hp
local notation "oldNode" u:arg n:arg => (early (u:fibre).val n).castLE (nodeRoom (u:fibre).val)
local notation "dof" u:arg => (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix (u:fibre).val)))
local notation "ord" => physicalDonorOrder b.frame term ret coords
local notation "take_" => ownerAt chart which window shape carrier coarse
local notation "prior_" => priorAt chart window carrier coarse
local notation "routed" => (ret).routedWord take_ prior_ wrd
local notation "ownerOf" q:arg => ((D₀).slots q).1
local notation "slotOf" q:arg => ((D₀).slots q).2

/-- The original donor digit is injective in the actual terminal's fibre. -/
def calendar_donor_index : fibre↪Fin (ret).donors where
  toFun u:=dof u
  inj' :=by
    intro x y eqn
    apply Subtype.ext
    have hx:=b.frame.homeHost x.val
    have hy:=b.frame.homeHost y.val
    rw [x.property] at hx
    rw [y.property] at hy
    have hosts : ((A).pos x.val).2=((A).pos y.val).2:=b.frame.host.injective (hx.symm.trans hy)
    change (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix x.val)))=
      (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix y.val))) at eqn
    have equalLow := (coords).symm.injective eqn
    have ids : ix x.val=ix y.val:= (old_home_digit b.frame term x).trans
      ((congrArg (fun lo=>source lo) equalLow).trans (old_home_digit b.frame term y).symm)
    apply (oldId).injective
    have sorted:=GroupStage.scheduled_site_order S A ctl.base ctl.radix cap.vertex cap.valid.coordinates
    exact le_antisymm (le_of_not_gt (fun h=>(not_lt_of_ge ids.le) ((sorted _ _ hosts.symm).1 h)))
      (le_of_not_gt (fun h=>(not_lt_of_ge ids.symm.le) ((sorted _ _ hosts).1 h)))

def reached_mouth {tag out:Type} (book:Recipe tag out) {N K:ℕ} (num:book.Node↪Fin N)
    (fit:∀n,book.arity n≤K) : Slot book↪Fin (N*K) where
  toFun s:=finProdFinEquiv (num s.1,s.2.castLE (fit _))
  inj' :=by
    rintro ⟨u,j⟩ ⟨v,k⟩ same
    have pair:=finProdFinEquiv.injective same
    obtain rfl:=num.injective (congrArg Prod.fst pair)
    have args : j=k:=Fin.ext (congrArg (fun z:Fin N×Fin K=>z.2.val) pair)
    cases args
    rfl

theorem reached_mouth_number {tag out:Type} (book:Recipe tag out) {N K:ℕ} (num:book.Node↪Fin N)
    (fit:∀n,book.arity n≤K) (s:Slot book) :
    (reached_mouth book num fit s).val=(num s.1).val*K+s.2.val:=by
  change (finProdFinEquiv (num s.1, s.2.castLE (fit _))).val = _
  simp only [finProdFinEquiv_apply_val, Fin.val_castLE, Nat.mul_comm, Nat.add_comm]

variable (oldArgs : ∀(u:fibre) n,(src u).arity n≤(ret).previousArgs)
  (nextRoom : Fintype.card ((after_).recipe xx.1).Node≤(ret).nodes)
  (newArgs : ∀n,(r).arity n≤(ret).args)
local notation "originalAddr" u:arg => reached_mouth (src u) ((early (u:fibre).val).toEmbedding.trans (Fin.castLEEmb (nodeRoom (u:fibre).val))) (oldArgs u)
local notation "newAddr" => reached_mouth r ((order_ xx.1).toEmbedding.trans (Fin.castLEEmb nextRoom)) newArgs
local notation "donors" => calendar_donor_index (b:=b) (a:=a) (yy:=yy) (chart:=chart) (total:=total) (axis:=axis)
local notation "current" q:arg => (finProdFinEquiv.symm (newAddr q):Fin (ret).nodes×Fin (ret).args)
local notation "a₀" u:arg s:arg => (s:Slot (src u)).2.castLE (oldArgs u (s:Slot (src u)).1)
local notation "atMouth" u:arg s:arg f:arg => (ret).entry wrd (donors u) (oldNode u (s:Slot (src u)).1) ((ret).operandField f (a₀ u s))
variable (arityWords : ∀(u:fibre) n,((ret).entry wrd (donors u) (oldNode u n) (ret).arityField).val=(src u).arity n)
variable (pin:P→ℕ)
local notation "oldPtr" u:arg s:arg => Reached.argumentPointer cap a.bit early sh hp pin (ret).previousArgs ⟨(u:fibre).val,(s:Slot (src u)).1⟩ (s:Slot (src u)).2.val
variable (headerWords : ∀(u:fibre)(s:Slot (src u))(f:Fin 4),(atMouth u s (f.castLE (by decide:4≤7))).val=(oldPtr u s).header f)
variable (aliasRoom:(ret).previousNodes*(ret).previousArgs≤2^(ret).bits)
local notation "key" => (D₀).key ((donors).trans (ord).toEmbedding) (fun u=>originalAddr u) aliasRoom

set_option maxHeartbeats 1050000 in
include won owns compared stencil counts arityWords in
private theorem calendar_registered_slots (s:Slot r) : take_ (donors (ownerOf s))=true ∧
      (oldNode (ownerOf s) (slotOf s).1).val<(ret).originalCount wrd (donors (ownerOf s)) ∧
      (a₀ (ownerOf s) (slotOf s)).val<((ret).entry wrd (donors (ownerOf s)) (oldNode (ownerOf s) (slotOf s).1) (ret).arityField).val ∧
      (current s).1.val=(ret).offset routed (ord (donors (ownerOf s)))+(oldNode (ownerOf s) (slotOf s).1).val ∧
      (current s).2.val=(a₀ (ownerOf s) (slotOf s)).val:=by
  have geometry (s:Slot r) :=
    calendar_primary_donor b a early chart total axis blocks groups size fits L won room nodeRoom term hp whole
      which window shape input word owns compared stencil counts ⟨xx.1,s.1⟩
      ⟨(ownerOf s).val,(slotOf s).1⟩
      (reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin s).1
      (ownerOf s).property nextRoom
  obtain ⟨taken,population,index,_⟩ := geometry s
  have placed : finProdFinEquiv.symm (newAddr s) =
      (((order_ xx.1) s.1).castLE nextRoom, s.2.castLE (newArgs s.1)) :=
    finProdFinEquiv.symm_apply_apply _
  refine ⟨taken,population,?_,?_,?_⟩
  · exact (slotOf s).2.isLt.trans_eq (arityWords (ownerOf s) (slotOf s).1).symm
  · exact (congrArg (fun z => z.1.val) placed).trans index
  · exact (congrArg (fun z => z.2.val) placed).trans
      (reached_slot_origin b hp one posUnit whole widthBound a sh xx yy origin s).2.symm

include compared in
private theorem calendar_aligned_slot (i : Fin (ret).donors) : neighbors prior_ i = (ord i).val := by
  have cmp j k : prior_ j k = decide ((ord j).val < (ord k).val) := by
    rw [compared]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (physicalDonorOrder_lt b.frame term ret coords j k).symm
  exact (ret).original_rank prior_ ord cmp i

set_option maxHeartbeats 1050000 in
include owns won stencil counts arityWords in
private theorem calendar_covered_slots : ∀(d₀ : Fin (ret).donors) (n₀ : Fin (ret).previousNodes) (j₀ : Fin (ret).previousArgs),take_ d₀=true→n₀.val<(ret).originalCount wrd d₀→
      j₀.val<((ret).entry wrd d₀ n₀ (ret).arityField).val→∃s:Slot r,
        donors (ownerOf s)=d₀ ∧ oldNode (ownerOf s) (slotOf s).1=n₀ ∧ a₀ (ownerOf s) (slotOf s)=j₀:=by
    intro d₀ n₀ j₀ paid occupied used
    obtain ⟨u,n,_,address,number⟩:=calendar_primary_original b a early chart total axis blocks groups size fits L won room
      term which window shape input word owns stencil counts d₀ n₀ paid occupied
    have dAt:donors u=d₀:=by
      change (coords).symm (low («c»:=dim) (rearrange b.frame.basis (ix u.val)))=d₀
      rw [address,Equiv.apply_symm_apply,low_join]
      exact (coords).symm_apply_apply d₀
    have nAt : oldNode u n=n₀ :=Fin.ext number
    have ar : j₀.val < (src u).arity n := by
      apply used.trans_eq
      simpa only [dAt, nAt] using arityWords u n
    let old:Slot (src u):=⟨n,⟨j₀.val,ar⟩⟩
    obtain ⟨s,eqn⟩:=(D₀).slots.surjective ⟨u,old⟩
    refine ⟨s,?_,?_,?_⟩
    · simpa only [eqn] using dAt
    · apply Fin.ext
      exact (congrArg (fun v : Σ u : fibre, Slot (src u) => (early v.1.val v.2.1).val) eqn).trans number
    · apply Fin.ext
      exact congrArg (fun v : Σ u : fibre, Slot (src u) => v.2.2.val) eqn

section
variable (registered : ∀s : Slot r, take_ (donors (ownerOf s))=true ∧
      (oldNode (ownerOf s) (slotOf s).1).val<(ret).originalCount wrd (donors (ownerOf s)) ∧
      (a₀ (ownerOf s) (slotOf s)).val<((ret).entry wrd (donors (ownerOf s)) (oldNode (ownerOf s) (slotOf s).1) (ret).arityField).val ∧
      (current s).1.val=(ret).offset routed (ord (donors (ownerOf s)))+(oldNode (ownerOf s) (slotOf s).1).val ∧
      (current s).2.val=(a₀ (ownerOf s) (slotOf s)).val)
variable (aligned : ∀i : Fin (ret).donors, neighbors prior_ i = (ord i).val)
variable (occurs : ∀(d₀ : Fin (ret).donors) (n₀ : Fin (ret).previousNodes) (j₀ : Fin (ret).previousArgs),take_ d₀=true→n₀.val<(ret).originalCount wrd d₀→
      j₀.val<((ret).entry wrd d₀ n₀ (ret).arityField).val→∃s:Slot r,
        donors (ownerOf s)=d₀ ∧ oldNode (ownerOf s) (slotOf s).1=n₀ ∧ a₀ (ownerOf s) (slotOf s)=j₀)
attribute [local irreducible] DescentRetainedPrivateSlotBook.reached
set_option maxHeartbeats 900000 in
include registered aligned occurs headerWords in
private theorem private_keys_from_slots :
    (∀s:Slot r,(ret).keyIndex routed (newAddr s)=(read r s).map key) ∧
      (∀j,(∀s,newAddr s≠j)→(ret).keyIndex routed j=none):=by
  have previous (s : Slot r) :=
    Reached.slot_privateIndex cap a.bit early sh hp pin (ret).previousArgs (ownerOf s).val
      (originalAddr (ownerOf s))
      (fun j => (reached_mouth_number (src (ownerOf s))
        ((early (ownerOf s).val).toEmbedding.trans (Fin.castLEEmb (nodeRoom (ownerOf s).val)))
        (oldArgs (ownerOf s)) j).symm) (slotOf s)
  constructor
  · intro s
    exact key_on_real (orig:=D₀) (C:=chart) (which:=which) (X:=window) (panels:=strips)
      (t:=shape) (h:=carrier) (g:=coarse) (order:=ord) (rank:=aligned)
      (donor:=donors) (node:=fun u n => oldNode u n) (arity:=oldArgs) (place:=newAddr) (issued:=registered)
      (slots:=fun u => originalAddr u) (fit:=aliasRoom) (ptr:=fun j=>oldPtr (ownerOf j) (slotOf j))
      (archive:=fun j=>headerWords (ownerOf j) (slotOf j)) (privateSource:=previous) s
  · exact key_on_padding (orig:=D₀) (C:=chart) (which:=which) (X:=window) (panels:=strips)
      (t:=shape) (h:=carrier) (g:=coarse) (order:=ord) (rank:=aligned)
      (donor:=donors) (node:=fun u n => oldNode u n) (arity:=oldArgs) (place:=newAddr)
      (issued:=registered) (covered:=occurs)
end

set_option maxHeartbeats 900000 in
include won owns compared stencil counts arityWords headerWords in
theorem calendar_primary_private_keys :
    (∀s:Slot r,(ret).keyIndex routed (newAddr s)=(read r s).map key) ∧
      (∀j,(∀s,newAddr s≠j)→(ret).keyIndex routed j=none):=by
  have registered := calendar_registered_slots b a early chart total axis blocks groups size fits L won room
      nodeRoom hp whole one posUnit widthBound sh xx yy origin which window shape input word owns compared
      stencil counts oldArgs nextRoom newArgs arityWords
  have aligned := calendar_aligned_slot b a chart total axis room yy window compared
  have occurs := calendar_covered_slots b a early chart total axis blocks groups size fits L won room
      nodeRoom hp whole one posUnit widthBound sh xx yy origin which window shape input word owns stencil
      counts oldArgs arityWords
  exact private_keys_from_slots b a early chart total axis size fits L room nodeRoom hp whole one posUnit
    widthBound sh xx yy origin which window shape input oldArgs nextRoom newArgs pin headerWords aliasRoom
    registered aligned occurs

private theorem donor_read_key_at {Tag₀ Tag₁ Out₀ I₀ : Type} {Out₁ : I₀→Type}
    {recipe₀ : Recipe Tag₀ Out₀} {parts : ∀i₀,Recipe Tag₁ (Out₁ i₀)} {d₀ k₀ w₀ : ℕ}
    (gather : Donors recipe₀ parts) (hosts : I₀↪Fin d₀)
    (mouths : ∀i₀,Slot (parts i₀)↪Fin k₀) (space : k₀≤2^w₀)
    (arg : Slot recipe₀) (oldWord : (parts (gather.slots arg).1).UsedWord)
    (readOld : read (parts (gather.slots arg).1) (gather.slots arg).2=some oldWord) :
    ∃w₁,read recipe₀ arg=some w₁ ∧ gather.key hosts mouths space w₁=
      (hosts (gather.slots arg).1,(firstAlias _ (mouths _) oldWord).castLE space) := by
  let node := gather.words.symm ⟨(gather.slots arg).1,oldWord⟩
  have inds := gather.words.apply_symm_apply ⟨(gather.slots arg).1,oldWord⟩
  refine ⟨node,(gather.uses arg node).2 ⟨oldWord,readOld,inds⟩,?_⟩
  exact congrArg (fun row : Σi₀,(parts i₀).UsedWord =>
    (hosts row.1,(firstAlias _ (mouths row.1) row.2).castLE space)) inds

private theorem private_pointer_of_read {Word₀ : Type} (ptr : Pointer) (addr : Word₀→ℕ) (reading : Option Word₀)
    (word₀ : Word₀) (hit : reading=some word₀) (same : ptr.privateIndex=reading.map addr) :
    ptr=Pointer.privateWord (addr word₀) := by
  subst reading
  cases ptr with
  | privateWord j => exact congrArg Pointer.privateWord (Option.some.inj same)
  | pin _ _ => cases same
  | cable _ _ _ => cases same

set_option maxHeartbeats 850000 in
include headerWords in
/-- A private operand read in the physical old rectangle has the private
address of its actual reached recipe as its successor. -/
theorem calendar_primary_private_pointer (s:Slot r) (oldName:ℕ)
    (was:oldPtr (ownerOf s) (slotOf s)=Pointer.privateWord oldName) :
    ∃w:(r).UsedWord,read r s=some w ∧
      key w=(ord (donors (ownerOf s)),atMouth (ownerOf s) (slotOf s) (2:Fin 7)) ∧
      Reached.argumentPointer b.next after_ order_ sh₁ hp pin (ret).args ⟨xx.1,s.1⟩ s.2.val=
        Pointer.privateWord (firstAlias r newAddr w).val:=by
  let u:=ownerOf s
  let q:=slotOf s
  have previous:=Reached.slot_privateIndex cap a.bit early sh hp pin (ret).previousArgs u.val
    (originalAddr u) (fun j=>(reached_mouth_number (src u) ((early u.val).toEmbedding.trans (Fin.castLEEmb (nodeRoom u.val))) (oldArgs u) j).symm) q
  rw [was] at previous
  change some oldName=(read (src u) q).map (fun w=>(firstAlias _ (originalAddr u) w).val) at previous
  cases readOld:read (src u) q with
  | none=>simp [readOld] at previous
  | some old=>
    rw [readOld,Option.map_some] at previous
    have aliasNumber:=Option.some.inj previous
    obtain ⟨w,got,keyPair⟩:=donor_read_key_at (D₀) ((donors).trans (ord).toEmbedding)
      (fun site=>originalAddr site) aliasRoom s old readOld
    refine ⟨w,got,?_,?_⟩
    · have label:=headerWords u q 2
      rw [was] at label
      change (atMouth u q (2:Fin 7)).val=oldName at label
      exact keyPair.trans (Prod.ext rfl (Fin.ext (aliasNumber.symm.trans label.symm)))
    · have reachedAt:=Reached.slot_privateIndex b.next after_ order_ sh₁ hp pin (ret).args xx.1
        newAddr (fun j=>(reached_mouth_number r ((order_ xx.1).toEmbedding.trans (Fin.castLEEmb nextRoom)) newArgs j).symm) s
      exact private_pointer_of_read _ (fun word₀=>(firstAlias r newAddr word₀).val)
        (read r s) w got reachedAt


end
end Hierarchy.DescentPrimitivePalette

end OAI
