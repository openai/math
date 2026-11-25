import OAI.Hierarchy.DescentClosedResetFreshWires
import OAI.Hierarchy.DescentNamedPublicBlock
import OAI.Hierarchy.DescentOperandResetPublic

namespace OAI
/-! # Original exterior argument slots through the two cuts and the ordered reset -/
namespace Hierarchy.DescentBundleHistory.WordBook
open DescentKernelHistory DescentLocalPrivateNames
noncomputable section
variable {X Y U V : Type} {r : Recipe U X} {s : Recipe V Y} (book : WordBook r s)

/-- Transport both the node and its actual finite argument ordinal. -/
def slotsTo : Slot r ≃ Slot s :=
  (Equiv.sigmaCongrRight (fun u=>finCongr (book.length u))).trans (Equiv.sigmaCongrLeft (β:=fun u=>Fin (s.arity u)) book.node)

theorem slots_read (slot : Slot r) (word : r.UsedWord) :
    read r slot=some word ↔ read s (book.slotsTo slot)=some (book.word word):=by
  obtain ⟨u,j⟩:=slot
  exact (read_some r u j word).trans ((book.hit u j word).trans (read_some s _ _ _).symm)
theorem slots_read_eq (slot : Slot r) :
    (read r slot).map book.word=read s (book.slotsTo slot):=by
  apply Option.ext
  intro t
  obtain ⟨w,rfl⟩:=book.word.surjective t
  rw [Option.map_eq_some_iff,←book.slots_read slot w]
  constructor
  · rintro ⟨u,hit,eqn⟩
    simpa only [book.word.injective eqn] using hit
  · intro hit
    exact ⟨w,hit,rfl⟩

end
end Hierarchy.DescentBundleHistory.WordBook

namespace Hierarchy.DescentRetainedResetPinPointer
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open ThreeFlat.Routing DescentResetPointerFields
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W}

/-- The initial all-edge split transports occupied private words bijectively. Public
pins retain their original identifier and aligned chunk, including at loop sites. -/
def grainBooks (W : MarkedWorld F d P bits) {B : BitDescription W} (m : W.graph.Edge→ℕ)
    (q : ℕ) (cut : ∀e,W.graph.width e=m e*q) (hp : 0<p) (pos : 0<q) (unit : p∣q)
    (sh : WorldShape p R B) : SiteBooks hp (sh.granular m q cut hp pos unit) sh:=by
  let scaled : q=q/p*p:=(Nat.div_mul_cancel unit).symm
  have positive : 0<q/p:=Nat.div_pos (Nat.le_of_dvd pos unit) hp
  refine ⟨Equiv.refl _,fun v=>WordBook.rerouted hp (sh.sites v) (grainMap W m q cut hp positive scaled v),?_⟩
  rintro v ⟨e|a,j,fit⟩ <;> rfl

def HasPin (sh : WorldShape p R B) (hp : 0<p) (y : NodeOrder.All B) (arg : ℕ)
    (ext : P) (chunk : ℕ) : Prop :=
  ∃j : Fin (((sh.sites y.1).recipe hp).arity y.2),j.val=arg ∧
    ∃b,((sh.sites y.1).recipe hp).operand y.2 j=.inl b ∧ b.exteriorAt W.graph y.1 ext chunk

theorem book_pin {W' : MarkedWorld F d P bits} {C : BitDescription W'} {sh : WorldShape p R B}
    {before : WorldShape p R C} (hp : 0<p) (book : SiteBooks hp sh before) (x : NodeOrder.All B)
    (arg : ℕ) (ext : P) (chunk : ℕ) (was : HasPin before hp (book.nodeAt hp x) arg ext chunk) :
    HasPin sh hp x arg ext chunk:=by
  obtain ⟨j,eqn,ref,hit,tag⟩:=was
  let localBook:=book.atSite x.1
  let k:=j.cast (localBook.length x.2).symm
  refine ⟨k,eqn,localBook.publicWord ref,localBook.publicHit x.2 k ref ?_,book.exterior _ ref _ _ tag⟩
  have ordinal : Fin.cast (localBook.length x.2) k = j := Fin.ext rfl
  rw [ordinal]
  exact hit

section Install
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d' : ℕ}
    (sh : WorldShape p R B) (hp : 0<p) (one : 1≤R)
    (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (hub : H→Bool)
    {width : W.graph.Edge→ℕ} (same : width=W.graph.width) (board : Network d' (Bool×Q) (publicWidth grp width))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (device : ∀v,Shape p (prog v)) (bound : ∀v u j g,((device v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
local notation "post" => B.installed home grp hub same board legacy sorted ids scalar prog valid
local notation "name" => NodeOrder.installedNames B home grp hub same board legacy sorted ids scalar prog valid
local notation "worldShape" => installedWorldShape sh hp one home grp hub same board legacy sorted ids scalar prog valid device bound widths

omit [Fintype Q] in
theorem installation_length (x : NodeOrder.All (post)) (y : NodeOrder.All B)
    (owns : name x=.inl y) :
    (((worldShape).sites x.1).recipe hp).arity x.2=((sh.sites y.1).recipe hp).arity y.2:=by
  have hx : x = (name).symm (.inl y) :=
    (name).injective (owns.trans ((name).apply_symm_apply _).symm)
  subst x
  subst width
  obtain ⟨v,u⟩:=y
  exact retained_terminal_arity W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u

omit [Fintype Q] in
theorem installation_pin (x : NodeOrder.All (post)) (y : NodeOrder.All B)
    (owns : name x=.inl y) (arg : ℕ) (ext : P) (chunk : ℕ) (was : HasPin sh hp y arg ext chunk) :
    HasPin worldShape hp x arg ext chunk:=by
  have hx : x = (name).symm (.inl y) :=
    (name).injective (owns.trans ((name).apply_symm_apply _).symm)
  subst x
  subst width
  obtain ⟨v,u⟩:=y
  obtain ⟨j,rfl,⟨port,g,ok⟩,hit,a,he,hport,hchunk⟩:=was
  dsimp only at hport hchunk
  subst port
  subst g
  subst ext
  let word : BlockRef p (boundaryWidth W.graph v):=⟨.inr a,chunk,ok⟩
  let f:=oldBlockMap W.graph home grp board ids sh.edges v
  let ref:=f.map word
  let j' := j.cast (retained_terminal_arity W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u).symm
  refine ⟨j',rfl,ref,retained_public W.graph home grp board ids sh.edges hp B.recipe prog sh.sites device v u j word hit,?_⟩
  have addr: (Sum.map Subtype.val Subtype.val ref.port,ref.block)=(Sum.inr a.val,chunk):=by
    simpa only [ref,f,word,oldField,firstBlock_eq] using old_at_pin hp W.graph home grp board ids sh.edges v a chunk ok
  cases hport : ref.port with
  | inl e=>simp [hport] at addr
  | inr z=>
    exact ⟨z,Sum.inr.inj (by simpa only [hport,Sum.map_inr] using congrArg Prod.fst addr),
      hport,congrArg Prod.snd addr⟩
end Install

set_option quotPrecheck false
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<b.reset.unit) (whole : p∣b.reset.unit)
    (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
local notation "key_" => DescentOrderedReset.grains W b.count b.order
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals key_ _ hp fit_ (resetMenu b) one wide
local notation "after_" => WorldShape.follow hp pos whole b.reblock b.cuts installed
local notation "next_" => (resetArchive b p hp whole a).bit
local notation "coarse" => b.reset.orderedReentry b.terminals key_
local notation "count_" => fun e=>(coarse).graph.width e/b.reset.unit

local notation "vertices" => b.frame.host.symm.toEmbedding.trans cap.vertex
local notation "hostRank" => (b.reset.rawHostRank b.terminals vertices).trans Fin.valEmbedding
local notation "siteRank" => b.raw.siteFrom
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) hostRank) b.valid.coordinates
local notation "oldRank" => (b.reset.nativeResetEdges b.terminals vertices key_).order.trans Fin.valEmbedding
local notation "edgeRank" => DescentResetLocalOrder.allCode b.raw oldRank S b.valid siteRank
local notation "cutFit" => b.reset.counts_fit b.terminals
private theorem nodeAt_cast {W' : MarkedWorld F d P bits} {B' : BitDescription W'}
    {first last : WorldShape p R B} {before : WorldShape p R B'} (hp : 0<p)
    (h : first=last) (book : SiteBooks hp last before) (x : NodeOrder.All B) :
    (Eq.mpr (congrArg (fun s=>SiteBooks hp s before) h) book).nodeAt hp x=book.nodeAt hp x := by
  cases h
  rfl

/-- The actual marked cut and physical permutation used by the reached reset. -/
def closedBooks : SiteBooks hp after_ installed :=
  Eq.mpr (congrArg (fun s=>SiteBooks hp s installed) (DescentResetFreshWires.closed_shape b hp one pos whole wide a sh)) <|
  SiteBooks.trans hp (SiteBooks.rename hp ((installed).pieces count_ b.reset.unit cutFit hp pos whole)
    (DescentPhysicalOrder.rename siteRank) (DescentPhysicalOrder.rename edgeRank))
    (SiteBooks.split hp installed count_ b.reset.unit cutFit pos whole)

local notation "books" => closedBooks b hp one pos whole wide a sh

theorem closedBooks_node (x : NodeOrder.All next_) :
    (books).nodeAt hp x = NodeOrder.followNames b.reblock _ x :=
  nodeAt_cast hp (DescentResetFreshWires.closed_shape b hp one pos whole wide a sh) _ x

set_option maxHeartbeats 800000 in
theorem closed_arity (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (owns : resetOrigin b hp whole a x=.inl y) :
    (((after_).sites x.1).recipe hp).arity x.2=((sh.sites y.1).recipe hp).arity y.2:=by
  let middle:=(books).nodeAt hp x
  have arity_eq : (((after_).sites x.1).recipe hp).arity x.2=(((installed).sites middle.1).recipe hp).arity middle.2:=
    ((books).atSite x.1).length x.2
  apply arity_eq.trans
  apply Eq.trans (b:=(((split_).sites y.1).recipe hp).arity y.2)
  · dsimp only [middle]
    rw [closedBooks_node]
    unfold reentryWorldShape
    apply installation_length (sh:=split_) (owns:=owns)
  · exact ((grainBooks W b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole) sh).atSite y.1).length y.2

theorem closed_hasPin (x : NodeOrder.All next_) (y : NodeOrder.All a.bit)
    (owns : resetOrigin b hp whole a x=.inl y) (arg : ℕ) (ext : P) (chunk : ℕ)
    (was : HasPin sh hp y arg ext chunk) : HasPin after_ hp x arg ext chunk:=by
  apply book_pin hp books x
  rw [closedBooks_node]
  unfold reentryWorldShape
  apply installation_pin (sh:=split_) (y:=y) (owns:=owns)
  exact book_pin hp (grainBooks W b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole) sh) y arg ext chunk was

theorem closed_pin (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_)
    (y : NodeOrder.All a.bit) (owns : resetOrigin b hp whole a x=.inl y)
    (j : Fin (((sh.sites y.1).recipe hp).arity y.2)) (port : Attached W.graph y.1) (chunk : ℕ)
    (ok : (chunk+1)*p≤bits port.val)
    (was : ((sh.sites y.1).recipe hp).operand y.2 j=.inl ⟨.inr port,chunk,ok⟩) :
    Reached.argumentPointer b.next next_ rank after_ hp pin args x j.val=.pin (pin port.val) chunk:=by
  obtain ⟨arg,eqn,⟨socket,t,fit⟩,hit,port',eqPort,hface,hchunk⟩:=
    closed_hasPin b hp one pos whole wide a sh x y owns j.val port.val chunk
      ⟨j,rfl,_,was,port,rfl,rfl,rfl⟩
  dsimp only at hface hchunk
  subst socket
  subst t
  rw [←eqn,←eqPort]
  exact Reached.argumentPointer_pin b.next next_ rank after_ hp pin args x.1 x.2 arg port' chunk fit hit

end
end Hierarchy.DescentRetainedResetPinPointer

end OAI
