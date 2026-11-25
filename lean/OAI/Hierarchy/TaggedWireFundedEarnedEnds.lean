import OAI.Hierarchy.TaggedWireFundedPurchasedLedger
import OAI.Hierarchy.TaggedWireFundedBallots
import OAI.Hierarchy.ProbeFixedEarlierBought
import OAI.Hierarchy.ProbeFixedWideBoughtCatalogue
import OAI.Hierarchy.ProbeFixedWideBoughtViewPrefix
import OAI.Hierarchy.ProbePaidOriginalFaces
import OAI.Hierarchy.TaggedWireEarnedPhysical

namespace OAI
/-! # The reference ballot and the chosen continuation use the same previously purchased sites -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
set_option cleanup.letToHave false
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots h D k)
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl

local notation "page" => v.wideSignedPage h width
local notation "owners" => sinkBank start cnt r (P).catalogue.rows

local notation "stock" => v.fixedTerminalStock P h width
local notation "bits" => page stock
local notation "banks" => TerminalLayout.settlement bits stock
local notation "source" => TerminalLayout.source bits
local notation "table" => TerminalLayout.table bits
local notation "target" => TerminalLayout.destination bits
local notation "C" => v.wideSignedChart h width stock
local notation "order" => wideRouteOrder h D k

variable (size : ℕ) (extent : (A).endAddress v.mesh≤ size) (π : Equiv.Perm (Fin (2^h)))
  (seed : Boot.Tape h D) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "L" => (reader).format.windows

local notation "dims" => v.wide_stock_sizes h width age budget small
local notation "base" => v.wideOrigin h width size seed π
local notation "origin" b => v.wideOrigin h width size ((L).header es b seed) π
local notation "slots" => (reader).format.slot

open Filter CalendarTape RepairHistogram

/-- Only fixed cofinal thresholds for the actual elected date and immutable ordinal tables. -/
def earnedEndsHeight := max v.paidBallotHeight
  (max v.wideJobs (Classical.choose (eventually_atTop.1 v.wire_bought_earlier_active)))

namespace FundedDate
variable {v h width size π seed age budget small} {tail x} {a : Attempt}
    {t : WireTelescope.CalendarTape.Prefix slots es base (.attempt a::tail) x} {refChoice choice : (slots (.attempt a)).choice x}
    (R : v.FundedDate h width size π seed age budget small t refChoice)
    (H : v.FundedDate h width size π seed age budget small t choice)
local notation "ev" => Event.attempt a
local notation "b" => (P).catalogue
local notation "dirs" => (P).routes.directory
local notation "heads" => (dirs).header h D k v.sampler.degree v.depth
local notation "refTape" => v.wideFundedRaw h width v.maxBits ((L).header es R.code seed)
local notation "useTape" => v.wideFundedRaw h width v.maxBits ((L).header es H.code seed)
local notation "nativeRef" => origin R.code
local notation "nativeUse" => origin H.code
local notation "chkRef" => checkedOut C ((A).endAddress v.mesh) nativeRef
local notation "chkUse" => checkedOut C ((A).endAddress v.mesh) nativeUse
local notation "marks" => v.birthMarks P h width r banks source table target owners nativeRef
local notation "name" => siteNumber h D k
local notation "edgeOrder" => v.wideOrder h width
local notation "originalEnds" => (b).physicalEnds (π:=π.symm) («marks»:=marks) dirs edgeOrder rfl
local notation "physical" => earnedCatalogue originalEnds (name).toEmbedding

/-- The public birth flag and location are both looked up before the two
future selector strings can begin to differ. -/
private theorem old_checkout (extent : (A).endAddress v.mesh≤ size) :
    PrefixAgreement.Low ((A).first+H.prior.length*(A).stride) x chkUse := by
  have run:=(v.wide_stock_at h width size extent v.radius π.symm useTape age budget small).mounted_all
  have old:=v.wide_prestate_low h width size π.symm useTape v.radius H.prior.length H.index.isLt.le run
  have atPrior := H.prior_state
  unfold wideOrigin at atPrior
  rw [atPrior] at old
  exact fun n hn=>(H.before_low n hn).trans (old n hn)

theorem earned_paid_ends (extent : (A).endAddress v.mesh≤ size) (late : v.earnedEndsHeight≤h)
    (e : Fin (b).rows) (positive : 0<H.paid e) :
    ((physical).tail e=H.afterMount.actual.tail e ∧ (physical).head e=H.afterMount.actual.head e) ∨
    ((physical).tail e=H.afterMount.actual.head e ∧ (physical).head e=H.afterMount.actual.tail e) := by
  have bounds:=max_le_iff.mp late
  have ages:=max_le_iff.mp bounds.2
  have jobs : v.wideJobs≤2^w:=ages.1.trans ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)
  have word:=(dims).words.addresses
  rcases (b).split_index e with ⟨j,rfl⟩|⟨u,rfl⟩
  · left
    have atCore := (b).physicalEnds_core (π:=π.symm) («marks»:=marks) dirs edgeOrder rfl ((edgeOrder) j)
    rw [(edgeOrder).symm_apply_apply] at atCore
    have first := H.afterMount.tail ((edgeOrder) j)
    have second := H.afterMount.head ((edgeOrder) j)
    change H.afterMount.actual.tail ((b).coreIndex ((edgeOrder).symm ((edgeOrder) j)))=(name) (ends π.symm ((edgeOrder) j)).1 at first
    change H.afterMount.actual.head ((b).coreIndex ((edgeOrder).symm ((edgeOrder) j)))=(name) (ends π.symm ((edgeOrder) j)).2 at second
    rw [(edgeOrder).symm_apply_apply] at first second
    change (name) ((originalEnds) ((b).coreIndex j)).1=_ ∧ (name) ((originalEnds) ((b).coreIndex j)).2=_
    rw [atCore,first,second]
    exact ⟨rfl,rfl⟩
  · have accounting:=H.paid_account extent bounds.1 ((b).boughtIndex u)
    have charged : 0<H.afterPaid ((b).boughtIndex u):=by omega
    have current : 0<v.wirePaidAt h width v.maxBits (H.index.val+1)
        (StockBound.state C nativeUse (H.index.val+1)) ((b).boughtIndex u) := by
      change 0<v.wirePaidAt h width v.maxBits (H.prior.length+1)
        (StockBound.state C nativeUse (H.prior.length+1)) ((b).boughtIndex u)
      rw [H.next_state];exact charged
    obtain ⟨p,old,rel,elapsed,birth,ordinal,active⟩:=
      Classical.choose_spec (eventually_atTop.1 v.wire_bought_earlier_active) h ages.2
        width small budget size extent π.symm useTape v.maxBits H.index u current
    have endAge := (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp bounds.1).2).2).2
    have internal := (Classical.choose_spec (eventually_atTop.1 v.wire_paid_ends) h endAge) width small budget size extent π.symm
      useTape v.maxBits (H.index.val+1) H.index.isLt ((b).boughtIndex u) current
    dsimp only [FundedDate.index] at internal
    have atNext := H.next_state
    unfold wideOrigin at atNext
    rw [atNext] at internal
    let cut:=(A).base v.mesh (.attempt (v.sourceAttempt p))+(A).stride
    have hit : Event.attempt (v.sourceAttempt p)∈es:=birth ▸ (es).get_mem old
    have cap : cut<2^w:=((A).within v.mesh _ hit).trans_lt word
    have ep : position v.mesh (.attempt (v.sourceAttempt p))=old.val := by
      rw [←birth,List.get_eq_getElem,position_at v.mesh old.isLt]
    have room : cut≤(A).first+H.prior.length*(A).stride := by
      have mul:=Nat.mul_le_mul_right (A).stride (show old.val+1≤H.prior.length from elapsed)
      rw [Nat.add_mul,one_mul] at mul
      dsimp only [cut,Arena.base];rw [ep];omega
    have length : H.prior.length=R.prior.length:=H.clock.1.symm.trans R.clock.1
    have saved : PrefixAgreement.Low cut chkUse chkRef := by
      intro n hn
      have low:=hn.trans_le room
      have refLow : n < (A).first+R.prior.length*(A).stride := by
        simpa only [←length] using low
      exact ((H.old_checkout extent) n low).symm.trans ((R.old_checkout extent) n refLow)
    have refLive:=(v.wide_stock_at h width size extent v.radius π.symm refTape age budget small).mounted_all
    have received:=v.wide_signed_boot_at h width size extent stock v.radius π.symm order refTape word
    have stop:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
    have headLow : (heads).stop≤(A).first:=(Nat.le_add_right ..).trans stop
    have header : (heads).Loaded chkRef:=received.2.2.1.board.rom.outer.frame (fun n _ hn=>
      v.wide_signed_checkout_below h width stock v.radius π.symm order refTape size n (hn.trans_le headLow) refLive)
    have flag:=v.wide_bought_flag_low h width p rel chkUse chkRef saved cap header jobs
    have view:=v.wide_bought_view_low h width p rel chkUse chkRef saved cap header jobs
    dsimp only at flag view
    rw [ordinal] at flag view
    have refActive : (b).bought.flag.eval chkRef (u.val:Word w)≠0 :=
      fun zero => active (flag.trans zero)
    obtain ⟨c,ident,loc⟩:=(v.wide_bought_catalogue_at h width size π.symm refTape extent age jobs small budget u).mp refActive
    have atBought:=(b).physicalEnds_bought (π:=π.symm) («marks»:=marks) dirs edgeOrder rfl c
    change (originalEnds) ((b).boughtIndex ((heads).enum ⟨c.1,BoughtLocation.relative c.2⟩))=_ at atBought
    rw [ident] at atBought
    let pair:=(originalEnds) ((b).boughtIndex u)
    have leftWord : ((b).bought.view chkUse (u.val:Word w)).left=((name) pair.1).val := by
      exact view.1.trans (loc.left.trans (congrArg (fun t : Site h D k × Site h D k=>(name t.1).val) atBought.symm))
    have rightWord : ((b).bought.view chkUse (u.val:Word w)).right=((name) pair.2).val := by
      exact view.2.trans (loc.right.trans (congrArg (fun t : Site h D k × Site h D k=>(name t.2).val) atBought.symm))
    let mount := (b).coreMount π.symm name edgeOrder chkUse
    have tailWord : mount.actual.tail ((b).boughtIndex u)=
        reportedSite name (min ((b).bought.view chkUse (u.val:Word w)).left ((b).bought.view chkUse (u.val:Word w)).right) :=
      (b).byKind_bought (fun j=>(name) (ends π.symm ((edgeOrder) j)).1)
        (fun j=>let rowView:=(b).bought.view chkUse (j.val:Word w);reportedSite name (min rowView.left rowView.right)) u
    have headWord : mount.actual.head ((b).boughtIndex u)=
        reportedSite name (max ((b).bought.view chkUse (u.val:Word w)).left ((b).bought.view chkUse (u.val:Word w)).right) :=
      (b).byKind_bought (fun j=>(name) (ends π.symm ((edgeOrder) j)).2)
        (fun j=>let rowView:=(b).bought.view chkUse (j.val:Word w);reportedSite name (max rowView.left rowView.right)) u
    change ((name) pair.1=_ ∧ (name) pair.2=_) ∨ ((name) pair.1=_ ∧ (name) pair.2=_)
    have tailAtEnd : H.afterMount.actual.tail ((b).boughtIndex u) =
        mount.actual.tail ((b).boughtIndex u) := internal.1
    have headAtEnd : H.afterMount.actual.head ((b).boughtIndex u) =
        mount.actual.head ((b).boughtIndex u) := internal.2
    rw [tailAtEnd,headAtEnd,tailWord,headWord,leftWord,rightWord]
    rcases le_total ((name) pair.1).val ((name) pair.2).val with forward|reverse
    · exact Or.inl ⟨by rw [min_eq_left forward,reportedSite_number],by rw [max_eq_right forward,reportedSite_number]⟩
    · exact Or.inr ⟨by rw [max_eq_left reverse,reportedSite_number],by rw [min_eq_right reverse,reportedSite_number]⟩

end FundedDate
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
