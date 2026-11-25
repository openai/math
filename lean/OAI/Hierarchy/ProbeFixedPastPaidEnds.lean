import OAI.Hierarchy.ProbeFixedWirePaidEnds
import OAI.Hierarchy.ProbeFixedPaidCausality

namespace OAI
/-! # Positive site endpoints for different branches with the same past -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "w" => Native.wordBits h D Native.copies
local notation "stock" => v.fixedTerminalStock P h width
local notation "C" => v.wideSignedChart h width stock
local notation "f" => v.nativeFormats P h width
local notation "r" => Fintype.card (Slots h D k)
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A))
local notation "start" => v.catalystStaticStart P h width
local notation "page" => v.wideSignedPage h width stock
local notation "owners" => sinkBank start cnt r (P).catalogue.rows
local notation "banks" => TerminalLayout.settlement page stock
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "recipe" => routeBanks start cnt r
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

local notation "ownerBank" => sinkBank start cnt r (P).catalogue.rows
local notation "paidO" => v.catalystPairOwners P h width
local notation "paidP" => v.catalystPairParity P h width
local notation "floor" => (A).endAddress v.mesh
local notation "who" => v.nativeBoards P h width
local notation "tree" => v.nativeTrees P h width
local notation "sink" => (P).catalogue.sink r banks (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) ownerBank

local notation "es" => events v.mesh
local notation "until" => fun e=>(A).base v.mesh e+(A).stride

local notation "rows" => (P).catalogue.rows
local notation "chk" => fun m=> checkedOut C floor m
local notation "memAt" => fun m j=> StockBound.state C m j
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (StripChart.header F who a).fieldTerm
  (StripChart.id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

local notation "B" => (P).catalogue
local notation "dir" => (P).routes.directory
local notation "heads" => (dir).header h D k v.sampler.degree v.depth
local notation "ports" => max (Fintype.card (StripDirectory.PayloadRole N k))
  (Fintype.card (StripDirectory.PurchasedRole v.depth k))

theorem past_paid_ends_of_birth (π : Equiv.Perm (Fin (2^h))) (other checked : Memory w)
    (word : floor<2^w) (jobs : v.wideJobs≤2^w) (original : (heads).Loaded checked)
    (j : ℕ) (same : PrefixAgreement.Low ((A).first+j*(A).stride) other checked)
    (e : Fin rows) (born : ∀u : Fin (B).boughtRows,(B).boughtIndex u=e→
      ∃p : Fin v.wideJobs,∃t : Fin (es).length,(es).get t=.attempt (v.sourceAttempt p) ∧
        t.val < j ∧ ∃z : Fin (heads).ports,(heads).enum ⟨p,z⟩=u) :
    let mount:=(B).coreMount π (siteNumber h D k) (v.wideOrder h width)
    (mount other).actual.tail e=(mount checked).actual.tail e ∧
      (mount other).actual.head e=(mount checked).actual.head e := by
  intro mount
  apply CatalogueRows.Board.paid_mount_ends
  intro u hu
  obtain ⟨p,t,date,past,z,id⟩:=born u hu
  have occurred : Event.attempt (v.sourceAttempt p)∈es:=date ▸ (es).get_mem t
  have pos : position v.mesh (.attempt (v.sourceAttempt p))=t.val:=by
    rw [←date,List.get_eq_getElem,position_at v.mesh t.isLt]
  have steps:=Nat.mul_le_mul_right (A).stride (show t.val+1 ≤ j from past)
  rw [Nat.add_mul,one_mul] at steps
  have low : PrefixAgreement.Low (until (.attempt (v.sourceAttempt p))) other checked:=by
    intro x hx
    change x < (A).first + position v.mesh (.attempt (v.sourceAttempt p)) * (A).stride + (A).stride at hx
    rw [pos] at hx
    exact same x (by omega)
  have eq:=v.wide_bought_view_low h width p z other checked low (((A).within v.mesh _ occurred).trans_lt word)
    original jobs
  simpa only [id] using eq

theorem wide_past_paid_ends :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh ≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits j,
        let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
        let mount:=((placed).catalogue).coreMount π (siteNumber h (2^v.W) k) (v.wideOrder h width)
        ∀other : Memory (Native.wordBits h (2^v.W) Native.copies),
          PrefixAgreement.Low ((arena).first+j*(arena).stride) other checked→
          ∀e : Fin (placed).catalogue.rows,0 < v.wirePaidAt h width bits j other e→
          (mount other).actual.tail e=(mount checked).actual.tail e ∧
          (mount other).actual.head e=(mount checked).actual.head e := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_past_agreement,v.wide_spill_core_only,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight,
    Filter.eventually_ge_atTop v.wideJobs] with h cash spill limit age dates
  intro width small budget placed arena paidStock paidOrder size extent π raw bits j checked mount other same e positive
  let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
  have sizes:=v.wide_stock_sizes h width age budget small
  have word:=sizes.words.addresses
  have live:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have boot:=v.wide_signed_boot_at h width size extent paidStock v.radius π paidOrder raw word
  have pub:=boot.2.2.2.1
  have header (a : Attempt) (_ : Event.attempt a∈events v.mesh) :=
    (v.terminal_port_header placed h width (Fintype.card (Slots h (2^v.W) k))
      (TerminalLayout.settlement (v.wideSignedPage h width paidStock) paidStock)
      (TerminalLayout.source (v.wideSignedPage h width paidStock)) (TerminalLayout.table (v.wideSignedPage h width paidStock))
      (TerminalLayout.destination (v.wideSignedPage h width paidStock))
      (sinkBank (v.catalystStaticStart placed h width)
        (rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards placed h width) v.mesh
          (placed).catalogue (placed).routes F arena))) (Fintype.card (Slots h (2^v.W) k)) (placed).catalogue.rows)
      a mid ((arena).endAddress v.mesh) pub live (Nat.le_add_right ..)).2
  have storage:=(v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first placed h width)
  let hh:=((placed).routes.directory).header h (2^v.W) k v.sampler.degree v.depth
  have lowHeader : hh.stop≤(arena).first:=(Nat.le_add_right ..).trans storage
  have directoryAt : hh.Loaded checked:=boot.2.2.1.board.rom.outer.frame (fun x _ hx=>
    v.wide_signed_checkout_below h width paidStock v.radius π paidOrder raw size x (hx.trans_le lowHeader) live)
  have cap:=(spill width small budget size extent π raw).2
  have changed:=cash width small budget size extent π raw bits j other (fun x hx=>(same x hx).symm)
  have active : 0 < v.wirePaidAt h width bits j checked e:=by rw [changed e];exact positive
  apply v.past_paid_ends_of_birth h width π other checked word
    (dates.trans ((Nat.lt_two_pow_self (n:=h)).le.trans (v.date_prefix_fit h).le)) directoryAt j same e
  intro u hu
  apply v.wire_born_in_prefix h width checked header word (limit width).1 sizes.roles cap bits j u
  rw [hu]
  exact active

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
