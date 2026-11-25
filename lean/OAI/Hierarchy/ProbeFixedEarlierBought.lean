import OAI.Hierarchy.ProbeFixedWirePaidEnds
import OAI.Hierarchy.ProbeFixedWideHistorySupported

namespace OAI
/-! # Earlier positive birth and surviving flag of an original paid edge -/
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
local notation "stamp" => fun a=>(f a).labelSource sink (P).catalogue.idBase (header F who a).fieldTerm
  (id F who (P).catalogue a)
local notation "regular" => fun a=> PaidWidths.paidDirect (f a).pricedArea (f a).stockSource (stamp a)
local notation "secondary" => fun a u v'=> PaidWidths.paidMate (f a).pricedArea (f a).stockSource u v'
local notation "broadcasting" => fun (bits : ℕ) a=> PaidWidths.paidBroadcast (f a).pricedArea
  (tree a).positions (tree a).owner (tree a).parity (tree a).edge (tree a).sourceRow (f a).board.batch.copies bits

local notation "B" => (P).catalogue
local notation "dir" => (P).routes.directory
local notation "heads" => (dir).header h D k v.sampler.degree v.depth
local notation "ports" => max (Fintype.card (StripDirectory.PayloadRole N k))
  (Fintype.card (StripDirectory.PurchasedRole v.depth k))

theorem wire_bought_earlier_active :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits,
      let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
      let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
      let cal:=v.wideSignedChart h width paidStock
      let table:=(placed).routes.directory.header h (2^v.W) k v.sampler.degree v.depth
      ∀t : Fin (events v.mesh).length,∀u : Fin (placed).catalogue.boughtRows,
        0<v.wirePaidAt h width bits (t.val+1) (StockBound.state cal mid (t.val+1)) ((placed).catalogue.boughtIndex u)→
        ∃p : Fin v.wideJobs,∃b : Fin (events v.mesh).length,∃rel : Fin table.ports,
          b.val<t.val ∧ (events v.mesh).get b=.attempt (v.sourceAttempt p) ∧ table.enum ⟨p,rel⟩=u ∧
            (placed).catalogue.bought.flag.eval checked (u.val:Word (Native.wordBits h (2^v.W) Native.copies))≠0 := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_wire_paid,v.wide_spill_core_only,v.wide_row_room,v.wide_history_supported,
    Filter.eventually_ge_atTop v.wideStockHeight] with h cash spill limit alive age
  intro width small budget placed arena paidStock paidOrder size extent π raw bits mid checked cal table t u positive
  have sizes:=v.wide_stock_sizes h width age budget small
  have word:=sizes.words.addresses
  have live:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  obtain ⟨_,_,_,pub,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent paidStock v.radius π paidOrder raw word
  have header (a : Attempt) (_ : Event.attempt a∈events v.mesh) :=
    (v.terminal_port_header placed h width (Fintype.card (Slots h (2^v.W) k))
      (TerminalLayout.settlement (v.wideSignedPage h width paidStock) paidStock)
      (TerminalLayout.source (v.wideSignedPage h width paidStock)) (TerminalLayout.table (v.wideSignedPage h width paidStock))
      (TerminalLayout.destination (v.wideSignedPage h width paidStock))
      (sinkBank (v.catalystStaticStart placed h width)
        (rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards placed h width) v.mesh
          (placed).catalogue (placed).routes F arena))) (Fintype.card (Slots h (2^v.W) k)) (placed).catalogue.rows)
      a mid ((arena).endAddress v.mesh) pub live (Nat.le_add_right ..)).2
  have cap:=(spill width small budget size extent π raw).2
  have changed:=(cash width small budget size extent π raw bits).1
  have born:=v.wire_born_before_charge h width checked header word (limit width).1 sizes.roles cap bits (t.val+1)
  have positive':0<v.wirePaidAt h width bits (t.val+1) checked ((placed).catalogue.boughtIndex u):=by
    rw [←changed (t.val+1) t.isLt];exact positive
  obtain ⟨p,b,date,past,rel,which⟩:=born u positive'
  refine ⟨p,b,rel,by omega,date,which,?_⟩
  have supported:=(alive width small budget size extent π raw bits).2
  intro dormant
  apply Nat.ne_of_gt positive'
  apply (placed).catalogue.no_dormant_load _ checked u _ dormant
  intro s included
  obtain ⟨e,taken,member⟩:=List.mem_flatMap.mp included
  exact supported e (List.take_subset (t.val+1) _ taken) s member

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
