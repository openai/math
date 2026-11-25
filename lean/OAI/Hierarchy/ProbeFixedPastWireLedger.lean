import OAI.Hierarchy.ProbePaidChordWeights
import OAI.Hierarchy.ProbeFixedPastPaidEnds

namespace OAI
/-! # The signed graph before a future selector extension -/
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

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor

theorem wide_prestate_low (size : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
    (M : ℕ) (j : ℕ) (bounded : j≤(es).length) :
    let m:=v.wideSignedMidAt h width size stock M π order raw
    Calendar.mounted C es m→PrefixAgreement.Low ((A).first+j*(A).stride)
      (StockBound.state C m j) (v.wideSignedCheckoutAt h width size stock M π order raw) := by
  intro m active
  cases j with
  | zero =>
    intro x hx
    have first : x<(A).first:=by simpa using hx
    exact (v.wide_signed_checkout_below h width stock M π order raw size x first active).symm
  | succ i =>
    let t : Fin (es).length:=⟨i,bounded⟩
    have held:=v.prior_paid_low h width m active t (i+1) (Nat.lt_succ_self _) bounded
    have pos : position v.mesh ((es).get t)=i:=by
      rw [List.get_eq_getElem,position_at v.mesh t.isLt]
    intro x hx
    have fit : x < until ((es).get t) := by
      change x<(A).first+position v.mesh ((es).get t)*(A).stride+(A).stride
      simpa only [pos,Nat.add_mul,one_mul,Nat.add_assoc] using hx
    exact (held x fit).symm

/-- Future selector words may differ arbitrarily. The genuine prior native
paid graph and catalyst stock use only memory below the current cut. This
form admits an independent identification of the held commodity balances. -/
theorem wide_past_wireAt :
    ∀ᶠ h : ℕ in Filter.atTop,∀width,width≤2^h→v.keepLimit*width+1≤2^h→
      let placed:=v.widePlacement h width
      let arena:=v.privateArena placed h width
      let paidStock:=v.fixedTerminalStock placed h width
      let paidOrder:=wideRouteOrder h (2^v.W) k
      ∀size,(arena).endAddress v.mesh≤ size→∀(π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) bits j,
        let mid:=v.wideSignedMidAt h width size paidStock v.radius π paidOrder raw
        let cal:=v.wideSignedChart h width paidStock
        let prior:=StockBound.state cal mid j
        j≤(events v.mesh).length→∀other : Memory (Native.wordBits h (2^v.W) Native.copies),
        PrefixAgreement.Low ((arena).first+j*(arena).stride) other prior→
        v.wireGoodsAt h width j other=v.wireGoodsAt h width j prior→
        v.wireAt h width bits π j other=v.wireAt h width bits π j prior := by
  filter_upwards [v.wide_past_agreement,v.wide_past_paid_ends,Filter.eventually_ge_atTop v.wideStockHeight] with h cost ends age
  intro width small budget placed arena paidStock paidOrder size extent π raw bits j mid cal prior last other low goods
  let checked:=v.wideSignedCheckoutAt h width size paidStock v.radius π paidOrder raw
  let bound:=(arena).first+j*(arena).stride
  let mount:=((placed).catalogue).coreMount («w» := Native.wordBits h (2^v.W) Native.copies) π (siteNumber h (2^v.W) k) (v.wideOrder h width)
  have live:=(v.wide_stock_at h width size extent v.radius π raw age budget small).mounted_all
  have original:=v.wide_prestate_low h width size π raw v.radius j last live
  have both : PrefixAgreement.Low bound other checked:=fun x hx=>(low x hx).trans (original x hx)
  have captured:=cost width small budget size extent π raw bits j
  have eq : v.wirePaidAt h width bits j other=v.wirePaidAt h width bits j prior:=by
    funext e
    exact (captured other (fun x hx=>(both x hx).symm) e).symm.trans
      (captured prior (fun x hx=>(original x hx).symm) e)
  have views:=ends width small budget size extent π raw bits j
  have paid:=(positive_chords (mount other).actual (mount prior).actual (v.wirePaidAt h width bits j other)
    (fun e pos=>by
      have bound':=views other both e pos
      have pos':0<v.wirePaidAt h width bits j prior e:=by rw [←eq];exact pos
      have final':=views prior original e pos'
      exact ⟨bound'.1.trans final'.1.symm,bound'.2.trans final'.2.symm⟩))
  have word:=(v.wide_stock_sizes h width age budget small).words.addresses
  have saved : v.wireUsedAt h width j other=v.wireUsedAt h width j prior:=
    funext (v.past_reserve_agreement h width other prior word j low)
  dsimp only [wireAt]
  rw [paid,eq,goods,saved]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
