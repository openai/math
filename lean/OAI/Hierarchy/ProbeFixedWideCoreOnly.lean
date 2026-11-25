import OAI.Hierarchy.ProbeFixedWideSpillCases

namespace OAI
/-! # Core spill and feed instructions can never name a purchased archive row -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing

private theorem Reads_core_rows {w rows : ℕ} (b : Board) (t : Traversals) (m : Memory w)
    (walk : Fin rows → List (Fin b.rows)) (read : t.Reads m walk) (bound : ∀j e,e∈walk j → e.val<b.coreRows) :
    ∀i : Fin t.positions,(t.edge.eval m (i.val:Word w)).val<b.coreRows := by
  intro i
  rw [read.edgeAt i]
  exact bound (read.enum i).1 _ (List.getElem_mem (read.enum i).2.isLt)

namespace FixedProtocolFormat
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
section
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
local notation "recipe" => routeBanks (v.catalystStaticStart P h width) cnt r
local notation "order" => wideRouteOrder h D k
local notation "route" => source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "lay" => FeedLayout.atEvent («N»:=N) v.mesh A f (P).joint.initial width v.keepLimit

def CoreSpillRows (m : Memory w) : Prop :=
  (∀a,let t:=v.paidSpillPath P h width recipe route order a
      ∀i : Fin t.positions,(t.edge.eval m (i.val:Word w)).val<(P).catalogue.coreRows) ∧
  (∀b,∀c∈(lay b).columns,let t:=v.paidFeedPath P h width route lay b c
      ∀i : Fin t.positions,(t.edge.eval m (i.val:Word w)).val<(P).catalogue.coreRows)

private theorem WideSpillSource.only_core (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (source : v.WideSpillSource h width π m) (menu : Fintype.card (Actions N k)≤2^w)
    (goods : Fintype.card (Commodity (Fin (2^h)) N k)≤2^w)
    (lanes : ∀l : Fin (FeedLayout.lanes N k),laneWidth (decodeLane l)*2^h<2^w)
    (rows : (P).catalogue.rows≤2^w) : v.CoreSpillRows h width m := by
  let owner:=v.catalystPairOwners P h width
  let parity:=v.catalystPairParity P h width
  let ord:=v.wideOrder h width
  have hits (j : Commodity (Fin (2^h)) N k) (e : Fin (P).catalogue.rows) (member : e∈v.spillPath P h π ord j) :
      e.val<(P).catalogue.coreRows := by
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact (ord.symm a).isLt
  constructor
  · intro a t
    have reads:=v.spill_read P h width π ord m route source.1 recipe _ source.2 menu goods rows owner parity a
    exact Reads_core_rows (P).catalogue t m _ reads (fun j=>hits _)
  · intro b c member t
    obtain ⟨l,_,rfl⟩:=List.mem_map.mp member
    have reads:=v.boundary_read P h π ord m route source.1 (lay b) owner parity l (lanes l) rows
    exact Reads_core_rows (P).catalogue t m _ reads (fun j=>hits _)

end

/-- Both price clocks see only the assigned core edge at every emit operation,
including rows whose spill or boundary load is zero. -/
theorem wide_spill_core_only :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let chart:=v.wideSignedChart h width stock
      let order:=wideRouteOrder h (2^v.W) k
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let m:=v.wideSignedMidAt h width size stock v.radius π order raw
        v.CoreSpillRows h width (run chart (events v.mesh) m) ∧
          v.CoreSpillRows h width (v.wideSignedCheckoutAt h width size stock v.radius π order raw) := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight] with h words rows age
  intro width small budget P A stock chart order size extent π raw m
  have inventory:=v.wide_stock_at h width size extent v.radius π raw age budget small
  have source:=v.wide_spill_source h width size extent π raw (v.wide_stock_sizes h width age budget small).words.addresses
    inventory.mounted_all
  exact ⟨WideSpillSource.only_core v h width π _ source.1 words.1 words.2.1 words.2.2 (rows width).1.le,
    WideSpillSource.only_core v h width π _ source.2 words.1 words.2.1 words.2.2 (rows width).1.le⟩

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
