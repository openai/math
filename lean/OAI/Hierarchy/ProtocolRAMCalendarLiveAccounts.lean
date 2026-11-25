import OAI.Hierarchy.ProtocolRAMCalendarLiveFormats
import OAI.Hierarchy.ProtocolRAMCalendarMountedScores
import OAI.Hierarchy.ProbeAccountQuotes

namespace OAI
/-! # Matching each stored test and repair quote to the actual predecessor stock -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe OuterBank ProbeStage ProbeStage.Native PurchaseCT
open scoped BigOperators Classical
variable {z d k q goods w N : ℕ}

section
variable (c : Mesh) (arena : Arena) (initial : ℕ) (build : Attempt→ℕ→Format z d k q goods)
    (capacity : ∀u addr,(build u addr).pricedArea=(build u initial).pricedArea)
    (addr : ∀u pc,(build u pc).market.shelf.stockBase=pc)

include capacity addr

theorem native_live_stock (payload : ℕ) (events : Event→WordRows) (cash a M beta : ℝ) (box : ℕ→ℝ)
    (u : Attempt) (i : Commodity (Fin (2^z)) N k) :
    let fm:=liveFormats c arena initial build
    let A:=nativeAccounts (N:=N) c arena fm initial payload events cash a M beta box
    A.stockAt u i=(fm u).market.shelf.stockBase+PurchaseInventory.slot i :=
  live_stock c arena initial build capacity addr u i

/-- A repair or reserve-replay price query made by the dynamically placed
strip is at the same physical bank used by the signed economic receipt. -/
theorem native_live_quotes (payload precision : ℕ) (events : Event→WordRows) (cash a M W T s : ℝ)
    (u : Attempt) (snapshot : Memory w) :
    let fm:=liveFormats c arena initial build
    let N:=CoreBoard.Stages z d
    let A:=nativeAccounts (N:=N) c arena fm initial payload events cash a M (W⁻¹^4/(N*T^2)) (routeCap N M)
    maximizer A.a A.M s A.coefficient A.box (A.bank.units payload (A.read u snapshot))=
      stageQuotes (publicPhase (2*rounds d+1) a M W T s payload precision) 0 1 (fm u).market.shelf.stockBase snapshot := by
  have quote:=native_account_quotes c arena (liveFormats c arena initial build) initial payload precision events cash a M W T s u snapshot
  dsimp only at quote ⊢
  rw [live_published c arena initial build capacity] at quote
  simpa only [liveFormats,addr,resolvedStock] using quote
end

/-- The native integer low/high comparator now reads the same storage base
as the phase's entire signed stock. All bounds are independent public slots
or the actual capped stock invariant. -/
theorem GlobalTests.live_outer_words (C : Chart w q goods) (arena : Arena) (initial : ℕ)
    (build : Attempt→ℕ→Format z d k q goods)
    (capacity : ∀u addr,(build u addr).pricedArea=(build u initial).pricedArea)
    (address : ∀u pc,(build u pc).market.shelf.stockBase=pc)
    (payload : ℕ) (events : Event→WordRows) (cash a M beta : ℝ) (box : ℕ→ℝ)
    (s : PhasePrice) (l : GlobalTests.Layout) (p j : ℕ) (boot : Memory w)
    (start : GlobalTests.Resident l z N k s boot) (whole : Calendar.mounted C (Calendar.events C.mesh) boot)
    (hp : p<C.mesh.inject+C.mesh.cool) (hj : j<C.mesh.outerFuel)
    (fixed : ∀ev∈Calendar.events C.mesh,∀u,l.base≤u→u<GlobalTests.stop l z N k→protected C u ev)
    (rowsFit : GlobalTests.rows z N k<2^w) (indices : GlobalTests.rows z N k≤2^l.indexBits)
    (spanFit : GlobalTests.span l N k<2^w) (tableCap : GlobalTests.span l N k≤2^l.indexBits)
    (limit : let fm:=liveFormats C.mesh arena initial build
      let A:=nativeAccounts (N:=N) C.mesh arena fm initial payload events cash a M beta box
      ∀i,(A.trial C boot p j).bits i<l.stride) (unitFits : GlobalTests.unitBound l N k s<2^w)
    (aPos : 0<s.a) (bPos : ∀i<GlobalTests.kinds N k,0≤ s.bonus i) (mPos : 0≤ s.M)
    (tPos : 0<s.time) (cPos : ∀i<GlobalTests.kinds N k,0≤ s.cap i) :
    let fm:=liveFormats C.mesh arena initial build
    let A:=nativeAccounts (N:=N) C.mesh arena fm initial payload events cash a M beta box
    let input : Bank:=⟨(fm (.outer p j)).market.shelf.stockBase,l.indexBits⟩
    GlobalTests.ReadStock A (A.trial C boot p j) l input s (trialState C boot p j) := by
  exact GlobalTests.ReadStock.at_trial _ C boot l _ s p j start whole hp hj fixed
    (native_live_stock C.mesh arena initial build capacity address payload events cash a M beta box (.outer p j))
    rowsFit indices indices spanFit tableCap limit unitFits aPos bPos mPos tPos cPos

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
