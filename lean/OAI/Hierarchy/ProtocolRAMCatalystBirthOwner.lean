import OAI.Hierarchy.ProtocolRAMCatalystStripLedgerReads
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners
import OAI.Hierarchy.ProtocolRAMStoredColumnFits
import OAI.Hierarchy.ProtocolRAMPurchaseAllocation

namespace OAI
/-! # Localizing the owner decoder to the public originating trial -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets PurchaseFrozen
open scoped Classical Fin.CommRing

namespace CatalystArchive
open Calendar ColumnWires
variable {C H E : Type*} [Fintype C] [Fintype H] [Fintype E] {w limit k : ℕ}

theorem ownerPass_fits (base : ℕ) (h : StockCommit.PortHeader) (column : C → Expr)
    (word : limit < 2^w) (top : h.stop ≤ limit) (cells : ∀c,(column c).Fits w limit) :
    (ownerPass (D:=h.ports) (H:=H) (E:=E) (k:=k) base h.count column h.fieldTerm h.ballTerm).term.Fits w limit := by
  have address : h.start+2*h.small+2*h.large≤limit := by
    simp only [StockCommit.PortHeader.stop, StockCommit.PortHeader.parity, StockCommit.PortHeader.owner] at top
    omega
  have safe (b : Bank) (endAt : b.base+b.size≤limit) : b.Fits w limit := ⟨Nat.two_pow_pos _,by omega,endAt⟩
  have ball : h.ballTerm.Fits w limit := ⟨safe _ (by change h.start+h.small≤limit; omega),trivial⟩
  have field : h.fieldTerm.Fits w limit := ⟨safe _ (by change h.start+h.small+h.small≤limit; omega),trivial⟩
  have mul (n : ℕ) (x : Expr) (fit : x.Fits w limit) : (scale n x).Fits w limit := by
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨fit,ih⟩
  have table (r : Role C H E k) : (ownerExpr column r).Fits w limit := by
    cases r with
    | catalyst c j => exact ⟨trivial,mul k _ (cells c)⟩
    | radius | cross | horizontal | extra => trivial
  apply choose_fits_bound _ _ _ _ _ field
  intro i
  unfold PortPadding.extend
  split
  · exact CatalogueRows.fits_atRow _ _ (table _) ball
  · trivial

end CatalystArchive

namespace Calendar.StripChart
open CatalogueRows StripDirectory
variable {z W k q depth w limit : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

/-- The originating calendar site is public. Its candidate ordinal enters
the same stratum selector that the full birth dispatch would select. -/
def birthColumn (p a : ℕ) (col : ChainStrip.Columns depth) : Expr :=
  G.directory.eventPosition (s.outer p a).market.shelf G.column s.sampler z W k depth G.oldGroups G.bins G.height
    (chainPosition depth col) (decide (col.val.val%2=1))

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
/-- Equality on the entire originating candidate rectangle, including rows
whose entered bit is zero. No such bit enters the decoder. -/
theorem birthColumn_eval (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (m : Memory w)
    (_shelf : G.directory.shelf (finProdFinEquiv (p,a))=(s.outer p.val a.val).market.shelf)
    (_loaded : (G.directory.header z (2^W) k s.sampler.degree depth).Loaded m)
    (_room : (c.inject+c.cool)*c.outerFuel ≤ 2^w)
    (r : Fin (count z (2^W) k * paths z s.sampler.degree depth)) (col : ChainStrip.Columns depth) :
    ((boughtPortsAt s c b G p.val a.val).column col).eval m (r.val:Word w) =
      (birthColumn s c G p.val a.val col).eval m (r.val:Word w) := by
  rfl

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
theorem birthColumn_fits (p a : ℕ) (col : ChainStrip.Columns depth) (word : limit < 2^w)
    (tab : G.column+ColumnROM.words z (2^W) k ≤ limit)
    (cover : ColumnROM.Cover z W G.directory.remapBase G.directory.sitesBase G.directory.superBase
      G.oldGroups G.bins G.height limit)
    (keys : (stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase).stop ≤ limit)
    (source : ∀i : Key z (2^W) k,((s.outer p a).market.shelf.L s.sampler depth i).endAddress ≤ limit) :
    (birthColumn s c G p a col).Fits w limit := by
  apply BoughtSockets.select_fits _ _ word keys
  intro i
  apply ColumnROM.stage_fits_cols _ _ _ _ _ _ _ _ _ _ _ word tab cover
  let L := (s.outer p a).market.shelf.L s.sampler depth i
  have ⟨_,_,_,_,_,so,ga,pa,en⟩ := L.regions
  have high : L.endAddress ≤ limit := source i
  have off : L.source.base+L.source.size ≤ limit := by omega
  have bank : L.source.Fits w limit := ⟨Nat.two_pow_pos _,by omega,off⟩
  exact ⟨bank,trivial,trivial⟩

/-- The prior trial reads one bounded source shelf for each row of its original stratum. -/
def BirthBankFits (s : Boards z (2^W) k q depth) (keyBase limit : ℕ) : Attempt → Prop
  | .outer .. => True
  | .inner p a _ _ =>
    (stratumHeader z (2^W) k s.sampler.degree depth keyBase).stop ≤ limit ∧
      ∀i : Key z (2^W) k,((s.outer p a).market.shelf.L s.sampler depth i).endAddress ≤ limit

set_option maxHeartbeats 2400000 in
/-- The eventual frame bound needs only the source bank of the actual birth
and the fixed public column ROM. -/
theorem datedOwnerWords_fits (t : Attempt) (base : ℕ) (word : limit < 2^w)
    (tab : G.column+ColumnROM.words z (2^W) k ≤ limit)
    (cover : ColumnROM.Cover z W G.directory.remapBase G.directory.sitesBase G.directory.superBase
      G.oldGroups G.bins G.height limit)
    (top : (header (z:=z) (d:=2^W) (k:=k) (q:=q) (depth:=depth) F
      (withPorts (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G) t).stop ≤ limit)
    (localBanks : BirthBankFits (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s G.directory.keysBase limit t) :
    (datedOwnerWords (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G F t base).term.Fits w limit := by
  cases t with
  | outer p a =>
    apply CatalystArchive.ownerPass_fits _ _ _ word top
    intro col
    exact ColumnROM.payload_fits_cols _ _ _ _ _ _ _ _ _ word tab cover
  | inner p a j r =>
    apply CatalystArchive.ownerPass_fits _ _ _ word top
    intro col
    exact birthColumn_fits s c G p a col word tab cover localBanks.1 localBanks.2

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
