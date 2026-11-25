import OAI.Hierarchy.ProtocolRAMCatalystStripStoredOwners
import OAI.Hierarchy.ProtocolRAMCatalystDatedPorts

namespace OAI
/-! # Both physical ownership lookups on the actual chronological ledger -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical Fin.CommRing
namespace CatalystArchive
variable {k : ℕ}

/-- Every affirmative board selected from the original stock reads locates
the same typed path at its original DFS row in the padded rectangle. -/
theorem boughtBalls_relative {z d depth : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {marks : StageAt z d → Fin k × Bool → Finset (Fin (2^z))}
    {flag : Fin (PurchaseFrozen.count z d k * PurchaseFrozen.paths z S.degree depth) → Prop}
    (board : {i // flag i} ≃ LiveChains S π depth marks)
    (rows : ∀i,BoughtLocation.relative (board i)=i.val) (p : LiveChains S π depth marks) :
    boughtBalls flag board p = BoughtLocation.relative p := by
  change (board.symm p).val = BoughtLocation.relative p
  simpa only [Equiv.apply_symm_apply] using (rows (board.symm p)).symm

end CatalystArchive

namespace Calendar.StripChart
open CatalystArchive CatalogueRows StripDirectory BoughtSockets PurchaseFrozen
variable {z W k q depth w : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

abbrev datedOwnerWords (atTrial : Attempt) (base : ℕ) : Pass := ownerWords s c b G F atTrial base

theorem datedOwnerWords_eval (t : Attempt) (base : ℕ) (m : Memory w) (i : Fin (header F (withPorts s c b G) t).count) :
    (datedOwnerWords s c b G F t base).term.eval m (i.val:Word w) =
      ((datedOwnerWords s c b G F t base).apply m) (base+i.val) := by
  exact ownerWords_eval s c b G F t base m i

/-- The checkout scans the literal column/axis query of the originating
calendar attempt. Feed events have empty owner columns. -/
def ownerLedger (reserveArena : Arena) : OwnerLedger where
  arena := reserveArena
  rows
    | .attempt x => (header F (withPorts s c b G) x).count
    | .feed _ => 0
  term
    | .attempt x => (datedOwnerWords s c b G F x 0).term
    | .feed _ => .lit 0

theorem ledger_attempt (arena : Arena) (x : Attempt) (m : Memory w)
    (i : Fin (header F (withPorts s c b G) x).count) :
    ((ownerLedger s c b G F arena).term (.attempt x)).eval m (i.val:Word w) =
      ((datedOwnerWords s c b G F x 0).apply m) i.val := by
  change (datedOwnerWords s c b G F x 0).term.eval m (i.val : Word w) = _
  simpa only [Nat.zero_add] using datedOwnerWords_eval s c b G F x 0 m i

/-- The source term read at a positive payload occurrence, in the coordinates of the funding map. -/
theorem ledger_payload_rom (arena : Arena) (p a : ℕ) (π : Equiv.Perm (Fin (2^z)))
    (groups : Fin G.oldGroups ≃ AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups) (m : Memory w)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π m)
    (outputs : Native.Resident (Native.initialOutput z) m (fun x : Fin (2^z) => (π x).val))
    (fits : 2^z ≤ (header F (withPorts s c b G) (.outer p a)).rows)
    (loaded : (header F (withPorts s c b G) (.outer p a)).Loaded m) (room : D ≤ 2^w)
    (x : Fin (2^z) × (PayloadStrip.Columns N × Fin k)) :
    let ballsAt := payloadBalls z _ fits
    let slot := portCell (H:=Fin (PayloadStrip.edgeCount N)) (E:=PayloadStrip.Quotes N k ⊕ Empty)
      ballsAt (Nat.le_max_left P R) x
    ((ownerLedger s c b G F arena).term (.attempt (.outer p a))).eval m ((finProdFinEquiv slot).val:Word w) =
      ((pairKeys (CoreBoard.Columns z (2^W)) k (payloadPairs (d:=2^W) π x)).val:Word w) := by
  rcases x with ⟨r,col,axis⟩
  let head := header F (withPorts s c b G) (.outer p a)
  let occ := catalystOccurrence (H:=Fin (PayloadStrip.edgeCount N)) (E:=PayloadStrip.Quotes N k ⊕ Empty)
    head (Nat.le_max_left P R) (r.castLE fits) col axis
  exact (ownerWords_eval s c b G F (.outer p a) 0 m occ).trans
    (stored_payload_owner s c b G F π groups packed bins p a 0 m reports outputs (r.castLE fits)
      r.isLt col axis loaded room)

local notation "bits" => Native.wordBits z (2^W) Native.copies
local notation "strata" => count z (2^W) k
set_option quotPrecheck false in
local notation "perKey" => paths z s.sampler.degree depth

/-- The corresponding typed original-bought ROM, with its row equivalence
derived from the source flags and shelf CT in this event's RAM. -/
theorem ledger_purchased_rom (arena : Arena) (π : Equiv.Perm (Fin (2^z)))
    (groups : Fin G.oldGroups ≃ AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups) (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j t birthStock : ℕ)
    (phase : PhasePrice) (price : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z (2^W))
    (flags : StoredFlags ({(s.outer p.val a.val).market.shelf with stockBase := birthStock}) s.sampler π depth phase price kind frozen m k)
    (records : ∀i : Key z (2^W) k,ProtocolRAMPurchaseGateColumns.TileRows
      ((s.outer p.val a.val).market.shelf.L s.sampler depth i).source (Shelf.pathRows s.sampler π depth i) m)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π m)
    (keys : (stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase).Loaded m)
    (rooms : strata ≤ 2^bits ∧ (depth+1)*perKey ≤ 2^bits)
    (whole : strata*perKey ≤ 2^bits) (stock : PurchaseInventory.footprint z N k ≤ 2^bits)
    (loaded : (header F (withPorts s c b G) (.inner p.val a.val j t)).Loaded m) (room : D ≤ 2^bits) :
    let sh := {(s.outer p.val a.val).market.shelf with stockBase := birthStock}
    let marks := actualMarks sh phase price kind frozen (k:=k)
    let flag := fun i : Fin (strata*perKey) => (flagBank sh s.sampler z (2^W) k depth).read m (i.val:Word bits) ≠ 0
    ∃ board : {i // flag i} ≃ LiveChains s.sampler π depth marks,
      (∀ i,BoughtLocation.relative (board i)=i.val) ∧
      ∀ x : LiveChains s.sampler π depth marks × (ChainStrip.Columns depth × Fin k),
        let slot := portCell (H:=Fin (ChainStrip.edgeCount depth)) (E:=ChainStrip.Axes depth k ⊕ Unit)
          (boughtBalls flag board) (Nat.le_max_right P R) x
        ((ownerLedger s c b G F arena).term (.attempt (.inner p.val a.val j t))).eval m ((finProdFinEquiv slot).val:Word bits) =
          ((pairKeys (CoreBoard.Columns z (2^W)) k
            (paidPairs s.sampler π depth marks (actualMarks_unique sh phase price kind frozen) x)).val:Word bits) := by
  intro sh marks flag
  obtain ⟨board,rows,values⟩ := stored_purchased_owners s c b G F π groups packed bins p a j t 0 birthStock phase price
    kind frozen m flags records reports keys rooms whole stock loaded room
  refine ⟨board,rows,?_⟩
  rintro ⟨path,col,axis⟩
  let i := board.symm path
  let head := header F (withPorts s c b G) (.inner p.val a.val j t)
  let occ := catalystOccurrence (H:=Fin (ChainStrip.edgeCount depth)) (E:=ChainStrip.Axes depth k ⊕ Unit)
    head (Nat.le_max_right P R) i.val col axis
  have val := values i col axis
  have decoded : board i=path := board.apply_symm_apply path
  rw [decoded] at val
  exact (ownerWords_eval s c b G F (.inner p.val a.val j t) 0 m occ).trans val

end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
