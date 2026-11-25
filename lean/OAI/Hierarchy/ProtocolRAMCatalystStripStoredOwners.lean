import OAI.Hierarchy.ProtocolRAMStoredMarkFlags
import OAI.Hierarchy.ProtocolRAMCatalystLiveOwners
import OAI.Hierarchy.ProtocolRAMCatalystOwnerWords
import OAI.Hierarchy.ProtocolRAMCalendarStripPortBanks
import OAI.Hierarchy.ProbePurchaseSockets

namespace OAI
/-! # Reserve-owner words computed by the mounted outer and purchased strip ROMs -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets PurchaseFrozen
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
namespace CatalystArchive

variable {C H E G : Type*} [Fintype C] [Fintype H] [Fintype E] [Fintype G] {k w : ℕ}
local notation "Roles" => ColumnWires.Role C H E k

/-- Physical occurrence of one local catalyst role in the padded row table. -/
def catalystOccurrence (head : Calendar.StockCommit.PortHeader) (limit : Fintype.card Roles ≤ head.ports)
    (row : Fin head.rows) (c : C) (axis : Fin k) : Fin head.count :=
  head.enum ⟨row,PortPadding.inject limit ((Fintype.equivFin Roles) (.catalyst c axis))⟩

theorem catalystOccurrence_cell {A : Type*} (head : Calendar.StockCommit.PortHeader)
    (limit : Fintype.card Roles ≤ head.ports) (ballsAt : A ↪ Fin head.rows) (x : A × (C × Fin k)) :
    catalystOccurrence head limit (ballsAt x.1) x.2.1 x.2.2 =
      finProdFinEquiv (portCell (H:=H) (E:=E) ballsAt limit x) := rfl

theorem payloadPairs_column {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h))
    (col : PayloadStrip.Columns (Stages h d)) (axis : Fin k) :
    payloadPairs (d:=d) π (p,(col,axis))=(payloadPlace π p col,axis) := rfl

theorem paidPairs_column {h d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : StageAt h d → Fin k × Bool → Finset (Fin (2^h)))
    (unique : ∀ t j j' x,x∈marks t j → x∈marks t j' → j=j')
    (p : LiveChains S π depth marks) (col : ChainStrip.Columns depth) (axis : Fin k) :
    paidPairs S π depth marks unique (p,(col,axis)) =
      (.inr (.inl (allStripColumns S π depth marks unique (p,col))),axis) := rfl

/-- The column embedding supplied to the signed-cash entry for a purchased
strip. Its pair-with-axis embedding is the physical reserve owner's. -/
def paidColumns {h d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : StageAt h d → Fin k × Bool → Finset (Fin (2^h)))
    (unique : ∀ t j j' x,x∈marks t j → x∈marks t j' → j=j') :
    LiveChains S π depth marks × ChainStrip.Columns depth ↪ PayloadColumns h d :=
  (allStripColumns S π depth marks unique).trans
    ⟨fun c => .inr (.inl c),fun _ _ eq => Sum.inl.inj (Sum.inr.inj eq)⟩

theorem physical_paidColumns {h d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : StageAt h d → Fin k × Bool → Finset (Fin (2^h)))
    (unique : ∀ t j j' x,x∈marks t j → x∈marks t j' → j=j') :
    physical (k:=k) (paidColumns S π depth marks unique) = paidPairs S π depth marks unique := rfl

theorem stored_role_owner (base : ℕ) (column : C → Expr) (head : Calendar.StockCommit.PortHeader)
    (limit : Fintype.card Roles ≤ head.ports) (row : Fin head.rows) (c : C) (axis : Fin k)
    (mem : Memory w) (loaded : head.Loaded mem) (room : head.ports ≤ 2^w) (g : G)
    (placed : (column c).eval mem (row.val:Word w) = (((Fintype.equivFin G) g).val:Word w)) :
    ((ownerPass (D:=head.ports) (H:=H) (E:=E) (k:=k) base head.count column head.fieldTerm head.ballTerm).apply mem)
      (base+(catalystOccurrence head limit row c axis).val) = ((pairKeys G k (g,axis)).val:Word w) := by
  let role := PortPadding.inject limit ((Fintype.equivFin Roles) (.catalyst c axis))
  have read := StripDirectory.header_pair head mem loaded row role
  have hit : (head.fieldTerm.eval mem ((head.enum ⟨row,role⟩).val:Word w)).val =
      ((Fintype.equivFin Roles) (.catalyst c axis)).val := by
    rw [read.2,Fin.val_cast_of_lt (role.isLt.trans_le room)]
    rfl
  exact stored_owner base head.count column head.fieldTerm head.ballTerm mem (head.enum ⟨row,role⟩)
    limit room c axis g hit (by rw [read.1]; exact placed)

end CatalystArchive
namespace Calendar.StripChart
open CatalogueRows StripDirectory
variable {z W k q depth w : ℕ}
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def ownerWords (atTrial : Attempt) (base : ℕ) : Pass :=
  let head := header F (withPorts s c b G) atTrial
  match atTrial with
  | .outer .. => CatalystArchive.ownerPass (D:=(max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k)))) (H:=Fin (PayloadStrip.edgeCount (Stages z (2^W))))
      (E:=PayloadStrip.Quotes (Stages z (2^W)) k ⊕ Empty) (k:=k) base head.count (payloadPortsAt s c G).column
      head.fieldTerm head.ballTerm
  | .inner p a _ _ => CatalystArchive.ownerPass (D:=(max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k)))) (H:=Fin (ChainStrip.edgeCount depth))
      (E:=ChainStrip.Axes depth k ⊕ Unit) (k:=k) base head.count (boughtPortsAt s c b G p a).column
      head.fieldTerm head.ballTerm

theorem ownerWords_eval (atTrial : Attempt) (base : ℕ) (m : Memory w)
    (i : Fin (header F (withPorts s c b G) atTrial).count) :
    (ownerWords s c b G F atTrial base).term.eval m (i.val:Word w) =
      ((ownerWords s c b G F atTrial base).apply m) (base+i.val) := by
  cases atTrial <;> exact (ProtocolRAMGeneratedWrite.read_image ..).symm

variable (π : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups ≃ AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)
    (bins : G.bins=packed.groups)

include bins in
/-- Each entered outer row lies in the original source-port prefix. -/
theorem stored_payload_owner (p a base : ℕ) (m : Memory w)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π m)
    (outputs : Native.Resident (Native.initialOutput z) m (fun x : Fin (2^z) => (π x).val))
    (row : Fin (header F (withPorts s c b G) (.outer p a)).rows) (enters : row.val < 2^z)
    (col : PayloadStrip.Columns (Stages z (2^W))) (axis : Fin k)
    (loaded : (header F (withPorts s c b G) (.outer p a)).Loaded m) (room : (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))) ≤ 2^w) :
    let head := header F (withPorts s c b G) (.outer p a)
    let r := CatalystArchive.catalystOccurrence (H:=Fin (PayloadStrip.edgeCount (Stages z (2^W))))
      (E:=PayloadStrip.Quotes (Stages z (2^W)) k ⊕ Empty) head (Nat.le_max_left (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))) row col axis
    ((ownerWords s c b G F (.outer p a) base).apply m) (base+r.val) =
      ((CatalystArchive.pairKeys (CoreBoard.Columns z (2^W)) k (payloadPlace π ⟨row.val,enters⟩ col,axis)).val:Word w) := by
  dsimp only
  apply CatalystArchive.stored_role_owner base (payloadPortsAt s c G).column _ _ row col axis m loaded room
  have read := payload_column s.sampler G.core G.column G.directory.remapBase G.directory.sitesBase
    G.directory.superBase groups packed π m reports outputs ⟨row.val,enters⟩ col
  simpa only [payloadPortsAt,bins,ColumnROM.number] using read

include bins in
omit [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2 ^ W))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
/-- The purchased column instruction consumes one original tile from the
selected birth. Neither gates nor inverse path reconstruction enter this read. -/
theorem bought_column_tiles (p a : ℕ)
    (marks : StageAt z (2^W) → Fin k × Bool → Finset (Fin (2^z)))
    (path : LiveChains s.sampler π depth marks) (m : Shelf.Mem z (2^W)) (col : ChainStrip.Columns depth)
    (unique : ∀ t j j' x,x ∈ marks t j → x ∈ marks t j' → j=j')
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π m)
    (keys : (stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase).Loaded m)
    (cells : ProtocolRAMPurchaseGateColumns.TileRows ((s.outer p a).market.shelf.L s.sampler depth
      (BoughtLocation.keyOf path)).source (Shelf.pathRows s.sampler π depth (BoughtLocation.keyOf path)) m)
    (rooms : let w := Native.wordBits z (2^W) Native.copies
      count z (2^W) k ≤ 2^w ∧ (depth+1)*paths z s.sampler.degree depth ≤ 2^w) :
    ((boughtPortsAt s c b G p a).column col).eval m ((BoughtLocation.relative path).val:Word _) =
      (ColumnROM.number (.inr (.inl (allStripColumns s.sampler π depth marks unique (path,col)))):Word _) := by
  let sh := (s.outer p a).market.shelf
  let h := stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase
  let i := BoughtLocation.keyOf path
  let r := BoughtLocation.localRow path
  let pos := chainPosition depth col
  let side := decide (col.val.val%2=1)
  let parts := fun i : Key z (2^W) k => ColumnROM.stageColumn G.column G.directory.remapBase
    G.directory.sitesBase G.directory.superBase G.oldGroups packed.groups G.height k ((c.inject+c.cool)*c.outerFuel)
    (stage i) side (readTile sh s.sampler depth i pos)
  have header := header_pair h m keys i r
  have hi := BoughtSockets.select_read h parts m ((h.enum ⟨i,r⟩).val:Word _) (r.val:Word _) i rooms.1
    (by rw [header.1,Fin.val_cast_of_lt (i.isLt.trans_le rooms.1)]) header.2
  let q₀ := BoughtLocation.localIndex path
  have line : (readTile sh s.sampler depth i pos).eval m (q₀.val:Word _) =
      ((Shelf.pathRows s.sampler π depth i q₀ pos).val:Word _) := by
    unfold readTile
    rw [show paths z s.sampler.degree depth=(PurchaseDFS.layout (2^z) s.sampler.degree depth).length by simp [PurchaseFrozen.paths]]
    exact tile_read _ _ _ cells (ProtocolRAMPurchaseSampler.lt_span _).le (by simpa [PurchaseFrozen.paths] using rooms.2) q₀ pos
  rw [show Shelf.pathRows s.sampler π depth i q₀ pos=(liveRow s.sampler π depth marks path pos).castSucc
    from BoughtLocation.rows path pos] at line
  have stageRead := ColumnROM.stage_read _ _ _ _ groups packed π m reports (stage i) side (readTile sh s.sampler depth i pos)
    (q₀.val:Word _) (liveRow s.sampler π depth marks path pos) line
  rw [allStripColumns_single]
  have measured := hi.trans stageRead
  have ordinal : h.enum ⟨i,r⟩=BoughtLocation.relative path := rfl
  rw [ordinal] at measured
  have place := chain_chosenColumn s.sampler π depth marks path col
  simpa only [boughtPortsAt,purchasePorts,bins,BoughtSockets.Directory.eventPosition,parts,sh,pos,side,
    i,r,q₀,BoughtLocation.localRow,BoughtLocation.keyOf,stage_key,place] using measured

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2 ^ W))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
/-- The two endpoint columns of the very same ROM specialize to the
purchased sockets, including for a one-tile chain. -/
theorem bought_socket (marks : StageAt z (2^W) → Fin k × Bool → Finset (Fin (2^z)))
    (unique : ∀ t j j' x,x ∈ marks t j → x ∈ marks t j' → j=j')
    (path : LiveChains s.sampler π depth marks) (side : Bool) :
    allStripColumns s.sampler π depth marks unique (path,probeEnds depth side) =
      purchaseSockets s.sampler π depth marks unique (path,side) := rfl

local notation "bits" => Native.wordBits z (2^W) Native.copies
local notation "strata" => count z (2^W) k
local notation "perKey" => paths z s.sampler.degree depth

include bins in
/-- Every affirmative original ball, at every catalyst column and axis,
writes the owner of that same physical strip into the receiver archive. -/
theorem stored_purchased_owners (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel)
    (j t base birthStock : ℕ)
    (phase : PhasePrice) (price : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z (2^W))
    (flags : StoredFlags ({(s.outer p.val a.val).market.shelf with stockBase := birthStock}) s.sampler π depth phase price kind frozen m k)
    (records : ∀ i : Key z (2^W) k, ProtocolRAMPurchaseGateColumns.TileRows
      ((s.outer p.val a.val).market.shelf.L s.sampler depth i).source (Shelf.pathRows s.sampler π depth i) m)
    (reports : ColumnROM.Tables z W k ((c.inject+c.cool)*c.outerFuel) G.column G.directory.remapBase
      G.directory.sitesBase G.directory.superBase groups packed π m)
    (keys : (stratumHeader z (2^W) k s.sampler.degree depth G.directory.keysBase).Loaded m)
    (rooms : strata ≤ 2^bits ∧ (depth+1)*perKey ≤ 2^bits)
    (whole : strata*perKey ≤ 2^bits)
    (stock : PurchaseInventory.footprint z (Stages z (2^W)) k ≤ 2^bits)
    (loaded : (header F (withPorts s c b G) (.inner p.val a.val j t)).Loaded m)
    (room : (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))) ≤ 2^bits) :
    let marks := actualMarks ({(s.outer p.val a.val).market.shelf with stockBase := birthStock}) phase price kind frozen (k:=k)
    let flag := flagBank (s.outer p.val a.val).market.shelf s.sampler z (2^W) k depth
    let Active := {i : Fin (strata*perKey) // flag.read m (i.val:Word bits) ≠ 0}
    ∃ board : Active ≃ LiveChains s.sampler π depth marks, (∀ i,BoughtLocation.relative (board i)=i.val) ∧
      ∀ (i : Active) (col : ChainStrip.Columns depth) (axis : Fin k),
        let head := header F (withPorts s c b G) (.inner p.val a.val j t)
        let occ := CatalystArchive.catalystOccurrence (H:=Fin (ChainStrip.edgeCount depth))
          (E:=ChainStrip.Axes depth k ⊕ Unit) head (Nat.le_max_right (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k))) i.val col axis
        let surface := allStripColumns s.sampler π depth marks
          (actualMarks_unique ({(s.outer p.val a.val).market.shelf with stockBase := birthStock}) phase price kind frozen) (board i,col)
        ((ownerWords s c b G F (.inner p.val a.val j t) base).apply m) (base+occ.val) =
          ((CatalystArchive.pairKeys (CoreBoard.Columns z (2^W)) k (.inr (.inl surface),axis)).val:Word bits) := by
  intro marks flag Active
  let sh := {(s.outer p.val a.val).market.shelf with stockBase := birthStock}
  have wide : 0 < bits := by unfold Native.wordBits; omega
  obtain ⟨board,rows,_⟩ := liveBoardEquiv_relative sh s.sampler π depth G.directory.keysBase s.positive
    phase price kind frozen m records flags keys rooms.1 rooms.2 whole wide stock
  refine ⟨board,rows,?_⟩
  intro i col axis
  dsimp only
  apply CatalystArchive.stored_role_owner base (boughtPortsAt s c b G p.val a.val).column _ _
    i.val col axis m loaded room
  have value := bought_column_tiles s c b G π groups packed bins p.val a.val marks (board i) m col
    (actualMarks_unique sh phase price kind frozen) reports keys (records _) rooms
  rw [rows i] at value
  exact value


end Calendar.StripChart
end Hierarchy.ProtocolRAM
end

end OAI
