import OAI.Hierarchy.DescentResidentGeometryRead
import OAI.Hierarchy.DescentOrdinaryRootTables
import OAI.Hierarchy.DescentDepotPage

namespace OAI
/-! # Bump placement of the actual donor owner, four-hop rank, hub, and root tables -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement
open DescentPacking.PackedMatch.Local DescentHaloWalkRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM
open scoped Classical
noncomputable section
variable (H G M D input : ℕ)
local notation "P" => breadth D
local notation "paths" => H*P
local notation "rows" => H*chunks G M
def page (n : ℕ) := 2^(Nat.clog 2 n)
def topBank (base n : ℕ) : Bank := ⟨base,Nat.clog 2 n⟩
local notation "roots" => RootTables.length H G M D
local notation "chart" => DonorChartBook.words H G M P
def first (base : ℕ) := base+2*(roots+1)
def rowEnd (base : ℕ) := Owners.Board.venue input M (first H G M D base) rows + page rows
def rankBase (base : ℕ) := rowEnd H G M D input base + page paths
def hubBase (base : ℕ) := rankBase H G M D input base + page paths
def bookBase (base : ℕ) := hubBase H G M D input base + page paths
def endAddress (base : ℕ) := bookBase H G M D input base + 2*(chart+1)

def layout (base : ℕ) (neighbors hub : Bank) : Dynamic.Layout where
  ownerBase:=first H G M D base
  walks:=RootTables.walks H D base neighbors
  ranks:=RootTables.ranks H D base (topBank (rowEnd H G M D input base) paths)
  hub:=hub
  rankOut:=rankBase H G M D input base
  hubOut:=hubBase H G M D input base
  literal:=bookBase H G M D input base

theorem translate (base : ℕ) :
    endAddress H G M D input base=base+endAddress H G M D input 0 := by
  simp only [endAddress,bookBase,hubBase,rankBase,rowEnd,Owners.Board.venue,Owners.Board.rom,first,Owners.Board.bank,Bank.size,Nat.zero_add,Nat.add_assoc]

theorem extent (base : ℕ) :
    endAddress H G M D input base ≤ base+18*paths+12*rows+2*P*((M+1)*(P+1))+2^(input*M)+16 := by
  have p:=(ceilPage paths).2
  have r:=(ceilPage rows).2
  unfold endAddress bookBase hubBase rankBase rowEnd first page RootTables.length DonorChartBook.words DonorChartBook.pages
  simp only [Owners.Board.venue,Owners.Board.rom,Owners.Board.bank,Bank.size]
  nlinarith only [p,r]

variable {w : ℕ} (base : ℕ) (neighbors flags : Bank)
local notation "L" => layout H G M D input base neighbors flags
local notation "roof" => endAddress H G M D input base
local notation "owner" => first H G M D base
local notation "ends" => rowEnd H G M D input base
local notation "ranks" => rankBase H G M D input base
local notation "hubs" => hubBase H G M D input base
local notation "books" => bookBase H G M D input base

private theorem root_column_bound (j : ℕ) (hj : j<6) :
    (RootTables.bank H D base j).base+(RootTables.bank H D base j).size≤owner := by
  change base+j*paths+page paths≤base+2*(roots+1)
  have hi:=Nat.mul_le_mul_right paths (show j≤6 by omega)
  have pad:=(ceilPage paths).2
  unfold page RootTables.length;omega

theorem prior (before : neighbors.base+neighbors.size≤base) (kept : flags.base+flags.size≤base) :
    Dynamic.Prior L := by
  have base_le_owner : base ≤ owner := Nat.le_add_right _ _
  exact ⟨before.trans base_le_owner, root_column_bound H G M D base 0 (by decide),
    fun j => root_column_bound H G M D base (j.val + 1) (by omega),
    root_column_bound H G M D base 5 (by decide), kept.trans base_le_owner⟩

/-- The predecessor provides its real adjacency and hub vectors. Every other old
bank in this walk is a literal column of the new root table. -/
theorem room {r p d : ℕ} (routed : input=Owners.inputBits r D p d) (e : Expr) (read : e.Fits w owner)
    (key : M*max input ((Owners.digits r D d*3)*r)≤w/2)
    (ngh : neighbors.base+neighbors.size≤base) (hub : flags.base+flags.size≤base)
    (neighborsSize : H*D≤neighbors.size) (hostWord : H<2^w) (degreeWord : D<2^w) (cap : roof≤2^w) :
    Dynamic.Room L r D p d H G M w e := by
  have ord := prior H G M D input base neighbors flags ngh hub
  have rowsFit : rows ≤ page rows := (ceilPage rows).1
  have pathsFit : paths ≤ page paths := (ceilPage paths).1
  have positions : owner≤ends := by
    calc
      owner ≤ Owners.Board.rom owner rows := Nat.le_add_right _ _
      _ ≤ Owners.Board.rom owner rows + 2^(input*M) := Nat.le_add_right _ _
      _ ≤ Owners.Board.venue input M owner rows := Nat.le_add_right _ _
      _ ≤ ends := Nat.le_add_right _ _
  have beforeRank : ends+paths≤ranks := Nat.add_le_add_left pathsFit ends
  have beforeHub : ranks+paths≤hubs := Nat.add_le_add_left pathsFit ranks
  have beforeBook : hubs+paths≤books := Nat.add_le_add_left pathsFit hubs
  have ceiling : books+chart<2^w := by
    change books + 2*(chart+1) ≤ 2^w at cap
    omega
  have here : ends<2^w := by omega
  have middle : ranks<2^w := by omega
  have ownerBeforeRank : owner≤ranks := by omega
  refine ⟨read, ?_, ?_, ?_, ?_, beforeHub, beforeBook, ceiling,
    bankFits flags (ord.flags.trans positions) here⟩
  · simpa only [← routed] using key
  · change Owners.Board.venue (Owners.inputBits r D p d) M owner rows + rows ≤ ends
    rw [← routed]
    exact Nat.add_le_add_left rowsFit _
  · exact ⟨bankFits neighbors (ord.adjacency.trans positions) here,
      bankFits (RootTables.bank H D base 0) (ord.root.trans positions) here,
      fun j => bankFits (RootTables.bank H D base (j.val+1)) ((ord.directions j).trans positions) here,
      neighborsSize, pathsFit, fun _ => pathsFit, beforeRank.trans_lt middle, hostWord, degreeWord⟩
  · exact ⟨bankFits (topBank ends paths) (show ends + page paths ≤ ranks from le_rfl) middle,
      bankFits (RootTables.bank H D base 5) (ord.offsets.trans ownerBeforeRank) middle,
      pathsFit, pathsFit, by change ranks + paths < 2^w; omega⟩


end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement

end OAI
