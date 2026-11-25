import OAI.ThreeFlat.RAM.HistoryGatherGeometry
import OAI.ThreeFlat.RAM.HistoryPartyCatalogueData
import OAI.ThreeFlat.RAM.HistoryPartyTileTable
import OAI.ThreeFlat.Diagonal.FixedTileCapacity
import OAI.ThreeFlat.Diagonal.HistogramAdmissionNet
import OAI.ThreeFlat.Diagonal.HistogramTileNetwork
import OAI.ThreeFlat.RAM.HistoryCompactorCounts
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.PhysicalShrink
import OAI.ThreeFlat.Diagonal.RefreshPartyPorts
import OAI.ThreeFlat.Diagonal.ShrinkTableOrdinal
import OAI.ThreeFlat.Diagonal.CompressorNodeIncident

namespace OAI
/-! # The public word image of a physical shrink and refresh program -/

namespace ThreeFlat.RAM.HistoryStageBody.Physical

open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.MotifSelector
open CompressorPacking MotifOuterTerms HistogramTileNetwork Expander
open scoped Classical BigOperators Fin.CommRing

noncomputable section

variable {F : Type} [Field F] [Fintype F]

/-- Two finite scalar tables, with the same data and port numbering as a party leaf. -/
structure Party (F : Type) where
  demands : ℕ
  supplies : ℕ
  letters : ℕ
  codeBits : ℕ
  header : ℕ
  maxDigit : ℕ
  port : HistoryPortCatalogue.Page demands supplies
  tile : (Fin (header+(supplies*maxDigit+supplies*maxDigit))→Bool)→F
  admit : (Fin (supplies*codeBits+letters)→Bool)→F

def Party.bound (P : Party F) := P.header+(P.supplies*P.maxDigit+P.supplies*P.maxDigit) +
  (P.supplies*P.codeBits+P.letters)

def Party.kind (P : Party F) (ar : ℕ) : HistoryPartyHeader.Kind :=
  let table {b : ℕ} (f : (Fin b→Bool)→F) :=
    if h : b≤ar then (HistoryStaticArchive.index F ar h f).val else 0
  ⟨P.supplies,P.letters,P.codeBits,P.header,P.maxDigit,table P.tile,table P.admit⟩

def Party.ofTile {J E S : Type} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
    (D : PortGraph J E) (G : Supply J S) (j : J) (base : E→ℕ)
    (T : FixedMotifTile D (ports G) base F) {n e : ℕ} (dp : Fin n ≃ D.Port j)
    (sp : Fin e ≃ (ports G).Port j) (di : Fin n→ℕ) (si : Fin e→ℕ) : Party F := by
  letI := T.hasLetter
  let B : Header (D.Port j) T.Alphabet (fun q => base q.1.1) T.bits n := ⟨dp,T.encode⟩
  let fit := fun z (a : Fin e) => T.output_le_cap z (sp a).1.1
  let tile := HistogramTileNetwork.tile D G j base B sp T.output fit T.entry
  let good := headerGood G j sp T.encode
  let letter := headerLetter G j sp (Fintype.equivFin _) T.encode
  exact ⟨n,e,Fintype.card T.Alphabet,T.bits,B.arity,T.bitCap,
    ⟨di,si,fun u => base (dp u).1.1,(sp.symm (anchorPort G j)).val⟩,
    HistoryPartySpecialization.tileTable tile,MotifSelectorChecks.checkLut good letter⟩

def shrinkParty (T : ShrinkMotif.Table F) (i : Fin (T.more.length+1)) (j : Fin 6) : Party F :=
  let dp := (Fintype.equivFin (demandGraph.Port j)).symm
  let sp := (Fintype.equivFin (supplyGraph.Port j)).symm
  Party.ofTile demandGraph ShrinkMotif.supply j (T.base (T.row i)) (T.block (T.row i))
    dp sp (fun q => (dp q).1.1.val) (fun q => (sp q).1.1.val)

def refreshParty (B : PhysicalStage.Block F) (i : Fin (B.refresh.last+1))
    (j : Fin (2^B.exponent B.levels)) : Party F :=
  let G := DoublePorts.connectedSupply B.graph B.hh B.degree B.symmetric B.connected
  Party.ofTile (RefreshMotif.denseGraph _) G j (B.refresh.base i) (B.refresh.block i)
    (RefreshParty.denseOrder j) (RefreshParty.sparseOrder B.graph B.symmetric B.degree j)
    Fin.val Fin.val

/-- Each grid page is indexed by the native tile ordinal followed by the party ordinal. -/
def grid {n p : ℕ} (f : Fin n→Fin p→Party F) : List (Party F) :=
  (List.finRange n).flatMap fun i => List.ofFn (f i)

structure Grid (F : Type) where
  mode : HistoryGatherBody.Geometry
  oldPorts : ℕ
  childBound : ℕ
  motifs : ℕ
  parties : ℕ
  rows : List (Party F)

def shrinkGrid (B : PhysicalStage.Block F) (i : Fin B.levels) : Grid F :=
  let d := 2^B.exponent i.val
  let c := 2*d+1
  let D := 2^B.exponent (i.val+1)
  let count := PhysicalShrink.parallel c d D
  let S : Native.Graph.Stage := ⟨d,c,count,∑ j,count j,usedDegree count c d,D⟩
  ⟨.shrink S,d,d*2^c,Native.ShrinkStage.Incidents.capacity S,6,grid (shrinkParty B.shrink)⟩

def refreshGrid (B : PhysicalStage.Block F) : Grid F :=
  let m := 2^B.exponent B.levels
  ⟨.refresh m B.h B.pad,m,1,1,m,grid (refreshParty B)⟩

def grids (B : PhysicalStage.Block F) := List.ofFn (shrinkGrid B) ++ [refreshGrid B]

def Grid.demand (G : Grid F) := (G.rows.map Party.demands).sum
def Grid.supply (G : Grid F) := (G.rows.map Party.supplies).sum
def Grid.digits (G : Grid F) := (G.rows.map fun p => p.port.digits).sum
def Grid.stride (G : Grid F) := HistoryPortCatalogue.stride G.demand G.supply G.digits

def Grid.words (G : Grid F) (ar : ℕ) : List ℕ :=
  (G.rows.flatMap fun p => List.ofFn (p.kind ar).words) ++
    G.rows.flatMap (fun p => List.ofFn fun j : Fin G.stride => p.port.at G.demand G.supply j.val)

def Grid.size (G : Grid F) := (7+G.stride)*G.rows.length

def arity (B : PhysicalStage.Block F) := ((grids B).flatMap fun g => g.rows.map Party.bound).sum

def staticSize (B : PhysicalStage.Block F) := HistoryStaticArchive.size
  (HistoryStaticArchive.count F (arity B)) (arity B)

def gridSize (B : PhysicalStage.Block F) := ((grids B).map Grid.size).sum

/-- The complete mounted word image has two height-dependent arrays. All other words
depend only on the finite block and the field. -/
def libraryWords (B : PhysicalStage.Block F) (height : ℕ) :=
  StableCompactROMNative.size height + staticSize B + HistoryCompactorCounts.size height + gridSize B

def data (B : PhysicalStage.Block F) (height W : ℕ) (q : Fin (libraryWords B height)) : Word W :=
  let n := StableCompactROMNative.size height
  let l := staticSize B
  let c := HistoryCompactorCounts.size height
  if h : q.val<n then StableCompactROMNative.data height
    (fun t : (Fin 3→Bool)→F => (Fintype.equivFin _ t).val) ⟨q.val,h⟩
  else if h : q.val-n<l then (HistoryStaticArchive.all F (arity B)).data ⟨q.val-n,h⟩
  else if h : q.val-n-l<c then HistoryCompactorCounts.data F height ⟨q.val-n-l,h⟩
  else (((grids B).flatMap fun g => g.words (arity B))[q.val-n-l-c]?.getD 0 : ℕ)

/-- The selected stage occurs in this interval of the actual immutable S38 image. -/
structure Mounted (B : PhysicalStage.Block F) (height W start : ℕ) (m : Memory W) : Prop where
  words : ∀ q : Fin (libraryWords B height),m (start+q.val)=data B height W q

theorem libraryWords_eq (B : PhysicalStage.Block F) (height : ℕ) :
    libraryWords B height = 384000*(height+1)^4+staticSize B+2*(height+1)+gridSize B := by
  unfold libraryWords StableCompactROMNative.size HistoryCompactorCounts.size
  rw [StableCompactROMPool.size_eq]

end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
