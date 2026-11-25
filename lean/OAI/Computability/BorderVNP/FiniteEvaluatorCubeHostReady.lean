import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostSource

/-! # Executable host-copy bounds from the authenticated physical tables

The original sparse circuit headers, genuine directed-interval image and
published cell directory together justify the host pass. This proves the
word width and nonaliasing properties used by the native instruction
sequence on the post-ownership word memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube BorderVNP.Crossing Physical NativeIntervals HostAddress
open RoutingISA Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs VPVNP.MotifBase

variable (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ)
local notation "H" => HostScatter.Layout.fromFrame frame mem

variable {D v n d k w geometryBits J A origin m : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin a.cells) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin v) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
variable (F : Fields v a.cables n a.cells d k geometryBits σ) {x : σ → Bool} {old : Fin J → Fin v} {ports : Fin A → Fin n}
variable {il : NativeIntervals.Layout} {previous dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin m ↪o Fin il.count} {label : Fin a.cells → Label (a.n+1) a.header.d} {hz : a.header.d^(a.n+1)=il.alphabet}
variable (data : HostScatter.ResidentRows (HostScatter.Layout.fromFrame frame mem) il previous dir mem a.n a.header.d a.header.blocks a.b a.h a.K a.s)
variable (rows : PhysicalRows N cell il previous ord row Fin.valEmbedding label (productCode a.n a.header.d il.alphabet hz))
variable (interval : il.Image previous il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ a.header.blocks*(a.h*a.b))

include data rows in
omit [Fintype P] in
private theorem label_fit (i : ℕ) (hi : i < (H).count) (side : Bool) (hc : (H).cell mem i side < a.cells) :
    mem ((H).labels+(H).cell mem i side) < a.alphabet := by
  let j : Fin il.count := ⟨i,data.count ▸ hi⟩
  let c : Fin a.cells := ⟨(H).cell mem i side,hc⟩
  have lookup : previous (il.labels+(H).cell mem i side)=(productCode a.n a.header.d il.alphabet hz (label c)).val :=
    rows.labels c
  exact ((data.labels j side).trans lookup).trans_lt ((productCode a.n a.header.d il.alphabet hz (label c)).isLt.trans_eq hz.symm)

omit [Fintype P] in
/-- The canonical padding or internal row of the geometry producer has both
cell words zero. Thus even the unexecuted metadata read addresses in the
host's immutable input predicate stay in the directory when there is a cell. -/
theorem host_zero_cells {geometry : ℕ → ℕ}
    (header : Header frame origin a.cables a.cells J mem) (image : Image F old ports x origin geometry)
    (readGeo : ∀ z, origin ≤ z → z < origin+5*a.cables → mem z=geometry z)
    (i : ℕ) (hi : i < (H).count) (zero : (H).width mem i=0) : ∀ side, (H).cell mem i side=0 := by
  let j : Fin a.cables := ⟨i,header.edges ▸ hi⟩
  have col (u : Fin 3) : mem ((H).cables+3*i+u.val) = CableTriples.get (CableTriples.row F x j) u := by
    have base : (H).cables=origin := header.cables
    have hi := j.isLt
    have hu := u.isLt
    change i < a.cables at hi
    rw [base,Nat.mul_comm 3 i,readGeo _ (by omega) (by omega)]
    exact image.cable j u
  have width : (CableTriples.row F x j).width=0 := (col 2).symm.trans zero
  have blank : CableTriples.row F x j=⟨0,0,0⟩ := by
    simp only [CableTriples.row] at width ⊢
    split
    · rfl
    · rename_i h
      rw [ite_eq_right h] at width
      exact (h (.inr width)).elim
  intro side
  cases side with
  | false => exact (col 0).trans (congrArg (fun c => CableTriples.get c 0) blank)
  | true => exact (col 1).trans (congrArg (fun c => CableTriples.get c 1) blank)

include data rows interval cap in
/-- The actual copied cable slots supply both divisor and source bounds.
The retained scalar cable columns justify all receiving intervals, and the
native cell directory gives the start address of every one of them. -/
theorem host_fits_of_publication (rep : Represents N cell aux siteID edgeID portID F x)
    (codes : ∀ c, (F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^geometryBits)
    (supplyRoom : ∀ c, suppliedSize N cell c ≤ a.cellStride) {geometry : ℕ → ℕ}
    (header : Header frame origin a.cables a.cells J mem) (image : Image F old ports x origin geometry)
    (readGeo : ∀ z, origin ≤ z → z < origin+5*a.cables → mem z=geometry z)
    (before : origin+5*a.cables ≤ a.header.header) (words : HostWords a frame mem)
    (packet : (H).packets=a.header.packetBase) (single : (H).singles=a.singleBank)
    (radix : 0<a.header.d) (width : 0<a.h*a.b) (room : a.stop < 2^w)
    {controls teams : ℕ} (axis : Fin (a.n+1)) {initial scheduled written : ℕ → ℕ}
    (directory : CubeArena.DirectoryImage a frame controls axis teams initial scheduled written)
    (keepBank : ∀ c<a.cells, mem (a.hostDirectory+c*2+1) = written (a.hostDirectory+c*2+1)) :
    (H).Fits w mem := by
  have ends := host_ends_positive a frame mem N cell aux siteID edgeID portID F rep codes fieldRoom supplyRoom header image readGeo
  have allCells (pos : 0<a.cells) (i : ℕ) (hi : i < (H).count) (side : Bool) : (H).cell mem i side<a.cells := by
    by_cases nz : (H).width mem i=0
    · rw [host_zero_cells a frame mem F header image readGeo i hi nz side]; exact pos
    · exact (ends i hi side nz).1
  have bank (c : ℕ) (hc : c < a.cells) : mem (a.hostDirectory+2*c+1)=a.cellBank+c*a.cellStride := by
    rw [Nat.mul_comm 2 c,keepBank c hc]
    exact (directory.hostRows c hc).2
  exact host_fits_of_arena a frame mem header before words radix width room (label_fit a frame mem N cell data rows)
    allCells (fun i hi side nz => (ends i hi side nz).1) bank (fun i hi side own => (ends i hi side own.1).2)
    (fun i hi side own => by simpa only [words.blocks,words.width] using host_ordinal a data rows interval cap i hi side own)
    (host_source a data rows interval cap packet single)

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
