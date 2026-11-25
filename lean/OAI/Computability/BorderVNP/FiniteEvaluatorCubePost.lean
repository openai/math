import OAI.Computability.BorderVNP.FiniteEvaluatorCellsPost
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadSet

/-! # The cube evaluator on the actual memory left by the cell routines

The cell argument writer, signed validators, and finite scalar packer preserve
the allocated input regions of the cube lookup. In particular, the bounds for
dynamic recipe addresses and resolved input references hold in the final
memory, where the next native instructions execute.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TypedTaskBuilder BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit

variable {F : Type*} [Fintype F] {n b h K s w N : ℕ}
variable {pub : Arg → Word w} {mem : Memory w}
variable (X : Cells.Inputs F) {codec : Cells.Codec} (hc : Cells.Prepared X pub mem N codec)

namespace CubePacket

variable (P : Inputs n b h K s F)

include hc in
/-- Transport the protected live frame, triple stream and owned packet banks once
the scalar/recipe deck has been located in the actual post-cell memory. -/
private theorem post_of_tables (original : Prepared P pub mem)
    (tripleRange : X.layout.SourceRange P.frame.triples (3*P.frame.count))
    (bankRange : ∀ i, X.layout.SourceRange (P.visits i).base (bankWidth n b h K s))
    (recipes : P.frame.recipeAt (readings (X.post mem)) n b h K s)
    (zero : ((X.post mem) P.frame.zeroAddr).val=0) (one : ((X.post mem) P.frame.oneAddr).val=1)
    (deck : ∀ k < 2^argumentWidth n b h K s, ((X.post mem) (P.table+k)).val =
      idTable (selectorOrder n K h) (vertexOrder _) (fun e => CubeWord.encode (P.entry e)) k) :
    Prepared P pub (X.post mem) := by
  apply transfer_of_tables P original _ (fun j hj => Cells.post_source X hc tripleRange hj)
    (fun i j hj => Cells.post_source X hc (bankRange i) hj) recipes zero one deck
  intro j hj
  apply Cells.post_frame X hc
  simp [frameWords] at hj
  omega

/-- A scalar deck may use separate allocated intervals for its two literals,
fixed recipe table and finite-field value table. -/
structure Sources (l : Layout) : Prop where
  /-- Memory word containing literal zero. -/
  zero : l.SourceRange P.frame.zeroAddr 1
  /-- Memory word containing literal one. -/
  one : l.SourceRange P.frame.oneAddr 1
  /-- Row-major fixed address recipes. -/
  recipes : l.SourceRange P.frame.recipes (CubeConstants.recipes n b h K s).length
  /-- Scalar table indexed by the generated bits. -/
  values : l.SourceRange P.table (2^argumentWidth n b h K s)
  /-- The runtime triples of all owned vertices. -/
  triples : l.SourceRange P.frame.triples (3*P.frame.count)
  /-- Physical selector, demand and incident supply words for each owned visit. -/
  banks : ∀ i, l.SourceRange (P.visits i).base (bankWidth n b h K s)

include hc in
/-- The original cube inputs survive the entire cell stage on their allocated
intervals, including every computed address read by the native lookup. -/
theorem Prepared.post (original : Prepared P pub mem) (sources : Sources P X.layout) :
    Prepared P pub (X.post mem) := by
  apply original.transfer P
  intro a h
  cases h with
  | frame j needed =>
    apply Cells.post_frame X hc
    simp [frameWords] at needed
    omega
  | zero => exact Cells.post_source X hc sources.zero (i:=0) (by decide)
  | one => exact Cells.post_source X hc sources.one (i:=0) (by decide)
  | recipe j bound => exact Cells.post_source X hc sources.recipes bound
  | value j bound => exact Cells.post_source X hc sources.values bound
  | triple j bound => exact Cells.post_source X hc sources.triples bound
  | bank i j bound => exact Cells.post_source X hc (sources.banks i) bound

end CubePacket

namespace CubeDeck

variable (table : TableEntry n b h K s → F) (f : Frame) (fresh : ℕ)
variable (visits : Fin f.count → Visit n b h K s) (dst demand : ℕ)

local notation "packet" => inputs table f fresh visits dst demand
local notation "stop" => CubeConstants.arenaEnd fresh (entry table)

include hc in
/-- For the assembled native initializer there is just one common protected deck.
The runtime triples and the routed packet bits each remain in their original
source regions when the succeeding evaluator reads them. -/
theorem prepared_post (original : CubePacket.Prepared packet pub mem)
    (deckRange : X.layout.SourceRange fresh (stop-fresh))
    (tripleRange : X.layout.SourceRange f.triples (3*f.count))
    (bankRange : ∀ i, X.layout.SourceRange (visits i).base (bankWidth n b h K s)) :
    CubePacket.Prepared packet pub (X.post mem) := by
  have deck : At table f fresh (readings mem) := ⟨original.recipe,original.deck,original.zero,original.one⟩
  have retained := At.preserve table f fresh deck f (mem':=readings (X.post mem)) (fun a lo hi => by
    have eq : fresh+(a-fresh)=a := by omega
    have word := Cells.post_source X hc deckRange (i:=a-fresh) (by omega)
    rw [eq] at word
    exact congrArg Fin.val word)
  exact CubePacket.post_of_tables X hc packet original tripleRange bankRange retained.recipe retained.zero retained.one retained.words

end CubeDeck
end FiniteEvaluator

end BorderVNP
end Computability
end OAI
