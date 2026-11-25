import OAI.Computability.BorderVNP.DiagonalSignedPublishedMeanRows
import OAI.Computability.BorderVNP.DiagonalRoutedReceivingOwner

/-! # The receiver on the true published signed packet

The ordered network, demand widths, labels, and routed assignment are fixed
before the attained processor RAM. Actual published rows and the real label
pass recover that owner for each original cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP BurstRAM TeamContraction ProcessorSlots PackedHistoryCircuit Packing RoutingOutputs Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical Packing.Directory BorderVNP.Cube
open Cube.Physical Cube.MeanChoice Cube.LabelIndex
open TeamContraction.JointHeader CubeHeaderInstall LocalRow CubeArena Tally Physical.NativeAssignments
open scoped Classical

variable {D s n d k b w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : CubeArena.Layout) (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cables n a.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<a.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (pub : Arg → Word w) (base origin gap : ℕ) (before mid : Memory w)

local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin a.cables a.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin a.cables a.cells dir.entries
local notation3 (prettyPrint := false) "pp" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "lp" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory pp lp
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

local notation3 (prettyPrint := false) "width₀" => fun i : Fin (list).length => list[i.val].width

include net ids wireFit hk wordFit positive liveWidth in
set_option maxRecDepth 4800 in
set_option maxHeartbeats 1200000 in
/-- Glue the authentic directory publication directly to the post-label owner
word. Neither a receiving permutation nor a physical traffic placement is an
input. Both are read from the actual saved geometry and the native writer. -/
theorem signed_published_owner_word {I : Type} [Fintype I] {sc : I → Fin a.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {pins}
    (write : SlottedWriter a dir pp lp pins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (placed : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin a.cables a.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates ≤ origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : a.cells≤2^w) (stride : a.cellStride≤2^w)
    {R : ℕ} (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w) (G : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (raw : Broadcast a.n a.header.d a.header.cap)
    (room : PinnedRawInput (ar := a) (D := dir) («pp» := pp) («lp» := lp) (pub := pub) (slotted := mid) (base := base)
      f old fresh gates outputs width off ell controls G claims pad raw R X)
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg
      (ISA.publish mid head base rows)) (alphabet : 0<a.header.d) :
    let label := meanPackedLabel N cell recv width₀ (List.finRange a.cells) a.n a.header.d alphabet
    let owner := greedyOwner (blocks := a.header.blocks) (K := a.K) (h := a.h) R a.b a.s label recv width₀
    ∀ q : NativeAssignments.Routed (b := a.b) (s := a.s) owner,
      (show a.header.cap=declarationCap a.n a.header.d a.header.blocks a.b a.h a.s by rw [room.geometry]; rfl) ▸
        raw = broadcast a.b a.s q.1 →
      let axis := Fin.ofNat (a.n+1) (readCode (a.n+1) raw.1)
      let input := powerHeaderImage a f.dst (readings z.val.2.2)
      ∀ c : Fin a.cells, (a.receivingOwner head axis R input c.val).val = routedOwnerWord a owner label q c.val := by
  obtain ⟨_,_,_,cross,delivery,traffic⟩ := signed_published_mean_rows a dir N cell aux siteID edgeID portID F x
    net ids wireFit hk wordFit positive original live liveWidth bounds pub base origin gap before mid
    write img placed fit hdr scratch originFits teams procs fields literal cells stride
  exact pinned_static_owner_word N a cell recv width₀ f old fresh gates outputs width off ell controls mac reg
    G claims pad X raw room cross delivery.toEmbedding traffic z alphabet

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
