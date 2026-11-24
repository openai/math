import OAI.Computability.VPVNP.PairVertexSelectedPaths
import OAI.Computability.VPVNP.PairVertexFrameData
import OAI.Computability.VPVNP.PairTreeSelectedFrontier

/-! # An initialized physical root supplies the active ordinal worker -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NodeArguments TraversalRows TreeDecode
open CompressorRecords.SourceTransport LeafSourceLoad
open scoped Fin.CommRing

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → K) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (m : Memory w) (base grammar : ℕ) (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network)
    (half : ∀ u, ((B.execute κ hκ T hT X).finalState z).network.Half u)
    (cap : ℕ) (i : Fin (siteOrder ((B.execute κ hκ T hT X).finalState z)).length)
    (R : LeafArena.Regions) (data : Fin 10 → Word w) (fields : Fin 12 → Word w) (vals : Static 34 → Word w)
    (offset : Word w) (nodeCap maxTicks : ℕ) (format : Packet → Prop) (desc : ℕ → List ℕ)
    (domain : Word w → Scratch w (M.publicData 6).val → Prop)
    (handlers : NodeDispatch.Role → HookParser w (M.publicData 6).val)
    (cost : VisitPath w (M.publicData 6).val → Prop)

local notation "E₀" => B.execute κ hκ T hT X
local notation "Y₀" => StateExecution.finalState (E₀) z
local notation "tree₀" => selectedTrees B κ hκ T hT X z rowBase
local notation "site₀" => Order.entries (siteOrder (Y₀)) i
local notation "q₀" => Packet.mk (VertexTree.address ((tree₀) (site₀))) (packed (Y₀) (site₀) (half (site₀)))
local notation "word₀" => Machine.publicData M 6
local notation "N₀" => Fin.val (word₀)
local notation "H₀" => TerminalLink.header (Machine.publicData M)
local notation "G₀" => NativeFrame.frameBase R
local notation "stable₀" => VertexFrameData R data offset vals
local notation "valid₀" => Budgeted R.arguments format (stable₀) desc (privateHistogram order R.histBase) nodeCap ((N₀)*nodeCap)

/-- The checked physical gather initializes every state component used by
the ascending vertex interpreter. The layer checks concern the fixed role
programs, and the size and read bounds concern their selected public rows. -/
noncomputable def OrdinalRows.ofRoot
    (checked : SelectedChecks B κ hκ T hT X z rowBase A M m ((G₀) : Word w) offset R.histBase
      order P (valid₀) domain handlers cost)
    (cfg : Config w p r) (es : List (Event w)) (root : ActiveRootState A cfg (i.val : Word w) (word₀)
      offset R (q₀) data fields vals)
    (run : TerminalRootGather.Prefix M m (M.program.start (i.val : Word w)) es cfg)
    (det : choiceBits es = []) (same : after m es = m) (reads : Reads (TerminalLink.workerCell (H₀)) es)
    (labelCount : R.histWords = g) (offsetAt : fields 10 = offset) (histAt : fields 11 = (R.histBase : Word w))
    (positive : 0 < N₀) (above : N₀ ≤ R.histBase) (cacheFit : R.cacheBase+38 ≤ 2^w)
    (type : format (q₀)) (children : subtreeAddresses desc (q₀) = ((tree₀) (site₀)).preorder)
    (rows : AllRows w m B.recordLimit rowBase rowBase (selectedLayers B κ hκ T hT X z))
    (space : rowBase+words B.recordLimit (selectedLayers B κ hκ T hT X z) ≤ (H₀).val)
    (headerFit : (H₀).val+31 < 2^w) (capacity : B.growthConstant^T ≤ N₀)
    (external : base+grammar+g ≤ (H₀).val)
    (hbase : M.publicData 4 = (base : Word w)) (hgrammar : M.publicData 5 = (grammar : Word w))
    (hg : M.publicData 9 = (g : Word w))
    (small : ∀ j, cost j → j.trace.length ≤ maxTicks)
    (time : es.length+(15+maxTicks)*((E₀).termChain (B.records κ hκ T hT X) z).occurrences
      (fun _ => 1) (site₀)+7*g+46 ≤ cap) :
    OrdinalRows B κ hκ T hT X z rowBase A M base grammar order P half cap m i := by
  subst g
  have frameFit : G₀ + 12 ≤ 2^w := by
    have := R.hist_before
    unfold NativeFrame.frameBase
    omega
  have distinct : (subtreeAddresses desc (q₀)).Nodup := children ▸ (selected_preorders B κ hκ T hT X z rowBase).1 (site₀)
  have count := chainTrees_length ((E₀).termChain (B.records κ hκ T hT X) z) (selectedParsers B κ hκ T hT X z)
    (selectedPointers B κ hκ T hT X z rowBase) (fun v => leafTree (sitePointers B.recordLimit rowBase (siteOrder X) v))
    (fun _ => 1) (fun _ => le_rfl) (site₀)
  have size : ((tree₀) (site₀)).preorder.length ≤ N₀ :=
    count.trans (((B.branch_bounds κ hκ T hT X z).2.2.2.1 (site₀)).trans capacity)
  have prepared := budget_of_root root offsetAt histAt above frameFit cacheFit format type desc distinct order nodeCap
    ((N₀)*nodeCap) (by rw [children]; exact Nat.mul_le_mul_right _ size)
  have nonzero : word₀ ≠ 0 := fun h => by rw [h] at positive; exact (Nat.lt_irrefl _ positive)
  have wordTop : word₀-1 = (((N₀)-1 : ℕ) : Word w) := Fin.ext <| by
    rw [Fin.val_sub_one_of_ne_zero nonzero,Fin.val_natCast,Nat.mod_eq_of_lt (by have := (word₀).isLt; omega)]
  exact {
    endAddr := N₀, src := R.histBase, G := ((G₀) : Word w), offset := offset
    valid := Budgeted R.arguments format (VertexFrameData R data offset vals) desc
      (privateHistogram order R.histBase) nodeCap ((N₀)*nodeCap)
    domain := domain, handlers := handlers, cost := cost, selected := checked
    cfg := cfg, pre := es, pref := run, noChoice := det, noWrite := same, prefixReads := reads
    persistent := root.persistent, atRoot := root.pc, top := (N₀)-1, stack := root.resident.stack
    endTop := by omega, sp := root.top.trans wordTop, endReg := root.endReg.trans (Fin.cast_val_eq_self _).symm
    one := root.one, zero := root.resident.zeroHistogram order above (by omega), prepared := prepared
    rows := rows, space := space, hfit := headerFit, capacity := capacity, above := above
    hsrc := by have := R.hist_before; omega
    hdst := by omega, cells := fun j => TerminalFootprint.below (H₀) headerFit (by have := j.isLt; omega)
    hbase := hbase, hgrammar := hgrammar, hg := hg, maxTicks := maxTicks, small := small, room := time }

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
