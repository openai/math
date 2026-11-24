import OAI.Computability.VPVNP.PairRefreshTraversalPlan
import OAI.Computability.VPVNP.PairRefreshResidentKernel

/-!
# Executing the selected refresh body in the terminal DFS layout

The four geometry instructions and the resident map image run in one host program.
The old and new argument intervals are below the shared histogram. The actual map
workspace lies beyond the immutable geometry and finishes before the scalar cache.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
local notation "T" => plan B ties stride order
private abbrev siteOrder {a g : ℕ}
(X : State a (a + g)) := sites (D := 2 ^ a) X.baseIndex (bitWordFinEquiv g)
local notation "D" => 2 ^ S.portExponent
local notation "H" => 2 ^ S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds

/-- One constant for every node, level and input size of the fixed refresh role. -/
noncomputable def budget : ℕ := (T).uniform.choose + 4

variable {pcs regs bits g : ℕ} (loc : Fin (body B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (bank : Fin (body B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (degree n rowEnd : ℕ)
  (U V : IncidenceDirectory bits) (m : Memory bits)
  (start parent child listHead oldHead newHead : ℕ)

local notation "left" =>
  Segment.leftPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "right" =>
  Segment.rightPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "commonBank" => Function.Embedding.trans (locatorBank B ties stride order) bank
local notation "own" => Function.Embedding.trans (Function.Embedding.trans Function.Embedding.inr
  (Equiv.toEmbedding (RefreshResidentImage.Plan.registers T))) bank
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "supply" =>
  blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh choice
local notation "O" => siteOrder X
local notation "R" => TerminalLayout.privateRegions degree n rowEnd hist
local notation "A" => LeafArena.Regions.arguments R
local notation "histBase" => LeafArena.Regions.histBase R
local notation "directory" => histBase + hist + 12 + 2 * n
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "wo" => ws (v, Prod.snd v)
local notation "wi" => ws (Equiv.symm perm (v, Prod.snd v))

variable (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
local notation "diagonalValue" => portDiagonal perm ws (Prod.fst v) (Prod.snd v) (oldHalf X v old)
  (segments X v P S.port_order hd supply new)
local notation "E₀" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀)
local notation "u" => repetitions B.refresh (EntryInput.demand E₀)
local notation "d" => demandBits tieSource tieTarget (Prod.snd v) (EntryInput.demandBits E₀)
local notation "x" => mapHalf S.portSupply (fun _ => inputBits) (EntryInput.supplyBits E₀)

/-- Histogram ordinals emitted by the selected refresh entry after its diagonal tie check
succeeds. -/
noncomputable def emitted : Option (List (Fin hist)) :=
  if diagonalValue = (1 : ℤ) then
    ((runEntry B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀)
      (EntryInput.payload E₀) v.2 d x).1.map (List.map (fun e => order (.inr e))))
  else none

set_option maxHeartbeats 2200000 in
-- Elaborating the native call specializes every register and both dependent node frames.
/-- The selected refresh role executes from the actual located parent and singleton
preimage row. Its successful labels and its rejection branch agree with the local
refresh map, with constant external probes and linear local work. -/
theorem map_body
    (rows : ∀ j, M.code (loc j) =
      ((body B ties stride order).row loc dfs saved bank done j).resize bits)
    (apartD : ∀ i j, bank i ≠ dfs j) (apartS : ∀ i j, bank i ≠ saved j)
    (c : Config bits pcs regs) (entry : c.pc = left TraversalGeometry.reload.entry)
    {endAddr : ℕ} {G offset : W bits} (endWord : c.reg (dfs 6) = (endAddr : W bits))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset (word histBase))
    (oldWord : (c.reg (commonBank 11)).val = oldHead)
    (newWord : (c.reg (commonBank 4)).val = newHead)
    (siteWord : (c.reg (commonBank 7)).val = (O v).val)
    (parentWord : (c.reg (commonBank 0)).val = parent)
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits)
    {fit : Fintype.card X.Base * D * 2 ^ g * D ≤ 2 ^ bits}
    (stored : Build.Stored X S.graph
      (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldCols : U.ActualColumns X m) (newCols : V.ActualColumns Y m)
    (oldData : NodeFields A child X (oldSite X v) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites v) new c.privateMem)
    (childBound : child < rowEnd) (parentBound : parent < rowEnd) (oldDegree : D ≤ degree)
    (newDegree : 2 ^ (S.degreeExponent 0) ≤ degree) (oldWidth : X.maxWireWidth ≤ n)
    (newWidth : (Y).maxWireWidth ≤ n)
    (copyBound : u ≤ n) (large : MapCallWords.headCapacity D H + 12 ≤ n) (five : 5 ≤ n)
    (capacity : MapWorkspace.Capacity B.refresh bits n (R).cacheBase) (wide : D < 2 ^ bits)
    (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits) :
    let names := emitted B order X choice v old new
    ∃ out es, ChildScan.Prefix M m c out [] es ∧
      es.length ≤ budget B ties stride order * (wo + wi + u + 1) ∧
      countProbes es ≤ budget B ties stride order ∧
      choiceBits es = [] ∧ (if names.isSome then out.pc = done else M.code out.pc = .reject) ∧
      out.persistent = c.persistent ∧ (∀ j, (∀ i, j ≠ bank i) → out.reg j = c.reg j) ∧
      (∀ q : W bits, q.val < directory →
        (∀ l : Fin hist, q ≠ word (histBase + l.val)) → out.privateMem q = c.privateMem q) ∧
      ∀ l : Fin hist,
        out.privateMem (word (histBase + l.val)) = c.privateMem (word (histBase + l.val)) +
        ((names.getD []).count l : W bits) := by
  dsimp only
  obtain ⟨mid, pre, entry', priv, pers, frame, args, hdir, hhist⟩ :=
    enter B ties stride order loc dfs saved bank done M X choice v A U V m start parent child
      listHead oldHead newHead
      histBase rows c entry endWord resident oldWord newWord siteWord parentWord header row lanes
  have first : ChildScan.Prefix M m c mid [] (List.replicate 4 .tick) := by
    intro fuel bs
    exact pre.execute fuel m bs
  have ready : mid.pc = (T).diagSetup (right ∘ (T).locations) 0 := by
    rw [entry']
    change right ((T).diagSetup (T).locations 0) = (T).diagSetup (right ∘ (T).locations) 0
    by_cases h : 0 < (RegisterSetup.lines (T).diagonal).length
    · refine (congrArg right (dite_eq_left h)).trans ?_
      rw [RefreshResidentImage.Plan.diagSetup, dite_eq_left h]
      rfl
    · refine (congrArg right (dite_eq_right h)).trans ?_
      rw [RefreshResidentImage.Plan.diagSetup, dite_eq_right h]
      rfl
  have banks : RefreshResidentImage.Plan.Banks T dfs saved commonBank own := by
    refine ⟨fun _ j => apartD _ j, fun _ j => apartS _ j, ?_⟩
    intro a b eq
    have h : (Sum.inr a : Fin 14 ⊕ (T).Local) = Sum.inl b :=
      (T).registers.injective (bank.injective eq)
    contradiction
  have installed := (body_links B ties stride order loc dfs saved bank done M rows).2
  have oldEnd := TraversalGeometry.argument_end degree n rowEnd hist X (oldSite X v) old child
    childBound oldDegree oldWidth
  have newEnd := TraversalGeometry.argument_end degree n rowEnd hist Y (promotedSites v) new parent
    parentBound newDegree newWidth
  have endSpace :=
    TraversalGeometry.workspace_before_cache degree n rowEnd hist (MapCallWords.headCapacity D H) u
    large five copyBound
  have nfits : n < 2 ^ bits := by
    apply Nat.lt_of_le_of_lt _ capacity.room
    change n ≤ n + rowEnd * (2 * degree * n + 1) + hist + n ^ 5
    omega
  have fields (e) : ws e < 2 ^ bits := ((X.width_le_maxWireWidth _).trans oldWidth).trans_lt nfits
  obtain ⟨out, es, run, len, probes, path, pc', pers', frame', mem, hits⟩ :=
    (T).native (right ∘ (T).locations) dfs saved commonBank own done M installed
      X choice v A child parent U V start m old new mid ready banks args stored oldCols newCols
      (priv ▸ oldData) (priv ▸ newData) histBase n directory histBase hdir hhist oldEnd newEnd
      oldWidth newWidth (by omega) (by omega) endSpace.2 capacity copyBound wide
      (fields _) (fields _) tableWidth
  obtain ⟨readBound, workBound⟩ := (T).uniform.choose_spec z v.2 wo wi u
  refine ⟨out, List.replicate 4 (.tick : Event bits) ++ es, first.trans run, ?_, ?_, ?_, pc',
    pers'.trans pers,
    fun j hj => (frame' j (fun _ => hj _)).trans (frame j (hj _) (hj _)),
    fun q hq hn => (mem q hq hn).trans (congrFun priv q), ?_⟩
  · rw [List.length_append, List.length_replicate]
    have h := len.trans workBound
    change 4 + es.length ≤ ((T).uniform.choose + 4) * (wo + wi + u + 1)
    rw [Nat.add_mul]
    have four : 4 ≤ 4 * (wo + wi + u + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · rw [countProbes_append, probes]
    change 0 + _ ≤ (T).uniform.choose + 4
    dsimp only at readBound
    split <;> omega
  · rw [PrimedInputRAM.Flow.choiceBits_append, path]; rfl
  · intro l
    rw [hits, priv]; rfl

/-- The fixed capacity requirements hold simultaneously up to the scalar cache in
any polynomial bound on the number of absolute descriptor addresses. -/
theorem eventually_body_capacity (degree labels b : ℕ) (hb : 1 ≤ b) (nodes : ℕ → ℕ)
    (bound : PolynomiallyBounded nodes) :
    ∀ᶠ n : ℕ in Filter.atTop, MapWorkspace.Capacity B.refresh (CursorBounds.wordBits b n) n
      (TerminalLayout.privateRegions degree n (nodes n) labels).cacheBase :=
  MapWorkspace.eventually_capacity (B := B.refresh) b hb _ <|
    ((PolynomiallyBounded.id.add (bound.mul (NodeArguments.frameStride_bounded degree))).add
      (.const labels)).add (PolynomiallyBounded.id.pow 5)

theorem copies_le : u ≤ Fintype.card (Tie D) * X.maxWireWidth := by
  apply term_repetitions_le B.refresh
  intro e
  change blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) v.1 e ≤ _
  unfold blockDemandWidths internalWidth
  split <;> exact X.width_le_maxWireWidth _

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
