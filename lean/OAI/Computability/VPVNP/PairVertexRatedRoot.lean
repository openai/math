import OAI.Computability.VPVNP.PairVertexRatedRow
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost
import OAI.Computability.VPVNP.PairVertexOrdinalLiveCosts
import OAI.Computability.VPVNP.PairVertexRootOrdinal
import OAI.Computability.VPVNP.PairVirtualVertexRoot

/-! # Measured ordinal calls initialized by the physical root gather -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM Compression DFS LocalHistory NodeArguments TraversalRows TreeDecode
open CompressorRecords.SourceTransport LeafSourceLoad
open scoped Fin.CommRing

variable {k K : Type*} [Field k] [CommRing K] {S : BlockSchedule k}
    (B : S.Templates) (κ : B.Entry → K) (hκ : B.IsSolution κ) {lanes : ℕ}
    (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (z : (B.execute κ hκ T hT X).Choices) (rowBase : ℕ)
    {geometry rootFields leaf shrink refresh : Segment} {p r w g : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r) (M : Machine w p r 11)
    (m : Memory w) (base grammar : ℕ) (order : Fin g ≃ B.Entry) (P : SiteParsers κ X.network)
    (half : ∀ u, ((B.execute κ hκ T hT X).finalState z).network.Half u)
    (cap : ℕ) (i : Fin (siteOrder ((B.execute κ hκ T hT X).finalState z)).length)
    (degree bound n power scan nodeCap : ℕ) (vals : Static 34 → Word w)
    (format : Packet → Prop) (desc : ℕ → List ℕ)
    (domain : Word w → Scratch w (M.publicData 6).val → Prop)
    (handlers : NodeDispatch.Role → HookParser w (M.publicData 6).val)

local notation "E₀" => B.execute κ hκ T hT X
local notation "Y₀" => StateExecution.finalState (E₀) z
local notation "v₀" => Order.entries (siteOrder (Y₀)) i
local notation "tree₀" => selectedTrees B κ hκ T hT X z rowBase (v₀)
local notation "packet₀" => Packet.mk (VertexTree.address (tree₀)) (packed (Y₀) (v₀) (half (v₀)))
local notation "chain₀" => StateExecution.termChain (E₀) (B.records κ hκ T hT X) z
local notation "N₀" => Fin.val (Machine.publicData M 6)
local notation "H₀" => TerminalLink.header (Machine.publicData M)
local notation "role₀" => m (Fin.val ((H₀) + 14))
local notation "area₀" => NativeFrame.fromHeader degree (Machine.publicData M) (H₀) m
local notation "leaf₀" => NativeFrame.leafWords degree (Machine.publicData M) (H₀) (role₀) m
local notation "fields₀" => NativeFrame.fields degree (Machine.publicData M) (H₀) (role₀) m
local notation "valid₀" => Budgeted (LeafArena.Regions.arguments (area₀)) format
  (VertexFrameData (area₀) (leaf₀) (role₀) vals) desc
  (privateHistogram order (LeafArena.Regions.histBase (area₀))) nodeCap ((N₀) * nodeCap)

/-- A successful gather and verified selected role programs give a row
whose clock and probe estimates refer to that same physical execution. -/
theorem RootRun.ratedOrdinal
    (root : RootRun A M m (i.val : Word w) degree (S.degreeExponent 0) bound (packet₀) vals)
    (checked : SelectedChecks B κ hκ T hT X z rowBase A M m
      ((NativeFrame.frameBase (area₀)) : Word w) (role₀) (LeafArena.Regions.histBase (area₀))
      order P (valid₀) domain handlers (ordinalJobCost n power scan))
    (type : format (packet₀)) (children : subtreeAddresses desc (packet₀) = (tree₀).preorder)
    (rows : AllRows w m B.recordLimit rowBase rowBase (selectedLayers B κ hκ T hT X z))
    (space : rowBase + words B.recordLimit (selectedLayers B κ hκ T hT X z) ≤ (H₀).val)
    (headerFit : (H₀).val + 31 < 2 ^ w)
    (cacheFit : (area₀).cacheBase + 38 ≤ 2 ^ w)
    (capacity : B.growthConstant ^ T ≤ N₀) (external : base + grammar + g ≤ (H₀).val)
    (hbase : M.publicData 4 = (base : Word w)) (hgrammar : M.publicData 5 = (grammar : Word w))
    (hg : M.publicData 9 = (g : Word w))
    (cacheTime : ∀ t ≤ bound, t + degree + 187 ≤ 44 + n ^ 3)
    (clock : ∀ t ≤ bound,
      t + degree + 187 + (15 + 21 * S.baseDegree + 5 * (packet₀).bits.length) +
        (15 + n ^ 43) * (chain₀).occurrences (fun _ => 1) (v₀) + 7 * g + 46 ≤ cap) :
    Nonempty (RatedOrdinal B κ hκ T hT X z rowBase A M base grammar order P
      half cap m i n power scan) := by
  obtain ⟨t,ht,cfg,pre,ready,ticks,probes,det,same,reads,run⟩ := root.run
  have labelCount : (area₀).histWords = g := by
    change (M.publicData 9).val = g
    rw [hg,Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  subst g
  have positive : 0 < N₀ :=
    lt_of_lt_of_le (pow_pos (by have := B.growthConstant_ge_two; omega) _) capacity
  have above : N₀ ≤ (area₀).histBase := Nat.le_add_right _ _
  have measure := ordinal_prefix_bounds (Y₀) (v₀) (half (v₀)) pre t degree n
    probes ticks (cacheTime t ht)
  let row := OrdinalRows.ofRoot B κ hκ T hT X z rowBase A M m base grammar order P half cap i
    (area₀) (leaf₀) (fields₀) vals (role₀) nodeCap (n ^ 43) format desc
    domain handlers
    (ordinalJobCost n power scan) checked cfg pre ready run det same reads rfl rfl rfl
    positive above cacheFit type children rows space headerFit capacity external hbase hgrammar hg
    (fun _ h => h.2) (ticks ▸ clock t ht)
  exact ⟨row,measure.1,measure.2,fun _ h => h.1,le_rfl⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
