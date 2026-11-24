import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory
import OAI.Computability.VPVNP.CompressorCurrentGraph
import OAI.Computability.VPVNP.CompressorBlockLevelFit

/-!
# Native refresh records retained by the selected history

A refresh reads its selected demands and terms from its own level. The
successor contributes six incidence pointers and the packed graph itself.
The old header supplies the traversal arena and its frame stride.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPayloadHistory

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh DescriptorSpace
open PortRefresh PortRefresh.Allocation SourceTransport
set_option maxHeartbeats 1600000

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w g : ℕ} (L : Layout) (i n : ℕ) (X : State S.portExponent (S.portExponent+g))
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)
variable (choice : DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph
  (Nat.two_pow_pos S.expanderExponent) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh S.port_order (And.right S.degree_bounds) choice
local notation "s" => RefreshBlockPlan.shape B
local notation "start" => arrayBase L i
local notation "P" => plan X (S.degreeExponent 0) (LevelRecipe.Shape.dH s) (LevelRecipe.Shape.ties s) (LevelRecipe.Shape.stride s) start
local notation "oldDir" => packedIncidence L w i (X.positions*2^S.portExponent)
local notation "newDir" => packedIncidence L w (i+1) (State.positions Y*2^(S.degreeExponent 0))

/-- The selected refresh's native term, old and new graphs, and DFS arena. -/
structure Data (m : Memory w) : Prop where
  fits : (P).segments ≤ 2^w
  stored : Build.Stored X S.graph hE hC B.refresh choice (RefreshBlockPlan.order B) start (s).stride fits m
  old : (oldDir).Represents X m
  new : (newDir).Represents Y m
  geometry : TraversalHeaders.Geometry (Fintype.card X.Base) g (levelStart L i) (levelStart L (i+1)) start
    ⟨n,PairSimulation.NodeArguments.frameStride (slotDegree S) n⟩ oldDir newDir m

/-- Only the successor's six pointer words occur in the refresh header readback. -/
theorem keep_geometry {V lanes oldHead newHead scratch : ℕ} {A : PairSimulation.NodeArguments.Arena}
    {T U : IncidenceDirectory w} {m out : Memory w}
    (h : TraversalHeaders.Geometry V lanes oldHead newHead scratch A T U m)
    (old : ∀ j ≤ 60, out (oldHead+j) = m (oldHead+j))
    (new : ∀ c : Fin 6, out (newHead+54+c.val) = m (newHead+54+c.val)) :
    TraversalHeaders.Geometry V lanes oldHead newHead scratch A T U out := by
  refine ⟨h.oldRoom,h.newRoom,(old 0 (by decide)).trans h.vertices,(old 3 (by decide)).trans h.residual,
    (old 17 (by decide)).trans h.arena,(old 18 (by decide)).trans h.stride,?_,
    fun c => (new c).trans (h.newIncidence c),(old 60 le_rfl).trans h.scratch⟩
  intro c
  rw [Nat.add_assoc,old _ (by have := c.isLt; omega),← Nat.add_assoc]
  exact h.oldIncidence c

/-- Transport a physical incidence directory whose row count is computed
from the state's positions, as in the native copy packet. -/
theorem keep_incidence {L : Layout} {a l : ℕ} (j : Fin L.levels) (Z : State a l)
    {m out : Memory w} (room : endAddress L < 2^w) (size : Z.positions*2^a ≤ slotCapacity L)
    (h : (packedIncidence L w j (Z.positions*2^a)).Represents Z m)
    (same : ∀ x, incidenceStart L j ≤ x → x < arrayBase L j → out x = m x) :
    (packedIncidence L w j (Z.positions*2^a)).Represents Z out := by
  have rows : Z.positions*2^a = IncidenceDirectory.slotCount Z := by
    rw [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv l),Fintype.card_fin]
  rw [rows] at size h ⊢
  exact CurrentGraph.incidence_keep L j Z room size h same

variable {B L i n X choice}

/-- On a native block layout the selected records survive every later write
that agrees on the completed level and the successor's graph cells. -/
theorem Data.transfer {m out : Memory w} (data : Data B L i n X choice m)
    {base positions blocks : ℕ} (layout : L = BlockProgram.layout B base positions blocks)
    (live : i+1 < L.levels) (size : X.positions ≤ positions) (room : endAddress L < 2^w)
    (same : Agree (SelectedPayloadHistory.Cells L i) m out) : Data B L i n X choice out := by
  let cur : Fin L.levels := ⟨i,by omega⟩
  let nxt : Fin L.levels := ⟨i+1,live⟩
  have endpoint := (BlockLevelFit.refresh B base positions blocks cur layout X size room).1
  change BlockLevelFit.Endpoint w L i 0
    (plan X (S.degreeExponent 0) (s).dH (s).ties (s).stride (start+0*tableWords L)).stop at endpoint
  simp only [Nat.zero_mul,Nat.add_zero] at endpoint
  have before : (P).supply ≤ (P).stop := by
    unfold Plan.stop Plan.next Plan.reverseSlot Plan.targetPort
    omega
  have fields : L.shape.scalarFields = 54 := layout ▸ rfl
  have tables : L.shape.tables = 6 := layout ▸ rfl
  have span : levelStart L i+60 < levelStart L (i+1) := by
    simp only [levelStart,Nat.succ_mul,levelWords,levelHeaderWords,fields,tables]
    omega
  have oldEnd : start ≤ levelStart L (i+1) := by
    simp only [arrayBase,incidenceStart,levelStart,Nat.succ_mul,levelWords]
    omega
  have lower : levelStart L i ≤ start := by unfold arrayBase incidenceStart; omega
  have oldSize : X.positions*2^S.portExponent ≤ slotCapacity L := by
    rw [layout]
    exact Nat.mul_le_mul size (le_max_left ..)
  have outputSize := dyadicRefreshNext_positions X S.graph hE hC B.refresh S.port_order (And.right S.degree_bounds) choice
  have nextDegree : 2^(S.degreeExponent 0) ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right ..)
  have newSize : (Y).positions*2^(S.degreeExponent 0) ≤ slotCapacity L := by
    rw [layout]; exact Nat.mul_le_mul (outputSize.le.trans size) nextDegree
  refine ⟨data.fits,SelectedPayloadHistory.refresh_stored data.stored le_rfl endpoint.word.le lower (before.trans endpoint.next) same,
    keep_incidence cur X room oldSize data.old ?_,keep_incidence nxt Y room newSize data.new ?_,
    keep_geometry data.geometry ?_ ?_⟩
  · intro x lo hi
    exact (same x (Or.inl ⟨(Nat.le_add_right ..).trans lo,hi.trans_le oldEnd⟩)).symm
  · intro x lo hi
    apply (same x (Or.inr ⟨?_,hi⟩)).symm
    exact (by unfold incidenceStart levelHeaderWords; dsimp [nxt]; omega : _ ≤ incidenceStart L nxt).trans lo
  · intro j hj
    exact (same _ (Or.inl ⟨Nat.le_add_right ..,(Nat.add_le_add_left hj _).trans_lt span⟩)).symm
  · intro c
    apply (same _ (Or.inr ⟨?_,?_⟩)).symm
    · rw [fields]; exact Nat.le_add_right ..
    · unfold arrayBase incidenceStart levelHeaderWords
      rw [fields,tables]; have := c.isLt; omega

end CompressorRecords.RefreshPayloadHistory

end VPVNP
end Computability
end OAI
