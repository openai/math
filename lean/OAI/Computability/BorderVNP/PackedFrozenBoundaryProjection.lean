import OAI.Computability.BorderVNP.PackedFrozenSelectedPre
import OAI.Computability.BorderVNP.PackedFrozenSelectedReturn
import OAI.Computability.BorderVNP.PackedFrozenSeedInitial

/-! # All-word geometry of the initial, prepared and returned frozen frames -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape ProgramSchemas EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap w)
    (base : Format) (t : ℕ) (ht : t<T)

local notation3 "geo" j => S.source.StatePins S.last (S.high (offset S start t))
  (fun z => (before S start t z).sites) (fun z => (before S start t z).edges) w j
local notation3 "outer" j => Boundary.Pins S start (boundaryShape S start) w j
local notation3 "full" j => outerPins S start w base j

/-- Every geometry bit entering the inner history is the original subdivision
bit, for arbitrary child words including all padding and tape payloads. -/
theorem tapePre_geometry (ports : WorkWords.Ports (portSlots S start t 0)) (fit : (before S start t 0).sites ≤ 2^w)
    (x : Fin (fan S) × (full t) → Bool) (i : Fin (fan S)) (j : geo 0) :
    (R.tapePre base t ht ports fit).eval x (i,.inl (.inl j)) =
      (R.machine t ht).pre.eval (fun z => x (z.1,.inl (.inl z.2))) (i,j) :=
  (R.tapePre_width base t ht ports fit x i (.inl j)).trans
    ((R.atLevel t ht).widthPre_geo rfl ports fit (fun i z => x (i,.inl z)) i j)

/-- The final placement uses exactly the original child and root geometry
for every input, including roots produced by rejected histogram words. -/
theorem tapePost_geometry (x : Fin (fan S) × (full t) → Bool) (y : stagePins S start w base t S.rounds → Bool)
    (j : outer (t+1)) :
    (R.tapePost base t ht).eval (Sum.elim x y) (.inl (.inl j)) =
      (R.machine t ht).post.eval (Sum.elim (fun z => x (z.1,.inl (.inl z.2))) (fun z => y (.inl (.inl z)))) j :=
  (forwardRoot_post (R.atLevel t ht).widthPost x y (.inl j)).trans
    ((R.atLevel t ht).widthPost_geo (fun z => x (z.1,.inl z.2)) (y ∘ Sum.inl) j)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch Shortening Packing Packing.Inherited Packing.Inherited.FrozenTape
open Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace TeamContraction ParseBatch ParseBatchVerifier Prewire
open SelectedSchedule TeamScales VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable {σ : Type} [Fintype σ] (f : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*logWidth r n) 0))

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 5000 in
/-- The actual initialized tape and width fields project to the geometric
bottom frame on every public input assignment. -/
theorem seedTapeFrame_geometry (x : σ → Bool) :
    (seedTapeFrame S plan G order position f).eval x ∘ (fun j => .inl (.inl j)) = f.eval x := by
  have first : (seedTapeFrame S plan G order position f).eval x ∘ Sum.inl =
      (seedWidthFrame S plan f).eval x := funext fun j => parallelFrame_eval_inl ..
  have second : (seedWidthFrame S plan f).eval x ∘ Sum.inl = f.eval x := by
    unfold seedWidthFrame
    exact WorkWords.BottomPrep.frame_geometry ..
  exact (congrArg (· ∘ Sum.inl) first).trans second

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
