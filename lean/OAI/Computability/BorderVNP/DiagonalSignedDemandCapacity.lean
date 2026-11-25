import OAI.Computability.BorderVNP.DiagonalSignedSewnWidth
import OAI.Computability.BorderVNP.DiagonalSignedSewnCellLoads
import OAI.Computability.BorderVNP.PackedOriginalDescriptionRows
import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups

/-! # The signed history's actual receiving cells and native label budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing PhysicalEpochs DeckGrid
open Diagonal Diagonal.ExternalSew TeamContraction TeamScales Filter EnrichedOuter
open ParseBatch ParseBatchVerifier Prewire VPVNP
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxRecDepth 6000
set_option maxHeartbeats 2400000

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {n r d T copies header work R ell X : ℕ}
    (plan : SeedPlan S n r d T copies header work)
local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "block" => GridHosts.inputBlockWidth r n axes d
local notation "mass" => initialMass (D := D) n r d copies header
local notation "admit" => Boundary.Good (S:=S) (start:=d+1)
  (bits:= fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) => copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
  (shape:=boundaryShape S (d+1)) (w:=60*logWidth r n) (boundaryBudget S mass)
local notation "cap" => seedBoxCapacity n r axes d (Fintype.card (Direction axes))
local notation "desc" => seedDescriptionWidth n r axes d (header*logWidth r n) (BottomGridBank.bodyBudget cap)

variable (count : (fan S)^T*copies = R+1)
    {time pins inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r time pins ell inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (pos : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {g : ℕ} {len : Fin n} {st : Fin g} (W : WiredWitness G len D (Fintype.card (Cube D)) d order st)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order pos copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundaryShape S (d+1)) (60*logWidth r n) 0 → Bool)
local notation "initialState" => Boundary.seedState S G d order pos copies table words
variable (ready : Boundary.Good (S:=S) (start:=d+1)
    (bits:=fun _ : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) =>
      copies*GridHosts.inputBlockWidth r n (Fintype.card (Cube D)) d)
    (shape:=boundaryShape S (d+1)) (w:=60*logWidth r n)
    (boundaryBudget S (initialMass (D:=D) n r d copies header)) 0
    (Boundary.seedState S G d order pos copies table words))
local notation "bottom" => (Subtype.mk initialState ready : Admissible admit 0)
local notation "M" => plan.compiled.machine
local notation "dir" => freeDirectory R r (G.program.length+time) ell tiles block ((fan S)^T*tiles) desc
local notation "data" => Boundary.seedBirthFields (G:=G) (D:=D) (d:=d) (order:=order) (len:=len) (state:=st) W pos tag sites edges ports copies desc

/-- Both the actual delivery weights and each descriptor's receiving site are
charged on the same attained history of the signed evaluator. -/
theorem signed_directory_resources (widths : plan.SewnWidths count ell X (1/2)) (loads : plan.SewnCellLoads count ell)
    {cells : ℕ} (number : (Cube D → Deck (depth S (d+1) T+1)) ≃ Fin cells)
    (q : (packHistory bottom (M).epoch T).Index) :
    let state := ((packHistory bottom (M).epoch T).term q).val
    let N := enrichedSewnLayout G axes d order pos count M bottom rfl q
    let base := data
    let fields := (M).historyFields bottom (base true) T q
    let cell (v : N.Site) := number (reduceMove (depth S (d+1) T) (state.route.origin v))
    let old := originalDescriptionRows M bottom q dir rfl order
    (∀ j, desc ≤ fields.payload (old j)) ∧ intercellWidth N cell ≤ 2*(R+1)*X ∧
      ∀ c, localRecords N true fields.prior fields.payload (fun v => cell v=c) ≤ TeamScales.width n (1/5) := by
  intro state N base fields cell old
  let tile := fun v : N.Site => reduceMove (depth S (d+1) T) (state.route.origin v)
  have ren : intercellWidth N cell = intercellWidth N tile := by
    unfold intercellWidth
    congr 1
    funext edge
    exact propext (not_congr number.injective.eq_iff)
  have copiesPos : 0 < copies := Nat.pos_of_ne_zero (fun hz => by rw [hz,Nat.mul_zero] at count; omega)
  have bound (v) : desc ≤ (base true).payload v := (Nat.le_mul_of_pos_left _ copiesPos).trans (Nat.le_add_left _ _)
  have measured := (widths G order pos table words ready q).2.2 le_rfl
  refine ⟨originalDescriptionRows_payload M bottom q dir rfl order (base true) bound,?_,?_⟩
  · rw [ren]
    exact measured.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0<2)))
  · intro c
    have measured := (loads G order pos W tag sites edges ports table words ready q (number.symm c)).2
    have test : (fun v : N.Site => cell v=c) = (fun v : N.Site => tile v=number.symm c) :=
      funext fun _ => propext number.eq_symm_apply.symm
    rw [test]
    exact measured

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
