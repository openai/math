import OAI.Computability.NearSquareRoot.InterchangeFinBank
import OAI.Computability.NearSquareRoot.InterchangeRepairPhysical

/-!
# Passing the native packed row group to the Hamming interchange

The splitter enumerates the original rows by one natural number. Number the
ordered pair of a packed pencil lane and a label by its position in precisely
that physical enumeration. This identifies the spectral-predictor row bank
with the splitter packet, including padding in the final radix group.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageKernel

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangePayloadBank InterchangeAddress InterchangeSpectralFibre RepairSchedule

variable {p k m b : ℕ} [Fact p.Prime] [NeZero b] {I : Type} {D : I → Type}
  {r : Regime I} {l : I → ℕ}

noncomputable abbrev bankWidth (p k m : ℕ) := independentRows m * Fintype.card (HammingLabels p k)
abbrev PhysicalSlots (p k m : ℕ) := Fin (hammingReserve p k + m + hammingReserve p k)

theorem bankWidth_pos (p k m : ℕ) : 0 < bankWidth p k m := by
  apply Nat.mul_pos
  · simp only [independentRows,componentWidth,SwapRepair.width,SwapRepair.BasisIndex,
      OAI.LinearAlgebra.FiniteFourier.primePredictorRows,Fintype.card_fin,OAI.LinearAlgebra.FiniteFourier.countPencilOrder]
    positivity
  · apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ _ => ⟨0,by positivity⟩⟩

omit [Fact p.Prime] in
theorem packed_count (lanes : Series (PackedPencil.Index m)) (labels : Series (HammingLabels p k)) :
    (lanes.cart labels).count = bankWidth p k m := by
  simp only [Series.total,PackedPencil.Index,bankWidth,independentRows,componentWidth,
    Fintype.card_prod,Fintype.card_fin]

variable (K : StageKernel p k m) (atlas : RectangleAtlas (nodeRectangles p k) (hammingReserve p k))
  (P G S : I → Tape) (f : I → ℕ) (payload : (i : I) → Series (D i)) (src : ZMod p → Tree)

local notation "ord" => Equiv.refl (PhysicalSlots p k m)
local notation "width" => bankWidth p k m
local notation "slots" => mainSlots (hammingReserve p k) m

omit [NeZero b] in
/-- Transport a packed scalar program at the native row geometry to the row
numbers produced by the physical splitter. -/
theorem bank_run_of (lanes : Series (PackedPencil.Index m)) (labels : Series (HammingLabels p k))
    (machine : ∀ v : (i : I) → (PackedPencil.Index m × HammingLabels p k) →
      domain (J:=PhysicalSlots p k m) (b:=b) P G S f i × D i → ZMod p,
      ChargedTyped (b:=b) (r:=r) (l:=l) ord P G S f (Good payload src) (K.calls atlas)
        (render (layoutRows ord P G S f) payload (lanes.cart labels) src v)
        (render (layoutRows ord P G S f) payload (lanes.cart labels) src
          (fun i rw z => v i rw (swapMain slots z.1,z.2))))
    (v : Fin width → (i : I) → domain (J:=PhysicalSlots p k m) (b:=b) P G S f i → Tree)
    (good : ∀ u i x, Good payload src i (v u i x)) :
    ChargedTyped (b:=b) (r:=r) (l:=l) ord P G S f (Good payload src) (K.calls atlas)
      (FinBank.packet (layoutRows ord P G S f) v)
      (FinBank.packet (layoutRows ord P G S f) (fun u i => v u i ∘ swapMain slots)) :=
  FinBank.lift_rows (layoutRows _ P G S f) payload src _ (packed_count lanes labels) _ _ machine v good

/-- Child predicate with the padded quotient present as an additional prefix
spectator. The original radix digit is still present in the parent stream. -/
abbrev rowZone (i : I) (x : Request b) :=
  (allowed f (countRows (b:=b) ord (BatchFrame.front P (BatchRows.groups b width)) G S f) l i x ∧
    ∀ u, Good payload src i (x.contents u)) ∧
      inherited b (BatchFrame.front P (BatchRows.groups b width) i) (G i) (S i) x

omit [NeZero b] in
/-- Enclose the main-coordinate permutation between the actual splitter and
merger. The two reserve families remain in their original order at this step. -/
theorem main_of_bank (hb : width < b) (hf : r.Has (tally ∘ f))
    (hP : Told r P) (hG : Told r G) (hS : Told r S)
    (v : BatchFrame.Value (J:=PhysicalSlots p k m) (b:=b) P G S f b)
    (hv : Manifest _ l v) (gv : ∀ i x, Good payload src i (v i x))
    (run : ∀ w : Fin width → BatchFrame.Value (J:=PhysicalSlots p k m) (b:=b) P G S f
        (BatchRows.groups b width), (∀ u i x, Good payload src i (w u i x)) →
      ChargedTyped (b:=b) (r:=r) (l:=l) ord (BatchFrame.front P (BatchRows.groups b width)) G S f
        (Good payload src) (K.calls atlas)
        (BatchFrame.packet ord P G S f w)
        (BatchFrame.packet ord P G S f (fun u i => w u i ∘ swapMain slots))) :
    Hopto (Request.job b) r (fun i => (BatchFrame.rows (b:=b) ord P G S f b i).count) l
      (rowZone (p:=p) (k:=k) (m:=m) (l:=l) P G S f payload src) (K.calls atlas)
      (together r.header (stackRun (BatchFrame.rows (b:=b) ord P G S f b) v))
      (stackRun (BatchFrame.rows (b:=b) ord P G S f b) (fun i => v i ∘ swapMain slots)) := by
  classical
  let F (i : I) (x : (PhysicalSlots p k m → Block b (f i)) × (PhysicalSlots p k m → Block b (f i))) :=
    (fun j => if j ∈ Set.range slots then x.2 j else x.1 j,
     fun j => if j ∈ Set.range slots then x.1 j else x.2 j)
  let bank := BatchFrame.padded (W:=width) P G S f (show 0 < b by omega) v
  have hg (u : Fin width) (i : I) (x) : Good payload src i (bank u i x) := gv i _
  apply BatchFrame.with_rows ord P G S f (bankWidth_pos p k m) hb hf hP hG hS F v hv
  exact run bank hg

end Interchange.StageKernel

end NearSquareRoot
end Computability
end OAI
