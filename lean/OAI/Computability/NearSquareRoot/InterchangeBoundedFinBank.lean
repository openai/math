import OAI.Computability.NearSquareRoot.InterchangeConfiguredBank
import OAI.Computability.NearSquareRoot.InterchangeBQuestAddress
import OAI.Computability.NearSquareRoot.InterchangeBoundedRows

/-!
# Bounded physical input and output for one packed Hamming batch

The bank numbering changes no tape order. The bounded splitter and merger
preserve the same child list, child predicate and charge when acting on the
full original record stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageKernel

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangePayloadBank InterchangeAddress InterchangeSpectralFibre RepairSchedule InterchangeSpace

variable {p k m b : ℕ} [Fact p.Prime] [NeZero b] {I : Type} {D : I → Type}
  {r : Regime I} {l : I → ℕ}

variable (K : StageKernel p k m) (atlas : RectangleAtlas (nodeRectangles p k) (hammingReserve p k))
  (P G S : I → Tape) (f : I → ℕ) (payload : (i : I) → Series (D i)) (src : ZMod p → Tree)

local notation "ord" => Equiv.refl (PhysicalSlots p k m)
local notation "width" => bankWidth p k m
local notation "slots" => mainSlots (hammingReserve p k) m

omit [NeZero b] in
/-- Transport a packed scalar program at the native row geometry to the row
numbers produced by the physical splitter. -/
theorem bounded_bank_run_of (lanes : Series (PackedPencil.Index m)) (labels : Series (HammingLabels p k))
    (machine : ∀ v : (i : I) → (PackedPencil.Index m × HammingLabels p k) →
      domain (J:=PhysicalSlots p k m) (b:=b) P G S f i × D i → ZMod p,
      BChargedTyped (b:=b) (r:=r) (l:=l) ord P G S f (Good payload src) (K.calls atlas)
        (render (layoutRows ord P G S f) payload (lanes.cart labels) src v)
        (render (layoutRows ord P G S f) payload (lanes.cart labels) src
          (fun i rw z => v i rw (swapMain slots z.1,z.2))))
    (v : Fin width → (i : I) → domain (J:=PhysicalSlots p k m) (b:=b) P G S f i → Tree)
    (good : ∀ u i x, Good payload src i (v u i x)) :
    BChargedTyped (b:=b) (r:=r) (l:=l) ord P G S f (Good payload src) (K.calls atlas)
      (FinBank.packet (layoutRows ord P G S f) v)
      (FinBank.packet (layoutRows ord P G S f) (fun u i => v u i ∘ swapMain slots)) :=
  FinBank.lift_rows (layoutRows _ P G S f) payload src _ (packed_count lanes labels) _ _ machine v good

omit [NeZero b] in
/-- Enclose the main-coordinate permutation between the actual splitter and
merger. The two reserve families remain in their original order at this step. -/
theorem bounded_main_of_bank (hb : width < b) (hf : r.Has (tally ∘ f))
    (hP : Told r P) (hG : Told r G) (hS : Told r S)
    (v : BatchFrame.Value (J:=PhysicalSlots p k m) (b:=b) P G S f b)
    (hv : Manifest _ l v) (gv : ∀ i x, Good payload src i (v i x))
    (run : ∀ w : Fin width → BatchFrame.Value (J:=PhysicalSlots p k m) (b:=b) P G S f
        (BatchRows.groups b width), (∀ u i x, Good payload src i (w u i x)) →
      BChargedTyped (b:=b) (r:=r) (l:=l) ord (BatchFrame.front P (BatchRows.groups b width)) G S f
        (Good payload src) (K.calls atlas)
        (BatchFrame.packet ord P G S f w)
        (BatchFrame.packet ord P G S f (fun u i => w u i ∘ swapMain slots))) :
    BHop (Request.job b) r (fun i => (BatchFrame.rows (b:=b) ord P G S f b i).count) l
      (rowZone (p:=p) (k:=k) (m:=m) (l:=l) P G S f payload src) (K.calls atlas)
      (together r.header (stackRun (BatchFrame.rows (b:=b) ord P G S f b) v))
      (stackRun (BatchFrame.rows (b:=b) ord P G S f b) (fun i => v i ∘ swapMain slots)) := by
  have hw := bankWidth_pos p k m
  apply OuterReserves.bounded_with_rows_main (hammingReserve p k) m P G S f hw hb hf hP hG hS v hv
  exact run _ fun _ i _ => gv i _

end Interchange.StageKernel

end NearSquareRoot
end Computability
end OAI
