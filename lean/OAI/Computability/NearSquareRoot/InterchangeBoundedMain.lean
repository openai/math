import OAI.Computability.NearSquareRoot.InterchangeBoundedFinBank
import OAI.Computability.NearSquareRoot.InterchangeBQuestRepairGroup

/-!
# The space-bounded main swap for the native recursive node

The compiled repair group supplies the permutation on all independent rows.
After physically splitting a radix digit, the same result applies to its
padded rows and the ordinary merger returns the exact main-coordinate swap.
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
  {atlas : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)}
  (K : StageKernel p k m) (frame : RectangleAtlas.Frame atlas m b)
  (P G S : I → Tape) (f : I → ℕ)

local notation "ord" => Equiv.refl (PhysicalSlots p k m)
local notation "width" => bankWidth p k m
local notation "slots" => mainSlots (hammingReserve p k) m

include frame

/-- The bank produced by the splitter accepts every set of valid packed rows. -/
theorem bounded_bank_run (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hP : Told r P) (hG : Told r G) (hS : Told r S)
    (payload : (i : I) → Series (D i)) (hd : ∀ i, (payload i).count ≤ l i)
    (src : ZMod p → Tree) (hs : Function.Injective src)
    (v : Fin width → (i : I) → domain (J:=PhysicalSlots p k m) (b:=b) P G S f i → Tree)
    (good : ∀ u i x, Good payload src i (v u i x)) :
    BChargedTyped (b:=b) (r:=r) (l:=l) ord P G S f (Good payload src) (K.calls atlas)
      (FinBank.packet (layoutRows ord P G S f) v)
      (FinBank.packet (layoutRows ord P G S f) (fun u i => v u i ∘ swapMain slots)) := by
  let lanes := Series.arbitrary (PackedPencil.Index m)
  let labels := Series.arbitrary (HammingLabels p k)
  exact K.bounded_bank_run_of atlas P G S f payload src lanes labels
    (K.execute_group_bounded frame P G S f hb hf hP hG hS payload hd src hs lanes labels) v good

/-- Native width-`f` recursive calls perform the batched main swap on arbitrary
admissible packed trees. All charged children lie in the padded-row zone. -/
theorem bounded_main_admissible (hb : width < b) (hf : r.Has (tally ∘ f))
    (hP : Told r P) (hG : Told r G) (hS : Told r S)
    (payload : (i : I) → Series (D i)) (hd : ∀ i, (payload i).count ≤ l i)
    (src : ZMod p → Tree) (hs : Function.Injective src)
    (v : BatchFrame.Value (J:=PhysicalSlots p k m) (b:=b) P G S f b)
    (hv : Manifest _ l v) (gv : ∀ i x, Good payload src i (v i x)) :
    BHop (Request.job b) r (fun i => (BatchFrame.rows (b:=b) ord P G S f b i).count) l
      (rowZone (p:=p) (k:=k) (m:=m) (l:=l) P G S f payload src) (K.calls atlas)
      (together r.header (stackRun (BatchFrame.rows (b:=b) ord P G S f b) v))
      (stackRun (BatchFrame.rows (b:=b) ord P G S f b) (fun i => v i ∘ swapMain slots)) := by
  have hw := bankWidth_pos p k m
  exact K.bounded_main_of_bank atlas P G S f payload src hb hf hP hG hS v hv gv <|
    K.bounded_bank_run frame _ G S f (by omega) hf (BatchFrame.told_front P hw hb hP)
      hG hS payload hd src hs

end Interchange.StageKernel

end NearSquareRoot
end Computability
end OAI
