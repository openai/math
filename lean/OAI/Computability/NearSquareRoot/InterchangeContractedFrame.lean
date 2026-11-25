import OAI.Computability.NearSquareRoot.InterchangeCompiledAtlas
import OAI.Computability.NearSquareRoot.InterchangeStagePhysicalCost
import OAI.Computability.NearSquareRoot.InterchangeBatchIndices

/-!
# A single physical atlas and radix satisfying the recursion contraction

The last group of radix digits can be incomplete. Choosing the common
specialization prime larger than the number of independent label rows makes
its padding affordable in the same inequality as the occupied reserve.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Filter OAI.LinearAlgebra.FiniteFourier IntegerMultiplication.Port

theorem packed_price_lt {b W m ncall : ℕ} {γ : ℝ} (hW : 0 < W) (hb : W < b) (hm : 0 < m)
    (hn : (ncall : ℝ) ≤ (W : ℝ)*(m : ℝ)^γ) :
    ((ncall * BatchRows.groups b W : ℕ) : ℝ) / b < 2*(m : ℝ)^γ := by
  have hvol := BatchRows.groups_volume_lt (b:=b) hW
  have hvol' : (W : ℝ) * BatchRows.groups b W < 2*(b : ℝ) := by
    exact_mod_cast (show W * BatchRows.groups b W < 2*b by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb' : (0 : ℝ) < b := by exact_mod_cast hW.trans hb
  apply (div_lt_iff₀ hb').mpr
  push_cast
  calc
    _ ≤ ((W : ℝ)*(m : ℝ)^γ)*BatchRows.groups b W :=
      mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _)
    _ = ((W : ℝ)*BatchRows.groups b W)*(m : ℝ)^γ := by ring
    _ < (2*(b : ℝ))*(m : ℝ)^γ := mul_lt_mul_of_pos_right hvol' (Real.rpow_pos_of_pos hm' _)
    _ = _ := by ring

/-- One choice supplies the source and destination Gram diagrams, a legal
P192 instruction catalog for every prime-power width, and contraction of the
actual packed request budget. The prime may also specialize any given finite
catalog of extra rational coefficients. -/
theorem exists_contracted_frame {α γ : ℝ} (hγ : 1/2 < γ) (ha : γ < α) :
    ∃ p : ℕ, ∃ hp : Fact p.Prime, 2 < p ∧ ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      let q := 2^k
      let a := (2*p-1)*Fintype.card (Word p q)
      let W := independentRows m * Fintype.card (Label p q)
      let r := hammingRectangle (p:=p) (k:=k) (hp:=hp.out.pos)
      ∃ atlas : RectangleAtlas r a, ∀ (threshold : ℕ) (extra : Finset ℚ),
        ∃ b : ℕ, b.Prime ∧ max threshold W < b ∧ ∃ code : ℚ → Pinpoint b,
          (∀ x ∈ extra, (code x = none ↔ x = 0) ∧ ∀ f, Token x ((code x).stamp f)) ∧
          Nonempty (RectangleAtlas.Frame atlas m b) ∧
          let packed := @batchCalls p k m 108 hp * BatchRows.groups b W
          (packed : ℝ)/b < 2*(m : ℝ)^γ ∧ (packed : ℝ)/b + 2*a < (m : ℝ)^α := by
  obtain ⟨p,hp,hodd,hbatch⟩ := exists_contracted_batch hγ ha 108
  let := hp
  refine ⟨p,hp,hodd,?_⟩
  filter_upwards [hbatch,eventually_gt_atTop (0:ℕ)] with m hm hmpos
  obtain ⟨k,hcost,hspace⟩ := hm
  let q := 2^k
  let a := (2*p-1)*Fintype.card (Word p q)
  let W := independentRows m * Fintype.card (Label p q)
  have hW : 0 < W := by
    apply Nat.mul_pos
    · simp only [independentRows,componentWidth,SwapRepair.width,SwapRepair.BasisIndex,
        primePredictorRows,Fintype.card_fin,countPencilOrder]
      positivity
    · apply Fintype.card_pos_iff.mpr
      exact ⟨fun _ _ => ⟨0, by dsimp [q]; positivity⟩⟩
  obtain ⟨atlas⟩ := hamming_atlas p k hp.out.pos
  refine ⟨k,atlas,?_⟩
  intro threshold extra
  obtain ⟨b,hb,hlarge,code,hcode,hframe⟩ := atlas.compile_frame m (max threshold W) extra
  refine ⟨b,hb,hlarge,code,hcode,hframe,?_⟩
  have h₁ := packed_price_lt hW ((le_max_right threshold W).trans_lt hlarge) hmpos
    (ncall := batchCalls p k m 108) (γ:=γ) (by simpa only [W,Nat.cast_mul] using hcost)
  refine ⟨h₁, (add_lt_add_left h₁ _).trans ?_⟩
  simpa only [Word,Fintype.card_fun,Fintype.card_fin] using hspace

end Interchange

end NearSquareRoot
end Computability
end OAI
