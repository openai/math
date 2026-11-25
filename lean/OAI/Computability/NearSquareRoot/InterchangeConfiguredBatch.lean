import OAI.Computability.NearSquareRoot.InterchangeContractedFrame
import OAI.Computability.NearSquareRoot.InterchangeCompiledPivot
import OAI.Computability.NearSquareRoot.InterchangePackedPencil

/-!
# Fixed control data and recursive cost of a Hamming interchange node

A single choice of rank minor, finite pencil, repair table and address atlas
serves every native input width. The stage price is computed on the actual
packed ground-field program and counts every independent basis component.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open OAI.LinearAlgebra.FiniteFourier Matrix StageRoute

abbrev HammingLabels (p k : ℕ) := Label p (2^k)
noncomputable abbrev HammingRank (p k : ℕ) [Fact p.Prime] :=
  Fin (hammingLabelMatrix p (2^k)).rank
noncomputable abbrev hammingReserve (p k : ℕ) :=
  (2*p-1)*Fintype.card (Word p (2^k))
noncomputable abbrev nodeRectangles (p k : ℕ) [Fact p.Prime] :=
  hammingRectangle (p:=p) (k:=k) (hp:=(Fact.out : p.Prime).pos)

/-- All the algebraic and finite table decisions needed by the predictor and
the repair step. -/
structure StageKernel (p k m : ℕ) [Fact p.Prime] where
  source : HammingRank p k → HammingLabels p k
  target : HammingRank p k → HammingLabels p k
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  matrix : Matrix (HammingRank p k) (HammingRank p k) (ZMod p)
  factor : (rectangleMatrix (K:=ZMod p) (nodeRectangles p k)).submatrix id target * matrix *
    (rectangleMatrix (nodeRectangles p k)).submatrix source id = rectangleMatrix (nodeRectangles p k)
  env : SwapRepair.Environment (ZMod p) m
  table : SwapRepair.Table (ZMod p) m
  correct : ∀ (C : Type) [LinearOrder C]
    (x : Fin (SwapRepair.width m) → SwapSpectrum.Row (Fin m) C (SwapRepair.Coeff (ZMod p) m)) i a,
    SwapRepair.run env table x i a = x i (SwapRepair.swapAll a)

namespace StageKernel

variable {p k m : ℕ} [Fact p.Prime]

theorem exists_kernel (p k m : ℕ) [Fact p.Prime] (hp : 2 < p) (hm : 2 ≤ m) :
    Nonempty (StageKernel p k m) := by
  let R := hammingLabelMatrix p (2^k)
  obtain ⟨I,J,hi,hj,_,hf⟩ := exists_skeleton R
  have odd := (Fact.out : p.Prime).odd_of_ne_two (Nat.ne_of_gt hp)
  have h2 : IsUnit (2 : ZMod p) := by
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 p).mpr odd.coprime_two_left
  obtain ⟨env⟩ := SwapRepair.exists_environment (ZMod p) h2 m
  obtain ⟨T,hT⟩ := SwapRepair.exists_table hm env
  refine ⟨⟨I,J,hi,hj,(R.submatrix I J)⁻¹,?_,env,T,hT⟩⟩
  unfold nodeRectangles
  rw [rectangleMatrix_hammingRectangle]
  exact hf

noncomputable abbrev program (K : StageKernel p k m) := PackedPencil.program (nodeRectangles p k)
  K.source K.target K.matrix K.env

/-- Four complete predictors followed by the forward and backward passes on
the two sets of check rows. -/
noncomputable def calls (K : StageKernel p k m)
    (A : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)) : ℕ :=
  (4*SwapRepair.order m) *
    (Fintype.card (PackedPencil.Index m) * StageScript.cost (fun v => (A.routeWord v).price) K.program) +
    4*m*correctedRows m*Fintype.card (HammingLabels p k)

theorem calls_le_batchCalls (K : StageKernel p k m)
    (A : RectangleAtlas (nodeRectangles p k) (hammingReserve p k)) :
    K.calls A ≤ batchCalls p k m 108 := by
  let T := 4*SwapRepair.order m
  let M₀ := PackedPencil.mixer K.env.pencil.A₀
  let Mj := fun j => PackedPencil.mixer (fun β => K.env.pencil.A β j 1)
  have h := hamming_cost_le_batchCalls p k m A K.source K.target K.matrix
    (fun _ : Fin T => M₀) (fun _ : Fin T => Mj)
  have hcard : Fintype.card (PackedPencil.Index m) = independentRows m := by
    simp only [PackedPencil.Index,independentRows,componentWidth,Fintype.card_prod,Fintype.card_fin]
  simpa only [calls,hcard,program,PackedPencil.program,T,M₀,Mj,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

end StageKernel

open Filter IntegerMultiplication.Port

/-- The actual packed pencil, its finite spectral repair, and all native
rectangle moves share one choice of rates and layout. The final inequality
charges the physical padded volume per radix digit and both reserves. -/
theorem exists_configured_batch {α γ : ℝ} (hγ : 1/2 < γ) (ha : γ < α) :
    ∃ p : ℕ, ∃ hp : Fact p.Prime, 2 < p ∧ ∀ᶠ m : ℕ in atTop, ∃ k : ℕ,
      letI := hp
      let a := hammingReserve p k
      let W := independentRows m * Fintype.card (HammingLabels p k)
      ∃ (K : StageKernel p k m) (atlas : RectangleAtlas (nodeRectangles p k) a),
        ∀ (threshold : ℕ) (extra : Finset ℚ), ∃ b : ℕ, b.Prime ∧ max threshold W < b ∧
        ∃ code : ℚ → Pinpoint b,
          (∀ x ∈ extra, (code x = none ↔ x = 0) ∧ ∀ f, Token x ((code x).stamp f)) ∧
          Nonempty (RectangleAtlas.Frame atlas m b) ∧
          let charged := (K.calls atlas * BatchRows.groups b W : ℕ)
          (charged : ℝ)/b < 2*(m:ℝ)^γ ∧ (charged : ℝ)/b + 2*a < (m:ℝ)^α := by
  obtain ⟨p,hp,hodd,h⟩ := exists_contracted_frame hγ ha
  let := hp
  refine ⟨p,hp,hodd,?_⟩
  filter_upwards [h,eventually_ge_atTop (2:ℕ)] with m hm hm2
  obtain ⟨k,atlas,hr⟩ := hm
  obtain ⟨K⟩ := StageKernel.exists_kernel p k m hodd hm2
  refine ⟨k,K,atlas,fun threshold extra => ?_⟩
  obtain ⟨b,hprime,hw,code,hx,hf,ht,hs⟩ := hr threshold extra
  refine ⟨b,hprime,hw,code,hx,hf,?_,?_⟩
  · apply lt_of_le_of_lt _ ht
    gcongr
    exact K.calls_le_batchCalls atlas
  · apply lt_of_le_of_lt _ hs
    gcongr
    exact K.calls_le_batchCalls atlas

end Interchange

end NearSquareRoot
end Computability
end OAI
