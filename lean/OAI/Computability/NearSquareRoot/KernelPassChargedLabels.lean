import OAI.Computability.NearSquareRoot.KernelPassCharged
import OAI.Computability.NearSquareRoot.KernelPassChargedFrame
import OAI.Computability.NearSquareRoot.KernelPassChargedChart
import OAI.Computability.NearSquareRoot.KernelPassRectPencil
import OAI.Computability.NearSquareRoot.KernelPassRational

/-! # Charged source, common, and destination plans for the rectangle system

One middle plan works for every label, query, and rectangle of a fixed
geometry. All label-dependent parts are free. After tensoring the columns,
the charged rectangle has exactly the same transfer as the endpoint
factorization of a free rectangle.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Charged

open OAI.LinearAlgebra.FiniteFourier BinaryQuery KernelNormalization Matrix

noncomputable section
variable {L b m : ℕ} (G : BitRoutingGeometry 2 L b)

abbrev Axes := Arity (m+1) (G.D-1)
abbrev Spectator := EndpointDigitPairs (Fin 1) (Fin m) F

def chart (j : Fin (m+1)) (v : BitLabel L b) :
    Bits (Axes (m := m) G) ≃ₗ[F] Common G.Space (Spectator (m := m)) :=
  physicalLinear j (G.labelCharts v).first (G.labelCharts v).second

/-- The physical chart and the archive's chart differ only by the same
numbering of spectator coordinates at every label. -/
theorem transfer_eq (j : Fin (m+1)) (w v : BitLabel L b) :
    transfer G.form G.D (chart G j w) (chart G j v) =
      (G.transfer binaryRoot 1 1 j w v).submatrix
        (halves (m+1) (G.D-1)) (halves (m+1) (G.D-1)) := by
  let s := primeCommonUniformSpectators (C := Fin 1) (ℓ := 2) j
  let r := (Equiv.refl ((Fin 1 → G.Space) × (Fin 1 → G.Space))).prodCongr s
  have same (v : BitLabel L b) : (chart G j v).toEquiv =
      (halves (m+1) (G.D-1)).trans ((G.queryChart 1 j v).trans r) :=
    congrArg ((halves (m+1) (G.D-1)).trans ·)
      (primeCommonQueryChart_uniform (C := Fin 1) j (G.labelCharts v).first (G.labelCharts v).second).symm
  have invariant := primeCommonKernel_reindex_spectator (C := Fin 1) binaryRoot G.form 1 G.D s
  ext y x
  change (primeCommonKernel (C := Fin 1) binaryRoot G.form 1 G.D)
    ((chart G j w).toEquiv y) ((chart G j v).toEquiv x) = _
  rw [same, same]
  exact congrFun (congrFun invariant (G.queryChart 1 j w (halves _ _ y)))
    (G.queryChart 1 j v (halves _ _ x))

/-- The charged diagonal block is the actual quadratic Fourier query. -/
theorem transfer_self (j : Fin (m+1)) (v : BitLabel L b) :
    transfer G.form G.D (chart G j v) (chart G j v) = query (u := G.D-1) j := by
  have hd : G.D-1+1 = G.D := by have := G.dim_pos; omega
  have eq := physical_query j G.form (G.labelCharts v).first (G.labelCharts v).second
    (G.labelCharts v).pair
  rw [hd] at eq
  exact eq.symm

/-- Physical plans for a single charged middle and its zero-call chart changes.
Block semantics use the same single-column transfer at every address width. -/
structure Plans (m : ℕ) (G : BitRoutingGeometry 2 L b) where
  collect : Fin (m+1) → BitLabel L b → Plan (Axes (m := m) G) 1 1
  scatter : Fin (m+1) → BitLabel L b → Plan (Axes (m := m) G) 1 1
  middle : Plan (Axes (m := m) G) 1 1
  collect_calls j v : (collect j v).calls = 0
  scatter_calls j v : (scatter j v).calls = 0
  middle_calls : middle.calls ≤ 2*G.D
  block j w v : Implements (((scatter j w).seq middle).seq (collect j v))
    ((G.transfer binaryRoot 1 1 j w v).submatrix (halves (m+1) (G.D-1)) (halves (m+1) (G.D-1)))

/-- Compile the charged steps using one shared reference frame for every query. -/
def plans (m : ℕ) : Plans m G := by
  let base : BitLabel L b := fun _ _ => false
  let ref := chart G (m := m) 0 base
  have mid := realizes_transfer G.form (labelFrame G base false) (labelFrame G base true)
    (labelFrame_pair G base) ref ref
  let hS (j : Fin (m+1)) (v : BitLabel L b) := realizes_source ref (chart G j v)
  let hT (j : Fin (m+1)) (v : BitLabel L b) := realizes_target ref (chart G j v)
  refine ⟨fun j v => (hS j v).choose, fun j v => (hT j v).choose, mid.choose,
    fun j v => Nat.eq_zero_of_le_zero (hS j v).choose_spec.1,
    fun j v => Nat.eq_zero_of_le_zero (hT j v).choose_spec.1,mid.choose_spec.1,?_⟩
  intro j w v
  have compiled := ((hT j w).choose_spec.2.seq mid.choose_spec.2).seq (hS j v).choose_spec.2
  have e := (factor G.form G.D ref (chart G j w) (chart G j v)).trans (transfer_eq G j w v)
  exact (congrArg (Implements (((hT j w).choose.seq mid.choose).seq (hS j v).choose)) e).mp compiled

/-- Tensor-width semantics for a raw rectangle entry, after casting the three
rational singleton blocks to complex coefficients. -/
theorem Plans.entry (P : Plans m G) (h : ℕ) (j : Fin (m+1)) (w v : BitLabel L b) :
    ((oneRow ((P.scatter j w).eval h)) * oneRow (P.middle.eval h) *
      oneRow ((P.collect j v).eval h)).map (algebraMap ℚ ℂ) =
    lift h ((G.transfer binaryRoot 1 1 j w v).submatrix
      (halves (m+1) (G.D-1)) (halves (m+1) (G.D-1))) := by
  simpa only [Plan.eval,oneRow_mul] using P.block j w v h

/-- The archive transfer in numbered binary coordinates, tensorized at width h. -/
def routed (m : ℕ) : Rect.Kernels (Axes (m := m) G) (Fin (m+1)) (BitLabel L b) :=
  fun h j w v => rationalLift h ((G.transfer binaryRoot 1 1 j w v).submatrix
    (halves (m+1) (G.D-1)) (halves (m+1) (G.D-1)))

/-- On a surviving diagonal label the routed block is the specified
ordinary query at every tensor width. -/
theorem routed_self (m h : ℕ) (j : Fin (m+1)) (v : BitLabel L b) :
    routed G m h j v v = rationalLift h (query (u := G.D-1) j) :=
  congrArg (rationalLift h) ((transfer_eq G j v v).symm.trans (transfer_self G j v))

/-- Supply any charged support and its signed dyadic weight to the compiled plans. -/
def rectangleData (m : ℕ) (s : Rect.Support (BitLabel L b)) :
    Rect.ChargedData (Axes (m := m) G) (BitLabel L b) (Fin (m+1)) where
  toSupport := s
  input := (plans G m).collect
  output := (plans G m).scatter
  common := fun _ => (plans G m).middle
  input_free := (plans G m).collect_calls
  output_free := (plans G m).scatter_calls

theorem rectangleData_factors (m : ℕ) (s : Rect.Support (BitLabel L b)) :
    (rectangleData G m s).Factors (routed G m) := by
  intro h j w v _ _
  simpa only [rectangleData, Plan.eval, oneRow_mul, routed] using
    ((plans G m).block j w v).oneRow_eq h

theorem rectangleData_calls (m : ℕ) (s : Rect.Support (BitLabel L b)) (j : Fin (m+1)) :
    ((rectangleData G m s).common j).calls ≤ 2*G.D := (plans G m).middle_calls

end
end KernelPass.Charged

end NearSquareRoot
end Computability
end OAI
