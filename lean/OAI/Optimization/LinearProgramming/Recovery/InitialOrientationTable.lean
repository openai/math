import OAI.Optimization.LinearProgramming.Recovery.BundleSelect
import OAI.Optimization.LinearProgramming.Recovery.InitialPairShared
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderPublish
import OAI.Optimization.LinearProgramming.Recovery.PrincipalMath

/-! Identify the rows retained by the first marked LP subspace call. Both
branches refer to the actual adjacent matrices exported by the pair builder. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialOrientation

open Matrix RAM RAM.Callable Geometry Polynomial
open scoped Matrix

variable {m d k s n : ℕ}

def selected {K : Type*} (b : Bool) (F : Matrix (Fin k) (Fin n) K) (R : Matrix (Fin s) (Fin n) K) :
    Matrix (Fin (SupportBundle.selectedHeight b k s)) (Fin n) K :=
  match b with
  | false => F
  | true => R

theorem selected_table {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K}
    {F : Matrix (Fin k) (Fin (m+1)) K} {R : Matrix (Fin s) (Fin (m+1)) K} {t : Memory K}
    (ready : PairBuilder.Prepared false (InitialPair.layout m d) (slackColumns A b)ᵀ F R t) (side : Bool) :
    uniformRect (SupportBundle.selectedHeight side k s) (m+1)
      (SupportBundle.selectedBase side (InitialPair.layout m d).out k (m+1)) t=selected side F R := by
  cases side
  · exact ready.firstTable
  · exact ready.lastTable

theorem selected_kernel {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K}
    {F : Matrix (Fin k) (Fin (m+1)) K} {R : Matrix (Fin s) (Fin (m+1)) K} {t : Memory K}
    (ready : PairBuilder.Prepared false (InitialPair.layout m d) (slackColumns A b)ᵀ F R t) (side : Bool) :
    LinearMap.ker (selected side F R).mulVecLin=(Principal.side A b side).denote := by
  obtain ⟨primal,dual⟩ := Principal.opposite_spaces A b F R ready.firstSpan ready.kernelSpan
  cases side
  · exact dual
  · exact primal

theorem selected_height (side : Bool) (total : s+k=n) : SupportBundle.selectedHeight side k s ≤ n := by
  cases side
  · change k ≤ n;omega
  · change s ≤ n;omega

theorem selected_source (m d k : ℕ) (side : Bool) :
    let base := SupportBundle.selectedBase side (InitialPair.layout m d).out k (m+1)
    256 ≤ base ∧ PublicInput.sourceBase m d + (m*d+m) ≤ base := by
  intro base
  have start : PublicInput.sourceBase m d + (m*d+m) ≤ (InitialPair.layout m d).out := by
    change PublicInput.sourceBase m d + (m*d+m) ≤
      (PublicInput.sourceBase m d + (m*d+m) + (m+1)*(d+1)) + (d+1)*(m+1)
    omega
  have low : 256 ≤ PublicInput.sourceBase m d := Nat.le_add_right ..
  have room : (InitialPair.layout m d).out ≤ base := by
    cases side <;> simp [base,SupportBundle.selectedBase]
  exact ⟨by omega,start.trans room⟩

theorem table_width {h n src H : ℕ} {M : Matrix (Fin h) (Fin n) ℚ} {t : Memory ℚ}
    (read : uniformRect h n src t=M) (safe : t.AllData (fun q => ratBits q ≤ H)) :
    ∀ i j,ratBits (M i j) ≤ H := by
  intro i j
  rw [←read]
  exact safe _

theorem original_data {K : Type} {u v : Memory K}
    {A : Matrix (Fin m) (Fin d) K} {b : Fin m → K} {src : ℕ} (same : v.data=u.data)
    (old : SlackRAM.InputAt u src A b) : SlackRAM.InputAt v src A b :=
  ⟨fun i j => (congrFun same _).trans (old.1 i j),fun i => (congrFun same _).trans (old.2 i)⟩

end InitialOrientation
end Recovery
end LinearProgramming
end Optimization
end OAI
