import OAI.Optimization.LinearProgramming.Compression.NativeCache
import OAI.Optimization.LinearProgramming.Compression.NativeProxyCost
import OAI.Optimization.LinearProgramming.Compression.CommitOracle
import OAI.Optimization.LinearProgramming.Lattice.LLLWire

/-! Coordinates, admissible coefficient budget, exact trichotomy, and the returned integer
row for the numerical service. These definitions also serve the host RAM adapter. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice SignType
open scoped BigOperators

def permitted {p : ℕ} (N : ℕ) (a : Fin p → ℤ) : Prop :=
  (2:ℤ)^(paperRadius N+7)*(∑ i, |a i|) ≤ (2:ℤ)^manuscriptProxyFuel N

def goodWord (N p : ℕ) (w : Word) : Prop := ∃ a : Fin p → ℤ, w=signRowWord a ∧ permitted N a

def goodHistory (N p : ℕ) (h : Transcript) : Prop := ∀ e∈h, goodWord N p e.1

/-- The LLL sign query is the same affine strict-negative decision used by the graph. -/
theorem signTest_eq {d : ℕ} (fuel p : ℕ) (mag : Fin d → ℚ) :
    (fun a => decide (0 ≤ generatorSign fuel p mag a)) = affineCommitReply (requestMagnitudeNegative fuel p mag) := by
  funext a
  unfold generatorSign affineCommitReply requestMagnitudeNegative
  cases logProxySign fuel p (a (Fin.last d)) (fun i => a i.castSucc) mag <;> decide

theorem cached_sign_order {d : ℕ} (fuel p : ℕ) (mag : Fin d → ℚ) (a : Fin (d+1) → ℤ) :
    orderOfSign (generatorSign fuel p mag a) = logProxySign fuel p (a (Fin.last d)) (fun i => a i.castSucc) mag := by
  unfold generatorSign
  cases logProxySign fuel p (a (Fin.last d)) (fun i => a i.castSucc) mag <;> rfl

theorem cached_sign_pad {g : ℕ} (fuel p : ℕ) (mag : Fin (g+1) → ℚ) (hm : ∀ i, 0<mag i)
    (a : Fin (g+1) → ℤ) : generatorSign fuel p mag (padEpochQuery a) =
      generatorSign fuel p (fun i => mag i.castSucc) a := by
  rw [generatorSign_correct fuel p mag hm,generatorSign_correct fuel p _ (fun i => hm i.castSucc)]
  simp only [dotProduct,realCoordinates,Fin.sum_univ_castSucc,padEpochQuery,Fin.snoc_castSucc,Fin.snoc_last,
    Int.cast_zero,zero_mul,add_zero,generatorProxy]

def roundZ {d : ℕ} (N M : ℕ) (mag : Fin d → ℚ) : Fin (d+1) → ℤ :=
  SignQueries.run (affineCommitReply (requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) mag))
    (lllRoundingProgram (d+1) M)

def «matches» {g : ℕ} (N : ℕ) (mag : Fin (g+1) → ℚ) (o : WordOracle) : Prop :=
  ∀ h (a : Fin ((g+1)+1) → ℤ), permitted N a → o h (signRowWord a) =
    signReply (logProxySign (manuscriptProxyFuel N) (paperRadius N+7) (a (Fin.last (g+1)))
      (fun i => a i.castSucc) mag)

def position (g : ℕ) (member : Bool) (rank : ℕ) : Option (Fin g) :=
  if h : member=true ∧ rank<g then some ⟨rank,h.2⟩ else none

theorem position_of_coherent {g : ℕ} (pos : Option (Fin g)) (rank : ℕ)
    (coherent : ∀ i,pos=some i → i.val=rank) :
    position g pos.isSome rank=pos ∧ (pos.isSome=true → rank<g) := by
  cases pos with
  | none => simp [position]
  | some i =>
    have h := coherent i rfl
    subst rank
    simp [position,i.isLt]

def epochRadius (N g : ℕ) := epochFormBudget g (paperWidth N) (epochHeightFor N g)
def requestRadius (g : ℕ) := (g+3)*(requestCutoff (g+1)+3)

theorem sharedGamma_eq {g : ℕ} (N : ℕ) (mag : Fin (g+1) → ℚ) (hm : ∀ i,0<mag i) :
    sharedEpochCommit N g (requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) mag) =
      normalizeCommit (roundZ N (epochRadius N g) (fun i => mag i.castSucc)) := by
  unfold sharedEpochCommit
  have e : (fun a c => requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) mag (Fin.snoc a 0) c) =
      requestMagnitudeNegative (manuscriptProxyFuel N) (paperRadius N+7) (fun i => mag i.castSucc) := by
    funext a c; exact requestMagnitudeNegative_pad_epoch _ _ _ hm a c
  rw [e]; rfl

theorem normalizedRequest_eq {g : ℕ} (N : ℕ) (mag : Fin (g+1) → ℚ) :
    normalizeCommit (roundZ N (requestRadius g) mag)=nativeRequestRounded (manuscriptProxyFuel N) (paperRadius N+7) mag := rfl

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
