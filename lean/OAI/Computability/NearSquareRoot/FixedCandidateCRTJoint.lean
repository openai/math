import OAI.Computability.NearSquareRoot.FixedCandidateCRTLarge
import OAI.Computability.NearSquareRoot.FixedCandidateCRTEffectiveHalfStage
import OAI.Computability.NearSquareRoot.FixedCandidateJointParameters

/-! # Concrete CRT batches at the common computable acceptance threshold -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Joint

open IntegerMultiplication Code Space DigitPacking FixedPoint Controlled CRTDispatch
open CandidateParameters EffectiveBoundedTask

noncomputable section

abbrev N (degree : ℕ) (p : Guess) (i : LargeInput (inputCut degree p)) := i.val.width
abbrev Job (degree : ℕ) (inv : Bool) (p : Guess) := Half.KernelIndex (N degree p) inv

theorem valid (degree : ℕ) (p : Guess) (i : LargeInput (inputCut degree p)) : Directory (N degree p i) :=
  (accepted_width i.property).1

theorem capPos (degree : ℕ) (p : Guess) (i : LargeInput (inputCut degree p)) :
    0 < Cap (addressBits (N degree p i)) := by
  let empty : Fin 0 → Fin (CRTTable.targetOrder (box i.val.width).length 0).length := Fin.elim0
  exact (accepted_native i.property (ρ := 0) le_rfl zero_le_one (slot := 0) (Q := 0)
    empty (Nat.zero_le _) (Nat.zero_le _)).capacity_pos

variable (degree : ℕ) (pos : 0 < degree) (rho : Guess → ℝ) (h₀ : ∀ p, 0 ≤ rho p) (h₁ : ∀ p, rho p ≤ 1)
variable (inv : Bool) (p : Guess)

include pos h₀ h₁ in
theorem eligible (z : Job degree inv p) :
    let k := addressBits (N degree p z.1.1)
    let s := z.1.2.1.val
    CRTBudget.NativeAdmission (selection (box (N degree p z.1.1)) s.1.val k s.2.2 z.2.1.val)
      k s.2.2 (k/16) (exterior p) k (rho p) := by
  dsimp only
  let k := addressBits (N degree p z.1.1)
  have one : (k+1)^1 ≤ (k+1)^degree := Nat.pow_le_pow_right (Nat.succ_pos _) pos
  exact accepted_native z.1.1.property (h₀ p) (h₁ p) _
    (selected_count (capPos _ _ _) _ _ _) ((Nat.le_succ k).trans (by simpa using one))

def site (z : Job degree inv p) : Site (rho p) inv :=
  let h := eligible degree pos rho h₀ h₁ inv p z
  { n := N degree p z.1.1, valid := valid degree p z.1.1, stage := z.1.2.1.val,
    generated := z.1.2.1.property, β := z.2.1
    admit := { h with payload := by simp [payloadBits] }
    values := Benes.scatter z.2.2 (pack (valid degree p z.1.1) z.1.2.1.val z.1.2.2) }

theorem siteSizeDom :
    let allSites (x : Sigma (Job degree inv)) := site degree pos rho h₀ h₁ inv x.1 x.2
    Dom (fun x => (allSites x).actual.k) (fun x => size (allSites x).actual.seed) := by
  dsimp only
  let J := (p : Guess) × LargeInput (inputCut degree p)
  let width (i : J) := N degree i.1 i.2
  let z0 (x : Sigma (Job degree inv)) : Input width inv := ⟨⟨x.1,x.2.1.1⟩,x.2.1.2⟩
  let z1 (x : Sigma (Job degree inv)) : Fin (batchN (seed inv (z0 x).2.1.val)) :=
    ⟨x.2.2.1.val,by rw [countAt (valid degree x.1 x.2.1.1)]; exact x.2.2.1.isLt⟩
  have bound := (issueSizeDom width inv).map (fun x => ⟨z0 x,z1 x⟩)
  simpa only [Site.actual_k,Site.actual_seed,z0,z1,width,site,N,Site.k] using bound

def clock (tick : Guess → ℕ → ℕ) (p : Guess) (n : ℕ) :=
  count n*(CRTBudget.batches (addressBits n)*tick p n+n+n)+n

def peak (arena : Guess → ℕ → ℕ) (p : Guess) (n : ℕ) := arena p n+n+n

set_option maxHeartbeats 1200000 in
/-- The candidate's accepted widths, including every reserve guess, use the same
real descriptor, record enumeration, and complete native stage program. -/
theorem effective (tick arena : Guess → ℕ → ℕ)
    (kernel : let f := site degree pos rho h₀ h₁ inv
      Family (fun p (z : Job degree inv p) => tick p (N degree p z.1.1))
        (fun p z => arena p (N degree p z.1.1))
        (fun p z => .fork (send (f p z).actual.seed) (CRTKernel.array Site.actual Site.u Site.f (f p z)))
        (fun p z => CRTKernel.result Site.actual Site.u Site.f (f p z))) :
    EffectiveCRTAt (inputCut degree) (peak arena) (clock tick) (fun p i => outcome (valid degree p i) inv) := by
  have raw := Half.fullSweep (N degree) (valid degree)
    (fun p i => (inputCut_ge_two _ _).trans i.property) (capPos degree) inv tick arena
  apply raw
  apply kernel.conform (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p z; rw [Site.actual_seed,Site.array_eq]; rfl
  · intro p z; rw [Site.result_eq]; rfl

end
end FixedCandidate.CRTStream.Joint

end NearSquareRoot
end Computability
end OAI
