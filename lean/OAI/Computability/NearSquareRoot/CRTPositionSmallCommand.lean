import OAI.Computability.NearSquareRoot.CRTControlledReserveCutoff
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # One named position-routing fallback for every cutoff -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open NearSquareRoot.Space CommonRegisters GeneratorSyntax EffectiveBoundedTask Filter

noncomputable section

/-- The universal input family includes all widths and encoded record arrays. -/
private structure SmallCase where
  k : ℕ
  V : ℕ
  p : Equiv.Perm (Fin k)
  data : Block 2 k → Tree
  fits : (stripe (line 2 k) data).count ≤ V

private def SmallCase.input (x : SmallCase) :=
  Tree.fork (send (Reflections.table x.p)) (stripe (line 2 x.k) x.data)

private def SmallCase.output (x : SmallCase) :=
  stripe (line 2 x.k) (x.data ∘ flatBitPullback x.p)

private theorem smallTask :
    BoundedTask (fun x : SmallCase => (2*x.k+2)*x.V) SmallCase.V SmallCase.input SmallCase.output := by
  let r : Regime SmallCase := ⟨SmallCase.k, fun x => send (Reflections.table x.p), 2, 2,
    fun x => Reflections.table_size x.p⟩
  exact ReserveSmall.boundedRunAllWidths (r := r) SmallCase.k SmallCase.V SmallCase.p
    SmallCase.data SmallCase.fits (fun _ => le_rfl) r.self

/-- The fallback reads the original table. Its syntax is independent of every cutoff. -/
def smallCmd : Cmd := smallTask.choose

theorem small_runs_all {I : Type} (k V : I → ℕ) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → Tree) (fits : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    Runs smallCmd (fun i => (2*k i+2)*V i) V
      (fun i => .fork (send (Reflections.table (p i))) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) :=
  (show Runs smallCmd (fun x : SmallCase => (2*x.k+2)*x.V) SmallCase.V SmallCase.input SmallCase.output
    from smallTask.choose_spec).on (fun i => ⟨k i,V i,p i,f i,fits i⟩)

/-- Restrict the clock of the same fallback to widths at most `K`. -/
theorem small_runs {I : Type} (K : ℕ) (k V : I → ℕ) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (width : ∀ i, k i ≤ K) (f : (i : I) → Block 2 (k i) → Tree)
    (fits : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i) :
    Runs smallCmd V V
      (fun i => .fork (send (Reflections.table (p i))) (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ flatBitPullback (p i))) := by
  apply (small_runs_all k V p f fits).bound (2*K+2) 1
  · intro i
    have c := Nat.mul_le_mul_right (V i) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (width i)) 2)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · simp

/-- A cloth of bead records uses the same fallback, including empty payload strips. -/
theorem small_cloth_runs {I : Type} {U : I → Type} (K : ℕ) (k w : I → ℕ) (u : (i : I) → Series (U i))
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Loom.Bead)
    (width : ∀ i, k i ≤ K) (pos : ∀ i, 0 < w i) (payload : ∀ i, (u i).count ≤ w i) :
    Runs smallCmd (fun i => 2^(k i)*w i) (fun i => 2^(k i)*w i)
      (fun i => .fork (send (Reflections.table (p i))) (Loom.cloth (fun i => line 2 (k i)) u f i))
      (Loom.cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  have task := small_runs K k (fun i => 5*(2^(k i)*w i)) p width (fun i z => Loom.strip (u i) (f i z))
    (ReserveSmall.beadClothCap k w u f pos payload)
  exact task.bound 5 5 (fun i => by rw [Nat.mul_add]; omega) (fun i => by rw [Nat.mul_add]; omega)

theorem small_within : ∀ᶠ R in atTop, Within R smallCmd := RegisterSelect.within_eventually _

theorem small_effective_const {J : Type} [Primcodable J] : Effective ltr (fun _ : J => smallCmd) :=
  effective_const _ _

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
