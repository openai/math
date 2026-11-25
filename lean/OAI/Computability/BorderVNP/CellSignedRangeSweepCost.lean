import OAI.Computability.BorderVNP.CellPrivateTranslate
import OAI.Computability.BorderVNP.CellLocalSweepStatic

/-! # Physical clocks for the signed and range passes on the isolated directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

set_option maxHeartbeats 1800000
set_option maxRecDepth 30000

private theorem prepared_sweep_width {ps : Directory → Local.Params} (mode : Local.Pass)
    (hp : Procedure Typed.directory Local.paramsCode ps)
    (measured : Procedure.Measured blockSpan 30 (hp.pair (Procedure.identity Typed.directory)) id)
    (hw : ∀ (D : Directory) {p U : ℕ}, RawFields D p U → Local.ParamsWidth (ps D) (U.size+1))
    (A T B j : ℕ) :
    ∃ C k : ℕ, 0 < C ∧ 0 < k ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      (Local.sweepStmt mode (Procedure.identity Typed.directory) hp).meter D ≤ C*(M+1)^62*L^k := by
  obtain ⟨P,hP,prep⟩ := meter_width_of_blockSpan measured A B j
  obtain ⟨S,k,hS,hk,sweep⟩ := Local.sweepPrinter_meter_static_width mode A T B j
  refine ⟨6*(P+S),max (j*30) k,by positivity,lt_max_of_lt_right hk,?_⟩
  intro D p M U L hL hs hstore hraw hu ht
  have hp' := prep D p M U L hL hs hstore hraw hu
  have hd := hw D hraw
  have hw' : Local.ParamsWidth (ps D) (B*L^j) :=
    ⟨hd.1.trans hu,hd.2.1.trans hu,hd.2.2.trans hu⟩
  have hs' := sweep (ps D) D p M U L hL hs hstore hraw hu hw' ht
  let t := (M+1)^62*L^(max (j*30) k)
  have h₁ : (hp.pair (Procedure.identity Typed.directory)).meter D ≤ P*t := by
    calc _ ≤ P*(M+1)^(2*30)*L^(j*30) := hp'
      _ ≤ P*(M+1)^62*L^(max (j*30) k) := Nat.mul_le_mul
        (Nat.mul_le_mul_left P (Nat.pow_le_pow_right (by omega) (by decide)))
        (Nat.pow_le_pow_right hL (le_max_left ..))
      _ = P*t := Nat.mul_assoc ..
  have h₂ : (Local.sweepPrinter mode).meter (ps D,D) ≤ S*t := by
    calc _ ≤ S*(M+1)^62*L^k := hs'
      _ ≤ S*(M+1)^62*L^(max (j*30) k) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (le_max_right ..))
      _ = S*t := Nat.mul_assoc ..
  have hcomp := Procedure.meter_comp (Local.sweepPrinter mode) (hp.pair (Procedure.identity Typed.directory)) D
  change (Local.sweepStmt mode (Procedure.identity Typed.directory) hp).meter D ≤
    6*((hp.pair (Procedure.identity Typed.directory)).meter D+(Local.sweepPrinter mode).meter (ps D,D)) at hcomp
  exact hcomp.trans (by
    calc 6*((hp.pair (Procedure.identity Typed.directory)).meter D+(Local.sweepPrinter mode).meter (ps D,D))
        ≤ 6*(P*t+S*t) := Nat.mul_le_mul_left _ (Nat.add_le_add h₁ h₂)
      _ = _ := by dsimp only [t]; ring)

/-- The real signed-factor pass prepares the zero parameter tuple, retains the typed
directory, and prints every original signed factor with a uniform physical clock. -/
theorem factorSweep_meter_width (A T B j : ℕ) :
    ∃ C k : ℕ, 0 < C ∧ 0 < k ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      factorSweep.meter D ≤ C*(M+1)^62*L^k := by
  unfold factorSweep
  apply prepared_sweep_width
  · exact Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=1) (by simp [blockSpan])
  · intro D p U _
    change Nat.size 0+1 ≤ U.size+1 ∧ Nat.size 0+1 ≤ U.size+1 ∧ Nat.size 0+1 ≤ U.size+1
    simp

/-- The real range pass computes the length of the reported-count list in binary
before printing the identifier checks. Its scalar arguments obey the same clock
regardless of the numerical magnitudes of the global identifiers. -/
theorem rangeSweep_meter_width (A T B j : ℕ) :
    ∃ C k : ℕ, 0 < C ∧ 0 < k ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      (∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) →
      rangeSweep.meter D ≤ C*(M+1)^62*L^k := by
  unfold rangeSweep
  apply prepared_sweep_width
  · exact Procedure.Measured.of_degree _ _ (by decide) _ _ (by cqf_degree) (H:=1) (by simp [blockSpan])
  · intro D p U h
    change D.reportedCounts.length.size+1 ≤ U.size+1 ∧ Nat.size 0+1 ≤ U.size+1 ∧ Nat.size 0+1 ≤ U.size+1
    simpa using Nat.size_le_size h.lengths.2.2

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
