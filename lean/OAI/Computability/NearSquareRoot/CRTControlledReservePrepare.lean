import OAI.Computability.NearSquareRoot.CRTControlledReserveCompiler
import OAI.Computability.NearSquareRoot.CRTControlledElementaryRun
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Preparing the logarithmic reserve descriptors beside a full record array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Staff
open IntegerMultiplication.Strip IntegerMultiplication.Carry NearSquareRoot.Space
open NearSquareRoot.Controlled.Reflections (Table table)

/-- Both widths are generated from the length of the supplied image table. -/
def fromTable (a b : ℕ) (t : Table) : List Descriptor :=
  compiler (tally (payloadBits a t.length),tally (payloadBits b t.length),t)

theorem fromTable_poly (a b : ℕ) : Poly (fromTable a b) := by
  let r : Regime Table := ⟨size,send,Dom.base _⟩
  have tab : r.Has (id : Table → Table) := Poly.identity
  have n : Realizes r List.length := by
    change Poly (fun t : Table => tally t.length)
    have eq : (fun t : Table => tally t.length) = ruler := by
      funext t
      rw [← ruler_length t,recover_tally]
    rw [eq]
    exact (Easy.ruler (Easy.identity (X := Table))).poly
  have width : Realizes r (fun t : Table => Nat.clog 2 (t.length+1)) :=
    (Figure.of_spoken (n.plus (Realizes.fix 1))).short_log
  exact (((Realizes.fix a).times width).pair (((Realizes.fix b).times width).pair tab)).thenDo compiler_poly

theorem fromTable_value (a b : ℕ) {k : ℕ} (p : Equiv.Perm (Fin k))
    (cap : payloadBits a k + payloadBits b k ≤ k/2-2) :
    fromTable a b (table p) = (ReserveStage.four p cap).map encode := by
  rw [fromTable,show (table p).length = k by simp [table]]
  exact compiler_value p cap

/-- Computing the descriptors alongside the untouched payload costs linear
time and space in the record volume, including the complete position table. -/
theorem prepare {I : Type} (a b : ℕ) (k V : I → ℕ) (p : ∀ i, Equiv.Perm (Fin (k i)))
    (cap : ∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2)
    (hV : ∀ i, 2^(k i) ≤ V i) (data : I → Tree) (hdata : ∀ i, (data i).count ≤ V i) :
    BoundedTask V V (fun i => .fork (send (table (p i))) (data i))
      (fun i => .fork (send ((ReserveStage.four (p i) (cap i)).map encode)) (data i)) := by
  let r : Regime I := ⟨k,fun i => send (table (p i)),2,2,fun i => Reflections.table_size (p i)⟩
  have ready : r.Has (fun i => (ReserveStage.four (p i) (cap i)).map encode) := by
    have tab : r.Has (fun i => table (p i)) := r.self
    simpa only [fun i => fromTable_value a b (p i) (cap i)] using tab.thenDo (fromTable_poly a b)
  have charge {t : I → ℕ} (h : Dom k t) : ∃ A : ℕ, ∀ i, t i ≤ A*V i := by
    obtain ⟨d,C,ht⟩ := h
    obtain ⟨E,he⟩ := polynomial_le_multiple_array_length d
    refine ⟨C*E,fun i => ?_⟩
    rw [Nat.mul_assoc]
    exact (ht i).trans (Nat.mul_le_mul_left _ ((he (k i)).trans (Nat.mul_le_mul_left _ (hV i))))
  obtain ⟨t,ht,prog⟩ := ready
  obtain ⟨A,htime⟩ := charge ht
  obtain ⟨B,hsize⟩ := charge r.gauge
  have hpos (i : I) : 1 ≤ V i := (Nat.two_pow_pos _).trans_le (hV i)
  have hh : Carries (fun i => (V i : ℝ)) r.header
      (fun i => send ((ReserveStage.four (p i) (cap i)).map encode)) := by
    refine ⟨(Sized.natural prog).adapts (fun i => by exact_mod_cast hpos i) (A+1) ?_, B, ?_⟩
    · intro i
      have hh := htime i
      have hp := hpos i
      exact_mod_cast (by rw [Nat.succ_mul]; omega : t i + 1 ≤ (A+1)*V i)
    · intro i
      change ((r.header i).count : ℝ) ≤ (B : ℝ) * (V i : ℝ)
      exact_mod_cast hsize i
  have saved : Volume (fun i => (V i : ℝ)) data :=
    ⟨1,fun i => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr (hdata i)⟩
  exact boundedOfCarries (hh.first saved)

end Controlled.ReserveProgram

end NearSquareRoot
end Computability
end OAI
