import OAI.Computability.NearSquareRoot.CRTControlledReservePrepare

/-! # Addressing the four-stage descriptor list on a shared header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Controlled.Reflections (Table table)

def atStage {k lo hi : ℕ} (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2)
    (j : Fin 4) : ReserveStage k lo hi :=
  (ReserveStage.four p cap)[j.val]'(by simp)

theorem atStage_mem {k lo hi : ℕ} (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2)
    (j : Fin 4) : atStage p cap j ∈ ReserveStage.four p cap := List.getElem_mem ..

theorem stages_eq {k lo hi : ℕ} (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2) :
    List.ofFn (atStage p cap) = ReserveStage.four p cap := by
  apply List.ext_getElem
  · simp
  · intro i h h'
    simp only [List.getElem_ofFn, atStage]

theorem atStage_uniform {I : Type} {r : Regime I} {k lo hi : I → ℕ}
    (p : ∀ i, Equiv.Perm (Fin (k i))) (cap : ∀ i, lo i+hi i ≤ k i/2-2)
    (prepared : r.Has (fun i => (ReserveStage.four (p i) (cap i)).map encode)) (j : Fin 4) :
    r.Has (fun i => encode (atStage (p i) (cap i) j)) := by
  have look := (prepared.pair (Regime.fixed (tally j.val))).ez (Iter.facile (([],[]) : Descriptor))
  have eq (i : I) :=
    Iter.search ((ReserveStage.four (p i) (cap i)).map encode) (([],[]) : Descriptor) j.val
      (by simp)
  simpa only [eq, List.getElem_map, atStage] using look

theorem table_uniform {I : Type} {r : Regime I} (a b : ℕ) {k : I → ℕ}
    (p : ∀ i, Equiv.Perm (Fin (k i)))
    (cap : ∀ i, payloadBits a (k i) + payloadBits b (k i) ≤ k i/2-2)
    (tab : r.Has (fun i => table (p i))) :
    r.Has (fun i => (ReserveStage.four (p i) (cap i)).map encode) := by
  simpa only [fun i => fromTable_value a b (p i) (cap i)] using tab.thenDo (fromTable_poly a b)

end Controlled.ReserveProgram

end NearSquareRoot
end Computability
end OAI
