import OAI.Computability.NearSquareRoot.InterchangeROMStageTape
import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger

/-! # The recursive request list of a literal Hamming stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  IntegerMultiplication.Strip Space InterchangeSpace InterchangeROMSequence

variable {g : Frame} (r : Realization g) (d : ℕ) {Q : Type}

/-- Every scalar output of every route has its own expanded word and request list. -/
abbrev Field (k : Fin 6) := r.Boundary (routePos k+1) × Fin d

noncomputable def ledger (qs : (k : Fin 6) → r.Field d k → List Q) : List Q :=
  (List.finRange 6).flatMap fun k => (r.cells (routePos k+1) d).flatMap (qs k)

theorem mem_ledger {qs : (k : Fin 6) → r.Field d k → List Q} {q : Q} :
    q ∈ r.ledger d qs ↔ ∃ k z, q ∈ qs k z := by
  constructor
  · intro h
    obtain ⟨k,_,hw⟩ := List.mem_flatMap.mp h
    obtain ⟨z,_,hz⟩ := List.mem_flatMap.mp hw
    exact ⟨k,z,hz⟩
  · rintro ⟨k,z,hz⟩
    exact List.mem_flatMap.mpr ⟨k,List.mem_finRange _,List.mem_flatMap.mpr
      ⟨z,List.mem_flatMap.mpr ⟨z.1,(r.order _).complete _,List.mem_map.mpr
        ⟨z.2,List.mem_finRange _,rfl⟩⟩,hz⟩⟩

private theorem bill {A : Type} (l : List A) (q : A → List Q) (f : Q → ℕ) (M : ℕ) :
    costSum (fun a => M+costSum f (q a)) l = l.length*M+costSum f (l.flatMap q) := by
  induction l with
  | nil => simp [costSum]
  | cons a l ih =>
    simp only [costSum_cons,List.flatMap_cons,List.length_cons,Nat.succ_mul,ih]
    simp [costSum,List.sum_append]
    omega

private theorem sum_flat {A : Type} (l : List A) (q : A → List Q) (f : Q → ℕ) :
    costSum f (l.flatMap q) = costSum (fun a => costSum f (q a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp [costSum,List.sum_append] at ih ⊢
    exact ih

theorem aggregate (qs : (k : Fin 6) → r.Field d k → List Q) (price : Q → ℕ) (M : ℕ) :
    (∑ k, costSum (fun z => M+costSum price (qs k z)) (r.cells (routePos k+1) d)) =
      (∑ k : Fin 6, ((bank g (routePos k+1)).length*d)*M) + costSum price (r.ledger d qs) := by
  simp only [bill,length_cells,Finset.sum_add_distrib]
  congr 1
  unfold ledger
  rw [sum_flat]
  change _ = ((List.finRange _).map _).sum
  rw [← List.ofFn_eq_map,List.sum_ofFn]

theorem ledger_length (qs : (k : Fin 6) → r.Field d k → List Q) :
    (r.ledger d qs).length = ∑ k, costSum (fun z => (qs k z).length) (r.cells (routePos k+1) d) := by
  have one (l : List Q) : costSum (fun _ => 1) l = l.length := by simp [costSum]
  have h := r.aggregate d qs (fun _ => 1) 0
  simpa only [one,Nat.zero_add,Nat.mul_zero,Finset.sum_const_zero] using h.symm

end InterchangeROMStage.Frame.Realization

end NearSquareRoot
end Computability
end OAI
