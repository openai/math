import OAI.Hierarchy.ProbeCoreCongestion
import OAI.Hierarchy.ProbeCoreWalkMount
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Count

namespace OAI
/-! # Maximum load on one installed row from the two final returns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical BigOperators
variable {S : PurchaseSampler} {h d k : ℕ}

/-- The two signed spokes of a core catalyst pair are used only by that pair. -/
private def centerOwner : Edges S h d k → Option (Columns h d × Fin k)
  | .inl (.inl (c,j,_)) => some (c,j)
  | _ => none

private theorem owner_of_step (c : Columns h d × Fin k) (e : Edges S h d k)
    (step : e∈catalystWalk c) : centerOwner e=some c := by
  rcases c with ⟨c,j⟩
  simp only [catalystWalk,List.mem_cons,List.not_mem_nil,or_false] at step
  rcases step with rfl|rfl <;> rfl

private theorem disjoint_load {I E : Type*} [Fintype I] [DecidableEq E]
    (walk : I→List E) (bits : I→ℕ) (cap : ℕ) (bound : ∀i,bits i≤cap)
    (distinct : ∀i,(walk i).Nodup) (owner : E→Option I)
    (named : ∀i e,e∈walk i→ owner e=some i) (e:E) :
    routeLoad walk bits e≤cap := by
  classical
  unfold routeLoad
  by_cases live : ∃i,e∈walk i
  · obtain ⟨i,hit⟩:=live
    rw [Finset.sum_eq_single i]
    · simpa using Nat.mul_le_mul (List.nodup_iff_count_le_one.mp (distinct i) e) (bound i)
    · intro j _ ne
      have away : e∉walk j:=fun both=>ne (Option.some.inj ((named j e both).symm.trans (named i e hit)))
      rw [List.count_eq_zero.mpr away,zero_mul]
    · simp
  · exact (Finset.sum_eq_zero (fun i _=>by
      rw [List.count_eq_zero.mpr (show e∉walk i from fun mem=>live ⟨i,mem⟩),zero_mul])).trans_le
      (Nat.zero_le cap)

theorem catalyst_load_bound (bits : Columns h d × Fin k→ℕ) (cap : ℕ) (bound : ∀c,bits c≤cap)
    (e : Edges S h d k) : routeLoad catalystWalk bits e≤cap :=
  disjoint_load catalystWalk bits cap bound (fun _=>by simp [catalystWalk,radiusEdge])
    centerOwner owner_of_step e

private theorem mapped_load_bound {I E P : Type*} [Fintype I] [DecidableEq E] [DecidableEq P]
    (row : E ↪ P) (walk : I→List E) (bits : I→ℕ) (cap : ℕ)
    (price : ∀ e,routeLoad walk bits e≤cap) (p : P) :
    routeLoad (fun i=>(walk i).map row) bits p≤cap := by
  classical
  by_cases found : ∃ e,row e=p
  · obtain ⟨e,rfl⟩:=found
    simpa [routeLoad,List.count_map_of_injective _ _ row.injective] using price e
  · calc
      _ = 0 := Finset.sum_eq_zero (fun i _=>by
        have absent : p∉(walk i).map row := by
          rintro member
          obtain ⟨e,_,eq⟩:=List.mem_map.mp member
          exact found ⟨e,eq⟩
        rw [List.count_eq_zero.mpr absent,zero_mul])
      _ ≤ cap := Nat.zero_le _

/-- Take the invoice on the actual installed private/transport ordinal. An ordinal
outside the core receives no load from either of the two return procedures. -/
theorem Mount.final_return_bound {π : Equiv.Perm (Fin (2^h))} {K edges : ℕ} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (reserved used : Columns h d × Fin k→ℕ) (limit fuel w : ℕ)
    (held : ∀i,stock i≤limit*w) (escrow : ∀c,reserved c≤fuel*w) (e : Fin edges) :
    routeLoad B.ordinary stock e+routeLoad B.centers (fun c=>reserved c-used c) e≤
      ((1+Stages h d*(2*k))*(2*Stages h d+2)*limit+fuel)*w := by
  have orig:=mapped_load_bound B.row (commodityWalk π) stock _
    (fun t=>core_load_bound π t stock _ held) e
  have sink:=mapped_load_bound B.row catalystWalk (fun c=>reserved c-used c) _
    (fun t=>catalyst_load_bound _ (fuel*w) (fun c=>(Nat.sub_le ..).trans (escrow c)) t) e
  exact (Nat.add_le_add orig sink).trans_eq (by ring)

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
