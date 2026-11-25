import OAI.ThreeFlat.Routing.StableCompactPredicates

namespace OAI
/-! # The polynomial-size local verifier for a site of the compaction circuit -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.StableCompactSite

private def parts (F : Type*) [Zero F] [One F] {m k : ℕ} :
    (g : Gate m k) → BitNetwork F (Fintype.card (Port g))
  | .inl j => TypedWiring.localTable (fun p => if pass (k:=k) (.inl j) p then 1 else 0)
  | .inr (.inl _) => StableCompactStep.network F (width m)
  | .inr (.inr z) => TypedWiring.localTable (fun p => if pass (m:=m) (k:=k) (.inr (.inr z)) p then 1 else 0)

private def wire {m k : ℕ} (g : Gate m k) (p : Port g) : Label m k ⊕ Empty := .inl ⟨g,p⟩

def network (F : Type*) [Zero F] [One F] (m k : ℕ) : BitNetwork F (Fintype.card (Label m k)) :=
  TypedWiring.glue (parts F) wire

private theorem parts_eval {F : Type*} [CommSemiring F] {m k : ℕ} (g : Gate m k) (x : Port g → Bool) :
    TypedWiring.value (parts F g) x = if pass g x then 1 else 0 := by
  rcases g with j | (s | z)
  · exact TypedWiring.localTable_value ..
  · let a := fun j => x (.inr (0,j))
    let b := fun j => x (.inr (1,j))
    let c := fun j => x (.inr (2,j))
    have atPin : x = StableCompactStep.pin (x (.inl 0)) (x (.inl 1)) a b c := by
      funext q
      rcases q with d | ⟨d,j⟩ <;> fin_cases d <;> rfl
    refine (congrArg (TypedWiring.value (StableCompactStep.network F (width m))) atPin).trans ?_
    refine (StableCompactStep.network_eval (K:=F) (x (.inl 0)) (x (.inl 1)) a b c).trans ?_
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · exact TypedWiring.localTable_value ..

theorem network_value {F : Type*} [CommSemiring F] {m k : ℕ} (x : Label m k → Bool) :
    TypedWiring.value (network F m k) x = if ∀ g, pass g (fun j => x ⟨g,j⟩) then 1 else 0 := by
  rw [network,TypedWiring.glue_value,Fintype.sum_unique]
  simp only [wire,Sum.elim_inl,parts_eval,Fintype.prod_boole]

theorem network_cells (F : Type*) [Zero F] [One F] (m k : ℕ) :
    (network F m k).cells ≤ 5000*(k+1)*(width m+1) := by
  have bound := StableCompactStep.network_cells F (width m)
  have size : (network F m k).cells = ∑ g : Gate m k, (parts F g).cells :=
    TypedWiring.glue_cells (parts F) (wire (m:=m) (k:=k))
  rw [size]
  simp only [Fintype.sum_sum_type,parts,TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells,Port,Fintype.card_fin,Finset.sum_const,Finset.card_univ,
    Fintype.card_unit,nsmul_eq_mul]
  nlinarith [Nat.mul_le_mul_left k bound, Nat.zero_le (k*width m)]

theorem network_internal (F : Type*) [Zero F] [One F] (m k : ℕ) :
    (network F m k).internal ≤ 5000*(k+1)*(width m+1) := by
  have bound := StableCompactStep.network_internal F (width m)
  have size : (network F m k).internal = Fintype.card Empty + ∑ g : Gate m k, (parts F g).internal :=
    TypedWiring.glue_internal (parts F) (wire (m:=m) (k:=k))
  rw [size]
  simp only [Fintype.card_empty,zero_add,Fintype.sum_sum_type,
    parts,TypedWiring.localTable,TableCompiler.localTableNetwork_internal,Port,Fintype.card_fin,
    Finset.sum_const,Finset.card_univ,Fintype.card_unit,nsmul_eq_mul]
  nlinarith [Nat.mul_le_mul_left k bound, Nat.zero_le (k*width m)]

end ThreeFlat.Routing.StableCompactSite

end
end OAI
