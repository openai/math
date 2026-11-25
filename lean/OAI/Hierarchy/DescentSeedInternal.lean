import OAI.Hierarchy.DescentStageHistory

namespace OAI
/-! # Retaining the exterior hub equality while conditioning the inside atoms -/

namespace Hierarchy.DescentSixParty.Histories
open Computability.BorderVNP.Crossing DescentInitialHost
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {D : ℕ} {P : Type*} [Fintype P] {bits : P→ℕ}
variable (A : MarkedWorld F D P bits) (s : ℕ) (v : A.graph.Site)

abbrev SeedChoice (retain : Bool) := if retain then Count A.graph s v else PUnit

instance seedFinite (flag : Bool) : Fintype (SeedChoice A s v flag) := by
  cases flag <;> simp only [SeedChoice,Bool.false_eq_true,ite_false,ite_true] <;> infer_instance

def seedFactor : (flag : Bool)→SeedChoice A s v flag→F
  | false,_=>1
  | true,choice=>censusWeight A.graph A.tables s v choice

def seedEntry : (flag : Bool)→SeedChoice A s v flag→
    (∀e : {e : A.graph.Edge // A.graph.src e=v ∨ A.graph.dst e=v},Fin (s*A.graph.width e.1)→Bool)→
    (∀p : {p : P // A.graph.attach p=v},Fin (s*bits p.1)→Bool)→F
  | false,_,z,x=>stackTable A.graph A.tables v z x
  | true,choice,z,x=>censusTable A.graph s v choice z x

theorem seedEntry_sum (flag : Bool) (z : ∀e : {e : A.graph.Edge // A.graph.src e=v ∨ A.graph.dst e=v},
    Fin (s*A.graph.width e.1)→Bool) (x : ∀p : {p : P // A.graph.attach p=v},Fin (s*bits p.1)→Bool) :
    (∑h : SeedChoice A s v flag,seedFactor A s v flag h*seedEntry A s v flag h z x)=
      stackTable A.graph A.tables v z x := by
  cases flag
  · simp [SeedChoice,seedFactor,seedEntry]
  · exact local_histogram A.graph A.tables s v z x

variable (retain : A.graph.Site→Bool)
def seedInternal : Histories F D P (fun p=>s*bits p) where
  Choice := ∀u,SeedChoice A s u (retain u)
  finite := inferInstance
  state h := ⟨⟨stacked A.graph s,fun u=>seedEntry A s u (retain u) (h u)⟩,A.core⟩
  weight h := ∏u,seedFactor A s u (retain u) (h u)

theorem seedInternal_value (x : Ports (fun p=>s*bits p)) :
    (seedInternal A s retain).value x=∏i : Fin s,A.value (fun p=>rowAt (x p) i) := by
  change (∑ h : ∀ u, SeedChoice A s u (retain u),
    (∏ u, seedFactor A s u (retain u) (h u)) *
      (stacked A.graph s).value (fun u => seedEntry A s u (retain u) (h u)) x) =
    ∏ i : Fin s, A.graph.value A.tables (fun p => rowAt (x p) i)
  rw [←stack_value A.graph s A.tables x]
  unfold Network.value
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let factor (u : A.graph.Site) (h : SeedChoice A s u (retain u)) : F :=
    seedFactor A s u (retain u) h *
      seedEntry A s u (retain u) h (fun e => a e.val) (fun p => x p.val)
  calc
    _ = ∑ h : ∀ u, SeedChoice A s u (retain u), ∏ u, factor u (h u) := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [factor, Finset.prod_mul_distrib, Network.read]
      apply congrArg₂ (· * ·) rfl
      refine Finset.prod_congr ?_ ?_
      · ext u
        constructor <;> intro _ <;> apply @Finset.mem_univ
      · intro u _
        rfl
    _ = ∏ u, ∑ h, factor u h := (Fintype.prod_sum factor).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro u _
      exact seedEntry_sum A s u (retain u) _ _

end
end Hierarchy.DescentSixParty.Histories

end OAI
