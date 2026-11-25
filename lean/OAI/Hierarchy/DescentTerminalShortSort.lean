import OAI.Hierarchy.TaggedSortRelation
import OAI.Hierarchy.TaggedSliceData
import OAI.Hierarchy.DescentTerminalTagGroups

namespace OAI
/-! # Physical short-sort shells closed by a single homogeneous tag format -/

namespace Hierarchy.Tagged.TerminalSort
open ThreeFlat Routing SortNetwork
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {n s w d m L : ℕ}
variable (width : Fin m→ℕ) (cover : (∑j,width j)=n+w) (room : ∀j,width j≤n+s)

abbrev Socket (_n s m L : ℕ) := Fin m × Fin (poolBatchCount L (2^s))
abbrev Hole (n w : ℕ) := Fin (pins n (n+w))

/-- Each call shares the original guessed source tags for every record
field. Literal pins implement the surplus rows and the width padding. -/
def read (call : Socket n s m L) (pin : Fin (pins (n+s) (n+s))) :
    (Fin L×Hole n w) ⊕ Bool :=
  (TerminalGroups.wire n s (width call.1) L (room call.1) call.2 pin).map
    (fun z=>(z.1,Slices.pin width cover call.1 z.2)) id

theorem homogeneous_tags [Nonempty (Fin m)] (x : Fin L→Hole n w→Bool) :
    (∏ t : Socket n s m L,coeff F (n+s) (n+s)
      (Sum.elim (fun z=>x z.1 z.2) id ∘ read width cover room t)) =
      ∏i,coeff F n (n+w) (x i) := by
  rw [Fintype.prod_prod_type]
  calc
    _ = ∏j : Fin m,∏i : Fin L,coeff F n (width j) (x i ∘ Slices.pin width cover j) := by
      apply Finset.prod_congr rfl
      intro j _
      refine Eq.trans ?_ (TerminalGroups.eval F n s (width j) L (room j)
        (fun a=>x a.1 (Slices.pin width cover j a.2)))
      apply Finset.prod_congr rfl
      intro b _
      apply congrArg (coeff F _ _)
      funext pin
      simp only [Function.comp_apply,read]
      cases TerminalGroups.wire n s (width j) L (room j) b pin <;> rfl
    _ = _ := by
      rw [Finset.prod_comm]
      exact Finset.prod_congr rfl fun i _=>Slices.coefficient width cover (x i)

def sorted (digit : Fin d→Fin w) (input : Records n w) : Records n w :=
  input ∘ Tuple.sort (fun i=>addressEquiv d (input i ∘ digit))

/-- The very same shells are counted below. The hidden addresses shared
by the sliced tag tests are forced by stability of each local sort. -/
theorem sorts [Nonempty (Fin m)] (digit : Fin d→Fin w) (input : Fin L→Records n w)
    (out : Fin L→SortRelation.Data n w→Bool) :
    (∑ a : Fin L→Hole n w→Bool,
      (∏i,TypedWiring.value (SortRelation.shell F digit) (Sum.elim (Sum.elim (pack (input i)) (out i)) (a i)))*
      (∏ t : Socket n s m L,coeff F (n+s) (n+s)
        (Sum.elim (fun z=>a z.1 z.2) id ∘ read width cover room t))) =
      if ∀i,out i=pack (sorted digit (input i)) then 1 else 0 := by
  simp_rw [homogeneous_tags width cover room]
  simp_rw [←Finset.prod_mul_distrib]
  let factor (i : Fin L) (hole : Hole n w → Bool) :=
    TypedWiring.value (SortRelation.shell F digit)
      (Sum.elim (Sum.elim (pack (input i)) (out i)) hole) * coeff F n (n+w) hole
  change (∑ a : Fin L → Hole n w → Bool, ∏ i, factor i (a i)) = _
  refine (Fintype.prod_sum factor).symm.trans ?_
  dsimp only [factor]
  simp only [SortRelation.eval,sorted,Fintype.prod_boole]
  let ok := ∀ i, out i = pack (sorted digit (input i))
  have same (a b : Decidable ok) : @ite F ok a 1 0 = @ite F ok b 1 0 := by
    rw [Subsingleton.elim a b]
  exact same _ _

/-- Total tag pin volume depends on the actual number of short sorts,
with at most one unfinished homogeneous batch in each field slice. -/
theorem tag_volume : Fintype.card (Socket n s m L)*2^(n+s) ≤ m*(L*2^n+2^(n+s)) := by
  simp only [Socket,Fintype.card_prod,Fintype.card_fin,Nat.mul_assoc]
  exact Nat.mul_le_mul_left m (TerminalGroups.height_slots n s L)

theorem shells_price (digit : Fin d→Fin w) :
    L*((SortRelation.shell F digit (h:=n)).cells+(SortRelation.shell F digit (h:=n)).internal) ≤
      L*(2^n*((n+n+w)+(n+d+1)+(n+d+2)*176+28*w)+28*pins n (n+w)) :=
  Nat.mul_le_mul_left L (SortRelation.size F digit)

end
end Hierarchy.Tagged.TerminalSort

end OAI
