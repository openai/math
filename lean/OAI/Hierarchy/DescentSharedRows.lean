import OAI.Hierarchy.DescentFineRows
import OAI.Hierarchy.DescentBadBundles

namespace OAI
/-! # One input row for an old tensor across both reset routing banks -/

namespace Hierarchy.DescentFineTerminals
open DescentColonies DescentBaseProfile DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k f D Y B : ℕ} [NeZero Y]
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v x,wt v x≤B)
variable (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
variable (keys : Finset (V×ℕ)) (hub : V→Prop)
local notation "occ" => occupants (D:=D) (f:=f) near wt room b
local notation "key" => leafKey (D:=D) (f:=f) near wt room b

omit [Fintype V] [DecidableEq V] in
/-- Two remixed occurrences in the same refined leaf have the same original
dyadic base. This also fixes whether the base uses rotor hardware. -/
theorem base_same {v : V} {x y : Block k} (same : key v x=key v y) :
    baseOf b hk L (v,(rearrange L).symm x)=baseOf b hk L (v,(rearrange L).symm y) := by
  have depthEq := congrArg Prod.fst same
  change leaf (D:=D) (f:=f) near wt room b v x=leaf (D:=D) (f:=f) near wt room b v y at depthEq
  have groupEq := congrArg Prod.snd same
  change group (leaf (D:=D) (f:=f) near wt room b v x) x=group (leaf (D:=D) (f:=f) near wt room b v y) y at groupEq
  rw [depthEq] at groupEq
  apply congrArg (Sigma.mk v)
  apply Fin.ext
  simpa only [layout_id,Equiv.apply_symm_apply] using group_ancestor (d:=b v) (le_max_left ..) groupEq

abbrev OldBase (g : BaseId b) := {o : V×Block k // baseOf b hk L o=g}
def paid (o : V×Block k) : Prop := baseOf b hk L o∉validBases b keys ∧ ¬hub o.1

variable (enough : Y≤2^f) (goodRow : Bool→V×Block k→Fin Y)

/-- Preserve the same row as the installed rotor when its base is good,
including for the old items whose opposite endpoint uses a fallback tree. -/
def sharedRow (s : Bool) (o : V×Block k) : Fin Y :=
  if paid b hk L keys hub o then goodRow s o
  else oldRow (D:=D) near wt room b enough L s o

local notation "R" => sharedRow (D:=D) near wt room b hk L keys hub enough goodRow

@[simp] theorem shared_of_paid {o : V×Block k} (g : paid b hk L keys hub o) (s : Bool) :
    R s o=goodRow s o := ite_eq_left g

theorem shared_side (common : ∀s t o,goodRow s o=goodRow t o) (s t : Bool) (o : V×Block k) :
    R s o=R t o := by
  by_cases active : paid b hk L keys hub o
  · simpa [sharedRow,active] using common s t o
  · simp [sharedRow,active,oldRow]

/-- Both kinds of terminal respect the original whole-item account. The
weights may be side-specific physical loads, bounded by the remixed charges
used to choose exceptional rows. -/
theorem shared_bound (charge : Bool→V×Block k→ℝ)
    (positive : ∀s o,0≤charge s o)
    (small : ∀s v x,charge s (v,(rearrange L).symm x)≤(wt v x:ℝ))
    (holds : ∀s (g : BaseId b),g∉validBases b keys→¬hub g.1→∀j,
      inputLoad Finset.univ (fun z : OldBase b hk L g=>charge s z.val)
        (fun z=>goodRow s z.val) j≤3*((2^f*B:ℕ):ℝ)/Y)
    (s : Bool) (v : V) (p : ℕ×ℕ) (j : Fin Y) :
    inputLoad (occ v p) (fun x=>charge s (v,(rearrange L).symm x))
      (fun x=>R s (v,(rearrange L).symm x)) j ≤3*((2^f*B:ℕ):ℝ)/Y := by
  by_cases inhabited : (occ v p).Nonempty
  · obtain ⟨x,member⟩ := inhabited
    let o (x : Block k) := (v,(rearrange L).symm x)
    let g := baseOf b hk L (o x)
    have in_same (z : Block k) (hz : z∈occ v p) : baseOf b hk L (o z)=g :=
      base_same near wt room b hk L (((Finset.mem_filter.mp hz).2).trans (Finset.mem_filter.mp member).2.symm)
    by_cases isGood : paid b hk L keys hub (o x)
    · let lift : ↥(occ v p) ↪ OldBase b hk L g :=
        ⟨fun z=>⟨o z.val,in_same z.val z.property⟩,fun a c eqn=>Subtype.ext
          ((rearrange L).symm.injective (congrArg (fun z : OldBase b hk L g=>z.val.2) eqn))⟩
      let bill (z : OldBase b hk L g) := if goodRow s z.val=j then charge s z.val else 0
      have equate (z : ↥(occ v p)) :
          (if R s (o z.val)=j then charge s (o z.val) else 0)=bill (lift z) := by
        have hg : paid b hk L keys hub (o z.val) := ⟨(in_same z.val z.property).symm ▸ isGood.1,isGood.2⟩
        simp only [shared_of_paid near wt room b hk L keys hub enough goodRow hg s]
        rfl
      calc
        _ = ∑z : ↥(occ v p),bill (lift z) := by
          unfold inputLoad
          rw [←Finset.sum_coe_sort]
          exact Finset.sum_congr rfl fun z _=>equate z
        _ = ∑z∈Finset.univ.map lift,bill z := (Finset.sum_map _ _ _).symm
        _ ≤ ∑z,bill z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun z _ _=>by
          dsimp only [bill]
          split <;> simp [positive]
        _ ≤ _ := holds s g isGood.1 isGood.2 j
    · have bound := row_bound (D:=D) near wt room b enough v p j
      apply le_trans _ bound
      unfold inputLoad
      apply Finset.sum_le_sum
      intro z hz
      have no : ¬paid b hk L keys hub (o z) := by
        intro temp
        refine isGood ⟨?_,temp.2⟩
        change g ∉ validBases b keys
        rw [←in_same z hz]
        exact temp.1
      change (if R s (o z)=j then charge s (o z) else 0)≤_
      simp only [sharedRow,ite_eq_right no,oldRow,o,Equiv.apply_symm_apply]
      split <;> simp [small]
  · have empty := Finset.not_nonempty_iff_eq_empty.mp inhabited
    simp [inputLoad,empty]; positivity

end
end Hierarchy.DescentFineTerminals

end OAI
