import OAI.Computability.BorderVNP.CellGuardedObservations
import OAI.Computability.BorderVNP.CellPacketFieldMonotone
import OAI.Computability.BorderVNP.CellGadgetSteps

/-! # Range and size of a genuine observed scalar count word -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Every stored named scalar is one of the declared report coordinates. -/
def Factor.IDRange (n : ℕ) : Factor → Prop
  | .gadget _ ids => ∀ i ∈ ids, i<n
  | _ => True

theorem Factor.IDBound.range {f : Factor} {n : ℕ} (h : f.IDBound (n-1)) (positive : 0<n) : f.IDRange n := by
  cases f with
  | gadget => intro i hi; exact (h i hi).trans_lt (by omega)
  | _ => trivial

private theorem factor_seen {f : Factor} {n : ℕ} (hf : f.IDRange n) (bank : ℕ → Bool)
    (off copy : ℕ) {o : Bool × Option ℕ} (run : f.observe bank off copy = some o) :
    ∀ i, o.2=some i → i<n := by
  cases f with
  | gadget ws ids =>
    cases ha : ids[word bank (ws.map (off+·))]? with
    | none => simp [Factor.observe,ha] at run
    | some k =>
      have eq := Option.some.inj (show some (false,some k)=some o by simpa only [Factor.observe,ha,Option.map_some] using run)
      subst o
      intro i hki
      have e : k=i := Option.some.inj hki
      exact e ▸ hf k (List.mem_of_getElem? ha)
  | sign ws rs =>
    cases ha : rs[word bank (ws.map (off+·))]? <;> simp only [Factor.observe,ha,Option.map_none,Option.map_some] at run
    all_goals cases run <;> simp
  | truth | unary =>
    simp only [Factor.observe] at run
    split at run <;> cases run
    simp

private theorem list_seen {n : ℕ} (os : List Occurrence) (h : ∀ o ∈ os, o.factor.IDRange n) (bank : ℕ → Bool)
    {out : List (Bool × Option ℕ)}
    (seen : os.mapM (fun o => o.factor.observe bank o.offset o.copy) = some out) :
    (∀ i ∈ out.filterMap Prod.snd, i<n) ∧ out.length=os.length := by
  induction os generalizing out with
  | nil => simp at seen; subst out; simp
  | cons o os ih =>
    cases first : o.factor.observe bank o.offset o.copy with
    | none => simp [List.mapM_cons,first] at seen
    | some a =>
      cases tail : os.mapM (fun o => o.factor.observe bank o.offset o.copy) with
      | none => simp [List.mapM_cons,first,tail] at seen
      | some rest =>
        simp [List.mapM_cons,first,tail] at seen
        subst out
        obtain ⟨ids,length⟩ := ih (fun x hx => h x (.tail _ hx)) tail
        refine ⟨?_,by simp [length]⟩
        intro i hi
        rcases a with ⟨b,tag⟩
        cases tag with
        | none => exact ids i hi
        | some j =>
          rcases List.mem_cons.mp hi with eq|hi
          · exact eq ▸ factor_seen (h o List.mem_cons_self) bank o.offset o.copy first j rfl
          · exact ids i hi

/-- The observed IDs are in the true table directory and each multiplicity
is at most the actual number of factor visits. -/
theorem Directory.observed_range_counts {D : Directory} {n : ℕ}
    (stored : ∀ fs ∈ D.boxes, ∀ f ∈ fs, f.IDRange n) (bank : ℕ → Bool) {out : List (Bool × Option ℕ)}
    (seen : D.guardedObservations bank=some out) :
    (∀ i ∈ out.filterMap Prod.snd, i<n) ∧ ∀ i, (out.filterMap Prod.snd).count i ≤ D.visitCount := by
  have oc (o : Occurrence) (ho : o ∈ D.occurrences) : o.factor.IDRange n := by
    obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp ho
    cases r with
    | box id base copies stride =>
      change o ∈ (List.range copies).flatMap (fun i => (D.boxes.getD id []).map
        (fun f => (⟨f,base+i*stride,i⟩ : Occurrence))) at hr
      obtain ⟨_,_,hm⟩ := List.mem_flatMap.mp hr
      obtain ⟨f,hf,e⟩ := List.mem_map.mp hm
      subst o
      by_cases hi : id < D.boxes.length
      · rw [List.getD_eq_getElem _ _ hi] at hf
        exact stored _ (List.getElem_mem hi) f hf
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at hf
        cases hf
    | _ => cases hr
  obtain ⟨hr,hl⟩ := list_seen D.occurrences oc bank (Directory.guarded_some.mp seen).2
  refine ⟨hr,fun i => (List.count_le_length ..).trans ?_⟩
  have bound := List.length_filterMap_le Prod.snd out
  rw [hl] at bound
  exact bound.trans_eq D.visitCount_eq.symm

end CellSparse

end BorderVNP
end Computability
end OAI
