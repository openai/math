import OAI.Hierarchy.DescentMatchedSlabs
import Mathlib.Data.List.Nodup

namespace OAI
/-! # Distinct original graph atoms on both sides of all matched items -/

namespace Hierarchy.DescentPacking
open scoped Classical BigOperators
noncomputable section
variable {U V : Type*} [Fintype V] [DecidableEq V]
abbrev Atom (traffic : U → V → ℕ) := Σ u, Σ v,Fin (traffic u v)

omit [Fintype V] [DecidableEq V] in
theorem pack_get (ds : List (List U × Option V))
    (ok : (ds.map Prod.fst).flatten.Nodup) :
    Function.Injective (fun q : Σ a : Fin ds.length,Fin (ds.get a).1.length =>
      (ds.get q.1).1.get q.2) := by
  have separated := (List.nodup_flatten.mp ok).2
  have inner := (List.nodup_flatten.mp ok).1
  rw [List.pairwise_map] at separated
  rintro ⟨i,a⟩ ⟨j,b⟩ equal
  have avoid {m n : Fin ds.length} (lt : m<n)
      (x : Fin (ds.get m).1.length) (y : Fin (ds.get n).1.length) :
      (ds.get m).1.get x ≠ (ds.get n).1.get y := by
    have free := separated.rel_get_of_lt lt
    intro h
    exact (List.disjoint_left.mp free) (List.get_mem _ x) (h.symm ▸ List.get_mem _ y)
  obtain rfl : i=j := by
    rcases lt_trichotomy i j with less|eqn|less
    · exact False.elim (avoid less a b equal)
    · exact eqn
    · exact False.elim (avoid less b a equal.symm)
  have nod := inner _ (List.mem_map.mpr ⟨ds.get i,List.get_mem _ _,rfl⟩)
  exact congrArg (Sigma.mk i) (List.nodup_iff_injective_get.mp nod equal)

def thinAtom (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (e : Matched traffic B thin thick) : Atom traffic :=
  let d := oldThin traffic B thin thick e
  ⟨((slabPacking traffic B thin thick).decisions.get d.1).1.get d.2.1,d.2.2⟩

def thickAtom (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (e : Matched traffic B thin thick) : Atom traffic :=
  let d := oldThick traffic B thin thick e
  ⟨thick.get d.2.1,d.1,d.2.2⟩

theorem thinAtom_injective (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (ok : thin.Nodup) : Function.Injective (thinAtom traffic (B:=B) (thin:=thin) (thick:=thick)) := by
  let ds := (slabPacking traffic B thin thick).decisions
  have unique := pack_get ds (by simpa [ds,thin_stream] using ok)
  intro e e' he
  apply (oldThin traffic B thin thick).injective
  generalize h : oldThin traffic B thin thick e=p
  generalize h' : oldThin traffic B thin thick e'=q
  unfold thinAtom at he
  rw [h,h'] at he
  rcases p with ⟨i,a,v,w⟩
  rcases q with ⟨j,b,u,z⟩
  have pair : (⟨i,a⟩ : Σ x : Fin ds.length,Fin (ds.get x).1.length)=⟨j,b⟩ := unique (congrArg Sigma.fst he)
  cases pair
  cases he
  rfl

theorem thickAtom_injective (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (ok : thick.Nodup) : Function.Injective (thickAtom traffic (B:=B) (thin:=thin) (thick:=thick)) := by
  intro e e' he
  apply (oldThick traffic B thin thick).injective
  generalize h : oldThick traffic B thin thick e=p
  generalize h' : oldThick traffic B thin thick e'=q
  unfold thickAtom at he
  rw [h,h'] at he
  rcases p with ⟨v,i,b⟩
  rcases q with ⟨w,j,c⟩
  obtain rfl : i=j := List.nodup_iff_injective_get.mp ok (congrArg Sigma.fst he)
  cases he
  rfl

theorem thinAtom_in (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (e : Matched traffic B thin thick) : (thinAtom traffic e).1∈thin := by
  let d := oldThin traffic B thin thick e
  let ds := (slabPacking traffic B thin thick).decisions
  apply (congrArg (fun l=>(thinAtom traffic e).1∈l) (thin_stream traffic B thin thick)).mp
  exact List.mem_flatten.mpr ⟨(ds.get d.1).1,
    List.mem_map.mpr ⟨ds.get d.1,List.get_mem _ _,rfl⟩,List.get_mem _ _⟩

/-- Each matched pair supplies two genuinely distinct old wires, and no wire
is reused by any other application, including at the same two endpoints. -/
def pairAtoms (traffic : U → V → ℕ) {B : ℕ} {thin thick : List U}
    (lo : thin.Nodup) (hi : thick.Nodup) (separate : thin.Disjoint thick) :
    Matched traffic B thin thick × Fin 2 ↪ Atom traffic where
  toFun p := if p.2=0 then thickAtom traffic p.1 else thinAtom traffic p.1
  inj' := by
    rintro ⟨a,s⟩ ⟨b,t⟩ eqn
    have noHit (a b : Matched traffic B thin thick) : thinAtom traffic a≠thickAtom traffic b := by
      intro e
      have z := congrArg Sigma.fst e
      have belongs : (thickAtom traffic b).1∈thick := List.get_mem _ _
      exact (List.disjoint_left.mp separate) (thinAtom_in traffic a) (z.symm ▸ belongs)
    fin_cases s <;> fin_cases t <;> simp only [Fin.isValue] at eqn ⊢
    · exact Prod.ext (thickAtom_injective traffic hi eqn) rfl
    · exact False.elim (noHit b a eqn.symm)
    · exact False.elim (noHit a b eqn)
    · exact Prod.ext (thinAtom_injective traffic lo eqn) rfl

end
end Hierarchy.DescentPacking

end OAI
