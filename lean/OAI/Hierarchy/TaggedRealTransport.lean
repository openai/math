import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Lattice
import Mathlib.Tactic

namespace OAI
/-! # Real-record transport through radix padding and reblocking

A transport records a bijection of the real rows. When this bijection
preserves order, changing the number of dummy slots leaves the sequence of
real words unchanged.
-/

namespace Hierarchy.Tagged.Radix
open scoped Classical
noncomputable section

variable {I J K W D : Type*} (real : W → Prop)

abbrev Live (x : I → W) := {i : I // real (x i)}

structure RealTransport (x : I → W) (y : J → W) where
  route : Live real x ≃ Live real y
  read : ∀ i, y (route i).val = x i.val

namespace RealTransport
variable {real} {x : I → W} {y : J → W} {z : K → W}

/-- A physical row permutation induces a transport of all real rows. -/
def perm (f : J ≃ I) (x : I → W) : RealTransport real x (x ∘ f) where
  route := f.symm.subtypeEquiv (fun i => by simp)
  read i := by simp [Function.comp_apply]

private def realSet {n : ℕ} (x : Fin n → W) (p : W → Prop) := Finset.univ.filter fun i => p (x i)
private def selected {n : ℕ} (x : Fin n → W) (p : W → Prop) : List W :=
  (List.ofFn x).filter fun w => decide (p w)

private theorem ordered_read {n r : ℕ} (x : Fin n → W) (p : W → Prop)
    (e : Fin r ≃ realSet x p) (ordered : StrictMono fun i => (e i).val) :
    selected x p = List.ofFn (fun i => x (e i).val) := by
  let all := List.ofFn (id : Fin n → Fin n)
  let live := all.filter (fun i => decide (p (x i)))
  let seq := List.ofFn (fun i => (e i).val)
  have allOrdered : all.Pairwise (· < ·) := List.pairwise_ofFn.mpr fun _ _ h => h
  have liveOrdered : live.Pairwise (· < ·) := allOrdered.filter _
  have seqOrdered : seq.Pairwise (· < ·) := List.pairwise_ofFn.mpr fun _ _ h => ordered h
  have idx : live = seq := by
    apply List.Perm.eq_of_pairwise' (r := (· ≤ · : Fin n → Fin n → Prop))
      (liveOrdered.imp fun h => h.le) (seqOrdered.imp fun h => h.le)
    apply (List.perm_ext_iff_of_nodup (liveOrdered.imp fun h => h.ne) (seqOrdered.imp fun h => h.ne)).mpr
    intro i
    constructor
    · intro h
      have mem : i ∈ realSet x p := by simpa [live,all,realSet] using h
      exact List.mem_ofFn.mpr ⟨e.symm ⟨i,mem⟩,by simp⟩
    · intro h
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨(e j).val,rfl⟩,
        decide_eq_true (Finset.mem_filter.mp (e j).property).2⟩
  have project (xs : List (Fin n)) : (xs.map x).filter (fun w => decide (p w))=
      (xs.filter (fun i => decide (p (x i)))).map x := by
    induction xs with
    | nil => rfl
    | cons i xs ih => by_cases ok : p (x i) <;> simp [ok,ih]
  have eq := (project all).trans (congrArg (List.map x) idx)
  simpa only [selected,all,seq,List.map_ofFn,Function.comp_def,id_eq] using eq

/-- A strictly increasing transport of the selected rows preserves their
entire list of words in physical lane order. -/
theorem same_read {n m : ℕ} {x : Fin n → W} {y : Fin m → W} (a : RealTransport real x y)
    (ascending : StrictMono a.route) :
    (List.ofFn y).filter (fun w => decide (real w)) = (List.ofFn x).filter (fun w => decide (real w)) := by
  let s := realSet x real
  let l := s.orderIsoOfFin rfl
  let a' : s ≃ realSet y real :=
    (Equiv.subtypeEquivRight (fun i => by simp [s,realSet])).trans
      (a.route.trans (Equiv.subtypeEquivRight fun i => by simp [realSet]))
  have mono : StrictMono a' := fun _ _ lt => ascending lt
  rw [show (List.ofFn y).filter (fun w => decide (real w)) = selected y real from rfl,
    ordered_read y real (l.toEquiv.trans a') (mono.comp l.strictMono),
    show (List.ofFn x).filter (fun w => decide (real w)) = selected x real from rfl,
    ordered_read x real l.toEquiv l.strictMono]
  congr 1
  funext i
  exact a.read ⟨(l i).val,(Finset.mem_filter.mp (l i).property).2⟩

end RealTransport
end
end Hierarchy.Tagged.Radix

end OAI
