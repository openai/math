import OAI.Computability.NearSquareRoot.SynchronizedBorrowing
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic

/-! # Completing a list of active pairs into a physical routing table

For a local address block, enumerate the two endpoints of each active pair and
then enumerate every remaining address in its original order. Adjacent positions
in the resulting permutation pair all idle cells. No search for a matching is
needed. The same table read backwards by lookup inverts the routing.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutingTable

variable {A : Type} [DecidableEq A]

def endpoints (pairs : List (A × A)) : List A :=
  pairs.flatMap (fun p => [p.1,p.2])

def complete (cells : List A) (pairs : List (A × A)) : List A :=
  endpoints pairs ++ cells.filter (fun x => x ∉ endpoints pairs)

theorem complete_perm (cells : List A) (pairs : List (A × A))
    (hu : cells.Nodup) (hp : (endpoints pairs).Nodup) (hm : ∀ x ∈ endpoints pairs, x ∈ cells) :
    (complete cells pairs).Perm cells := by
  have hn : (complete cells pairs).Nodup := by
    rw [complete, List.nodup_append]
    exact ⟨hp,hu.filter _, by simp; grind⟩
  apply (List.perm_ext_iff_of_nodup hn hu).mpr
  intro x
  simp only [complete,List.mem_append,List.mem_filter,decide_eq_true_eq]
  by_cases h : x ∈ endpoints pairs <;> grind

omit [DecidableEq A] in
@[simp] theorem length_endpoints (pairs : List (A × A)) : (endpoints pairs).length = 2*pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    change (p.1 :: p.2 :: endpoints ps).length = 2*(ps.length+1)
    simp only [List.length_cons]
    omega

omit [DecidableEq A] in
theorem endpoints_get (pairs : List (A × A)) (i : Fin pairs.length) (b : Fin 2) :
    (endpoints pairs)[2*i.val+b.val]? = some (if b=0 then pairs[i].1 else pairs[i].2) := by
  induction pairs with
  | nil => exact i.elim0
  | cons a t ih =>
    cases i using Fin.cases with
    | zero => fin_cases b <;> rfl
    | succ i =>
      have hi : 2*i.succ.val+b.val = (2*i.val+b.val)+2 := by simp; omega
      rw [hi]
      exact ih i

theorem complete_active (cells : List A) (pairs : List (A × A)) (i : Fin pairs.length) (b : Fin 2) :
    (complete cells pairs)[2*i.val+b.val]? = some (if b=0 then pairs[i].1 else pairs[i].2) := by
  have hi := i.isLt
  have hb := b.isLt
  rw [complete,List.getElem?_append_left (by rw [length_endpoints]; omega)]
  exact endpoints_get pairs i b

theorem complete_idle (cells : List A) (pairs : List (A × A)) (i : ℕ) :
    (complete cells pairs)[2*pairs.length+i]? =
      (cells.filter (fun x => x ∉ endpoints pairs))[i]? := by
  rw [complete,List.getElem?_append_right (by rw [length_endpoints];omega), length_endpoints]
  simp

/-- Read the completed table in the forward direction, invert by its unique row index. -/
def routing {n : ℕ} (pairs : List (Fin n × Fin n)) (hp : (endpoints pairs).Nodup) : Equiv.Perm (Fin n) :=
  let table := complete (List.finRange n) pairs
  have he := complete_perm (List.finRange n) pairs (List.nodup_finRange _) hp (by simp)
  have hl : table.length = n := he.length_eq.trans List.length_finRange
  { toFun j := table[j.val]'(by rw [hl]; exact j.isLt)
    invFun a := ⟨table.idxOf a, by
      exact (List.idxOf_lt_length_iff.mpr (he.mem_iff.mpr (List.mem_finRange a))).trans_eq hl⟩
    left_inv j := Fin.ext (by
      have hn : table.Nodup := he.nodup_iff.mpr (List.nodup_finRange _)
      exact hn.idxOf_getElem _ _)
    right_inv _ := List.getElem_idxOf _ }

theorem routing_reads {n : ℕ} (pairs : List (Fin n × Fin n)) (hp : (endpoints pairs).Nodup)
    (j : Fin n) : (complete (List.finRange n) pairs)[j.val]? = some (routing pairs hp j) :=
  List.getElem?_eq_getElem _

/-- Consecutive positions in the completed routing table make a full oriented matching. -/
def matching {n : ℕ} (he : Even n) (pairs : List (Fin n × Fin n)) (hp : (endpoints pairs).Nodup) :
    Fin 2 × Fin (n/2) ≃ Fin n :=
  (Equiv.prodComm ..).trans (finProdFinEquiv.trans ((finCongr (by obtain ⟨m,hm⟩ := he; omega)).trans (routing pairs hp)))

theorem matching_active {n : ℕ} (he : Even n) (pairs : List (Fin n × Fin n))
    (hp : (endpoints pairs).Nodup) (i : Fin pairs.length) (b : Fin 2) :
    ∃ hi : i.val < n/2,
      matching he pairs hp (b,⟨i.val,hi⟩) = (if b=0 then pairs[i].1 else pairs[i].2) := by
  have perm := complete_perm (List.finRange n) pairs (List.nodup_finRange _) hp (by simp)
  have hn := perm.length_eq
  rw [complete,List.length_append,length_endpoints,List.length_finRange] at hn
  have hi := i.isLt
  have hb := b.isLt
  have hi' : i.val < n/2 := by omega
  refine ⟨hi',?_⟩
  let j : Fin n := ⟨b.val+2*i.val,by omega⟩
  change routing pairs hp j = _
  apply Option.some.inj
  rw [← routing_reads pairs hp j]
  simpa only [j,Nat.add_comm b.val] using complete_active (List.finRange n) pairs i b

end ShortFourier.RoutingTable

end NearSquareRoot
end Computability
end OAI
