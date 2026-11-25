import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank

/-!
# Shared labels and wires

A shared label gives each site in a set the same index. The other sites
have one active coordinate, fixed to zero. Wires are the two-site case.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral
variable (K : Type) [Field K] {S : Type} [Fintype S] [DecidableEq S]

namespace Raw

def port {n : ℕ} (U : Finset S) (s : S) (i : Fin n) : Fin n :=
  if s ∈ U then i else ⟨0, Nat.zero_lt_of_lt i.isLt⟩

def shared (U : Finset S) (n : ℕ) : Raw K S :=
  ⟨fun _ => Fin n, Fin n, fun i s x => if x = port U s i then 1 else 0⟩

abbrev wire (a b : S) (n : ℕ) : Raw K S := shared K {a, b} n

end Raw

namespace Tensor

def shared (U : Finset S) (n : ℕ) : Tensor K S := ofRaw (Raw.shared K U n)

abbrev wire (a b : S) (n : ℕ) : Tensor K S := shared K {a, b} n

theorem shared_all (n : ℕ) : shared K (Finset.univ : Finset S) n = n := by
  rw [← diag_fin]
  apply ofRaw_eq
  exact Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => by
    change Fin n at x i
    change (if x = Raw.port Finset.univ s i then (1 : K) else 0) = if x = i then 1 else 0
    simp [Raw.port]

theorem shared_one (U : Finset S) : shared K U 1 = 1 := by
  apply ofRaw_eq
  refine Raw.relabel (Equiv.ofUnique (Fin 1) Unit)
    (fun _ => Equiv.ofUnique (Fin 1) Unit) fun i s x => ?_
  change Fin 1 at i x
  change (if x = Raw.port U s i then (1 : K) else 0) = 1
  rw [ite_eq_left (Subsingleton.elim _ _)]

theorem shared_mul (U : Finset S) (n m : ℕ) :
    shared K U (n * m) = shared K U n * shared K U m := by
  symm
  apply ofRaw_eq
  refine Raw.relabel finProdFinEquiv (fun _ => finProdFinEquiv) fun i s x => ?_
  change Fin n × Fin m at i x
  have he : Raw.port U s (finProdFinEquiv i) =
      finProdFinEquiv (Raw.port U s i.1, Raw.port U s i.2) := by
    unfold Raw.port
    split
    · rfl
    · exact Fin.ext (by simp [finProdFinEquiv])
  change (if x.1 = Raw.port U s i.1 then (1 : K) else 0) *
      (if x.2 = Raw.port U s i.2 then 1 else 0) =
      if finProdFinEquiv x = Raw.port U s (finProdFinEquiv i) then 1 else 0
  simp only [he, Equiv.apply_eq_iff_eq, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul]

theorem shared_mono (U : Finset S) (hU : U.Nonempty) {n m : ℕ} (h : n ≤ m) :
    shared K U n ≤ shared K U m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨s, hs⟩ := hU
  apply Raw.Restricts.pullback (fun _ (x : Fin n) => Fin.castAdd d x)
  intro x
  change S → Fin n at x
  change (∑ i : Fin n, ∏ t, if x t = Raw.port U t i then (1 : K) else 0) =
    ∑ i : Fin (n + d), ∏ t, if Fin.castAdd d (x t) = Raw.port U t i then 1 else 0
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin d))), add_zero]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro t _
    simp only [Raw.port, Fin.ext_iff]
    split <;> rfl
  · intro i _
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp only [Raw.port, hs, ↓reduceIte, Fin.ext_iff]
    exact ite_eq_right (by simp; omega)

theorem wire_comm (a b : S) (n : ℕ) : wire K a b n = wire K b a n := by
  unfold wire
  rw [Finset.pair_comm]

theorem wire_mono (a b : S) : Monotone (wire K a b) :=
  fun _ _ h => shared_mono K _ (by simp) h

theorem one_le_wire (a b : S) {n : ℕ} (hn : 0 < n) : 1 ≤ wire K a b n := by
  rw [← shared_one K {a, b}]
  exact wire_mono K a b hn

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
