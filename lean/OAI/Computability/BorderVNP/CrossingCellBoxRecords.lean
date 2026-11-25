import OAI.Computability.BorderVNP.CrossingCellBox

/-!
# The sparse box record of a bank junction

One directory entry suffices for all copies of a fixed one-copy local tensor.
Its observations give exactly the gadget-position list whose weights multiply
to the local profile table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.CellBox

open CellSparse
open scoped BigOperators Classical

/-- The public descriptor and fixed private directory for one repeated box. -/
def directory (f : Factor) (copies stride : ℕ) : Directory :=
  ⟨[[f]], [.box 0 0 copies stride], []⟩

/-- The sparse directory calls the same factor in copy order, with the prescribed stride. -/
theorem directory_occurrences (f : Factor) (copies stride : ℕ) :
    (directory f copies stride).occurrences =
      List.ofFn (fun i : Fin copies => (⟨f,i.val * stride,i.val⟩ : Occurrence)) := by
  simp only [Directory.occurrences, directory, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.getD_cons_zero, List.map_cons, List.map_nil, Nat.zero_add]
  rw [← List.map_eq_flatMap]
  apply List.ext_getElem <;> simp

private theorem mapM_ofFn {A B : Type} {n : ℕ} (f : A → Option B)
    (a : Fin n → A) (b : Fin n → B) (h : ∀ i, f (a i) = some (b i)) :
    (List.ofFn a).mapM f = some (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons, h,
      ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)]
    rfl

variable {A D j d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable (N : Fin A → Network D P bits)
variable (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)
variable (p : Fin A → ℕ) (a : Fin A) (v : (N a).Site) (order : Lane (N a) v ≃ Fin d)
variable (id : ∀ t, (N t).Tables ℕ)

/-- Fixed sparse private directory of a bank site, with one repeated descriptor. -/
noncomputable def bankDirectory : Directory :=
  directory (factor (N a) (id a) v order Fin.val) (p a) d

/-- One actual gadget-position observation per copy, even for positions of scalar zero. -/
theorem bankDirectory_observations (y : (Profile.network N place hball j p).Assignment) :
    let lanes := bankLanes N place hball p y a v
    let bank := packedBank (fun i k => lanes i (order.symm k))
    (bankDirectory N p a v order id).observations bank = some (List.ofFn
      fun i => (false, some (localRow (N a) (id a) v (lanes i)))) := by
  dsimp only
  rw [Directory.observations, bankDirectory, directory_occurrences]
  apply mapM_ofFn
  exact fun i => observe_bank N place hball p y a v order (id a) i

/-- Evaluating the listed positions multiplicatively is exactly the field (or tally)
weight read by this bank site of the physical network. -/
theorem bankSite_read {R : Type*} [CommMonoidWithZero R] (weight : ℕ → R) (first : P)
    (y : (Profile.network N place hball j p).Assignment)
    (x : Ports (fun u => j * bits u)) :
    (Profile.network N place hball j p).read
        (Profile.tables N place hball j p first (fun t v c b => weight (id t v c b)))
        y x (.inr (.inr ⟨a,v⟩)) =
      ∏ i : Fin (p a), weight (localRow (N a) (id a) v (bankLanes N place hball p y a v i)) :=
  rfl

end Crossing.CellBox

end BorderVNP
end Computability
end OAI
