import OAI.Computability.BorderVNP.CrossingCellProfile
import OAI.Computability.BorderVNP.CellSparseSemantics

/-!
# Sparse records for the profile origin and its terminals

Each terminal needs one profile record. The origin reads a route-free profile
on its reference spoke and compares all selector spokes with that spoke.
The resulting record predicates equal the local physical network tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile.Cell

open CellSparse
open scoped Classical
variable {A j D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {K : Type*} [CommSemiring K]

/-- One private cell record at a terminal, with one compact feeder for each term. -/
def terminalRecord (j b : ℕ) (p : Fin A → ℕ) (s original : Port) (compact : Fin A → Port) :
    Record :=
  .profile j s (Nat.clog 2 A) (List.ofFn p) (routes A b original compact)

/-- One reference header and one whole-selector equality per terminal spoke. -/
noncomputable def originRecords (j : ℕ) (p : Fin A → ℕ) (first : P) (spokes : P → Port) :
    List Record :=
  .profile j (spokes first) (Nat.clog 2 A) (List.ofFn p) [] ::
    List.ofFn fun i : Fin (Fintype.card P) =>
      .equal j (Nat.clog 2 A) (spokes ((Fintype.equivFin P).symm i)) (spokes first)

/-- Equality of all addressed binary lanes is exactly equality of the physical selector blocks. -/
theorem equalValid_selector (bank : ℕ → Bool) (s t : Port) (j A : ℕ) :
    equalValid bank j (Nat.clog 2 A) s t ↔
      selector (A := A) (j := j) bank s = selector bank t := by
  constructor
  · intro h
    funext i l
    exact congrArg finTwoEquiv.symm (h i i.isLt l l.isLt)
  · intro h i hi l hl
    exact finTwoEquiv.symm.injective (congrFun (congrFun h (⟨i, hi⟩ : Fin j))
      (⟨l, hl⟩ : Fin (Nat.clog 2 A)))

/-- The route-free reference record checks exactly the common selector's codes and counts. -/
theorem reference_record_iff (bank : ℕ → Bool) (s : Port) (j : ℕ) (p : Fin A → ℕ) :
    profileValid bank j s (Nat.clog 2 A) (List.ofFn p) [] ↔
      ∃ w : Fin j → Fin A, decode (selector bank s) = some w ∧ histogram w = p := by
  simp only [profileValid, List.length_ofFn, List.not_mem_nil, false_implies, implies_true, and_true]
  exact (and_congr_right fun _ => histRow_iff (fun a => earlier bank s (Nat.clog 2 A) a j) p).trans
    (header_iff bank s p)

/-- Simultaneous validity of the origin's sparse records is exactly the origin table predicate. -/
theorem origin_records_iff (bank : ℕ → Bool) (j : ℕ) (p : Fin A → ℕ) (first : P)
    (spokes : P → Port) (boxes : List (List Factor)) :
    (∀ r ∈ originRecords j p first spokes, r.Valid boxes bank) ↔
      originTest (j := j) first p (fun u => selector bank (spokes u)) := by
  simp only [originRecords, List.forall_mem_cons, Record.Valid, List.forall_mem_ofFn_iff,
    reference_record_iff, equalValid_selector]
  constructor
  · rintro ⟨⟨w, hd, hp⟩, hs⟩
    have he (u : P) : selector (A := A) (j := j) bank (spokes u) = selector bank (spokes first) := by
      simpa using hs (Fintype.equivFin P u)
    refine ⟨w, ?_, hp⟩
    rw [readSpokes, ite_eq_left he]
    exact hd
  · rintro ⟨w, hd, hp⟩
    have hb := (readSpokes_eq_some_iff first _ w).1 hd
    refine ⟨⟨w, (decode_eq_some_iff _ w).2 (congrFun hb first), hp⟩, fun i => ?_⟩
    exact (congrFun hb _).trans (congrFun hb first).symm

variable (N : Fin A → Network D P bits) (place : P → EuclideanSpace ℝ (Fin D))
variable (hball : ∀ u, ‖place u‖ ≤ 1) (p : Fin A → ℕ) (first : P) (T : ∀ a, (N a).Tables K)
variable (y : (network N place hball j p).Assignment) (x : Ports (fun u => j * bits u))

/-- Evaluating the actual terminal table agrees with the sparse record whenever
its selector, external bundle and compact feeders address those physical ports. -/
theorem terminal_read_record (u : P) (bank : ℕ → Bool) (s original : Port)
    (compact : Fin A → Port) (boxes : List (List Factor))
    (hs : selector bank s = (assignmentEquiv N place hball j p y).1 u)
    (hf : feeders p bank compact = fun a i => (assignmentEquiv N place hball j p y).2.1 a i u)
    (hx : external (j := j) (b := bits u) bank original = x u) :
    (network N place hball j p).read (tables N place hball j p first T) y x (.inr (.inl u)) =
      if (terminalRecord j (bits u) p s original compact).Valid boxes bank then 1 else 0 := by
  change (if terminalTest p ((assignmentEquiv N place hball j p y).1 u)
      (fun a i => (assignmentEquiv N place hball j p y).2.1 a i u) (x u) then 1 else 0) = _
  rw [← hs, ← hf, ← hx]
  rw [terminalRecord, Record.Valid, terminal_record_iff]

/-- Evaluating the actual origin table agrees with its sparse row list when
the origin reads the same selector bundles at its physical spokes. -/
theorem origin_read_records (bank : ℕ → Bool) (spokes : P → Port) (boxes : List (List Factor))
    (hs : (fun u => selector bank (spokes u)) = (assignmentEquiv N place hball j p y).1) :
    (network N place hball j p).read (tables N place hball j p first T) y x (.inl ()) =
      if ∀ r ∈ originRecords j p first spokes, r.Valid boxes bank then 1 else 0 := by
  change (if originTest first p (assignmentEquiv N place hball j p y).1 then 1 else 0) = _
  rw [← hs]
  have h := origin_records_iff bank j p first spokes boxes
  by_cases ho : originTest (j := j) first p (fun u => selector bank (spokes u))
  · rw [ite_eq_left ho, ite_eq_left (h.mpr ho)]
  · rw [ite_eq_right ho, ite_eq_right (mt h.mp ho)]

end Crossing.Profile.Cell

end BorderVNP
end Computability
end OAI
