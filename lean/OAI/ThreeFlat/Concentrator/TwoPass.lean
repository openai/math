import OAI.ThreeFlat.Concentrator.Greedy
import OAI.ThreeFlat.Concentrator.ReserveAssignment
import OAI.ThreeFlat.Concentrator.Halving

namespace OAI
/-! # Combining the greedy and reserve assignments -/

namespace ThreeFlat.Concentrator

namespace Greedy

variable {L R Z : Type*} [DecidableEq L] [DecidableEq R]
variable {N : L → List R} {xs : List L} {F : Finset R}
variable {report : L → Option R} (ok : Valid N report xs F)

private def destination (reserve : (run N xs F).missed ↪ Z) (x : xs.toFinset) : R ⊕ Z :=
  if h : x.val ∈ (run N xs F).missed then .inr (reserve ⟨x.val, h⟩)
  else
    .inl ((report x.val).get (Option.isSome_iff_ne_none.mpr (fun eq =>
      h (((valid_iff_result ok x.val).2).2 ⟨List.mem_toFinset.mp x.property, eq⟩))))

private theorem destination_spec (reserve : (run N xs F).missed ↪ Z) (x : xs.toFinset) :
    match destination ok reserve x with
    | .inl r => (x.val, r) ∈ (run N xs F).matched
    | .inr z => ∃ hx : x.val ∈ (run N xs F).missed, reserve ⟨x.val, hx⟩ = z := by
  by_cases hx : x.val ∈ (run N xs F).missed
  · simp only [destination, dite_eq_left hx]
    exact ⟨hx, trivial⟩
  · simp only [destination, dite_eq_right hx]
    apply ((valid_iff_result ok x.val).1 _).2
    exact ⟨List.mem_toFinset.mp x.property, (Option.some_get _).symm⟩

/-- Combining an accepted first pass with an injective assignment of its missed
requests assigns every active request to a distinct slot. -/
def combine (reserve : (run N xs F).missed ↪ Z) : xs.toFinset ↪ R ⊕ Z where
  toFun := destination ok reserve
  inj' := by
    intro x y h
    have hx := destination_spec ok reserve x
    have hy := destination_spec ok reserve y
    rw [h] at hx
    cases hd : destination ok reserve y with
    | inl r =>
      rw [hd] at hx hy
      have e := List.inj_on_of_nodup_map (run_invariants N xs F).distinct_rights hx hy rfl
      exact Subtype.ext (congrArg Prod.fst e)
    | inr z =>
      rw [hd] at hx hy
      obtain ⟨hx, he⟩ := hx
      obtain ⟨hy, he'⟩ := hy
      exact Subtype.ext (congrArg (fun z : (run N xs F).missed => (z : L))
        (reserve.injective (he.trans he'.symm)))

theorem combine_spec (reserve : (run N xs F).missed ↪ Z) (x : xs.toFinset) :
    match combine ok reserve x with
    | .inl r => r ∈ F ∧ r ∈ N x.val
    | .inr z => ∃ hx : x.val ∈ (run N xs F).missed, reserve ⟨x.val, hx⟩ = z := by
  have h := destination_spec ok reserve x
  change (match destination ok reserve x with
    | .inl r => r ∈ F ∧ r ∈ N x.val
    | .inr z => ∃ hx : x.val ∈ (run N xs F).missed, reserve ⟨x.val, hx⟩ = z)
  cases hd : destination ok reserve x with
  | inl r =>
    rw [hd] at h
    have inv := run_invariants N xs F
    exact ⟨inv.used_free _ h, inv.used_neighbor _ h⟩
  | inr z => simpa only [hd] using h

end Greedy

section Certificates

variable {L R V : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq V]

/-- A request enters the reserve iff it is active and reports no first-pass match. -/
def reportedMissed (xs : List L) (f : L → Option R) : Finset L :=
  xs.toFinset.filter fun x => (f x).isNone

theorem reportedMissed_eq {N : L → List R} {xs : List L} {F : Finset R} {f : L → Option R}
    (ok : Greedy.Valid N f xs F) : reportedMissed xs f = (Greedy.run N xs F).missed := by
  ext x
  simpa [reportedMissed, Option.isNone_iff_eq_none] using ((Greedy.valid_iff_result ok x).2).symm

/-- Both stages verify their reports locally. Reserve nodes read the first-pass
reports on their incident active requests and the labels at the opposite ends. -/
def Accepted (N : L → List R) (G : ReserveGraph L V) (xs : List L) (F : Finset R)
    (slots cap : ℕ) (certificate : (L → Option R) × (V → ℕ)) : Prop :=
  Greedy.PaddedLocalValid N certificate.1 xs F ∧
    G.ValidLabels slots (reportedMissed xs certificate.1) cap certificate.2

theorem existsUnique_accepted (N : L → List R) (G : ReserveGraph L V) (xs : List L)
    (F : Finset R) (slots cap : ℕ) (hd : xs.Nodup) :
    ∃! certificate, Accepted N G xs F slots cap certificate := by
  obtain ⟨f, hf, uniqF⟩ := Greedy.existsUnique_paddedLocalValid N xs F hd
  obtain ⟨label, hl, uniqL⟩ := G.existsUnique_validLabels slots (reportedMissed xs f) cap
  refine ⟨(f, label), ⟨hf, hl⟩, ?_⟩
  rintro ⟨f', label'⟩ ⟨hf', hl'⟩
  have he : f' = f := uniqF f' hf'
  subst f'
  exact Prod.ext rfl (uniqL label' hl')

end Certificates

variable {L R V : Type*} [LinearOrder L] [DecidableEq R] [DecidableEq V] [Fintype V]

/-- The two mixing bounds and a legal mask give an injection into the two public
slot banks. A greedy match uses a listed candidate and a reserve match uses
one of the edge's two endpoints. -/
theorem two_pass_matching_of_residual (N : L → List R) (G : ReserveGraph L V) (xs : List L)
    (all : Finset L) (F : Finset R) (threshold slots cap : ℕ) (hd : xs.Nodup)
    (active : ∀ x ∈ xs, x ∈ all)
    (small : (Greedy.run N xs F).missed.card < threshold)
    (reserveMix : ∀ H : Finset V, (slots + 1) * H.card ≤ 2 * threshold →
      4 * (G.internalEdges all H).card ≤ (slots + 1) * H.card)
    (time : threshold ≤ 2 ^ cap) :
    ∃ assign : xs.toFinset ↪ R ⊕ (V × Fin slots), ∀ x,
      match assign x with
      | .inl r => r ∈ F ∧ r ∈ N x.val
      | .inr (v, _) => v = G.src x.val ∨ v = G.dst x.val := by
  let A := (Greedy.run N xs F).missed
  have sub : A ⊆ all := fun x hx => active x ((Greedy.run_invariants N xs F).missed_subset x hx)
  have finished := G.finished_of_sparse_mixing sub slots (fun H hH =>
    reserveMix H (hH.trans (Nat.mul_le_mul_left 2 small.le))) (small.trans_le time)
  let label := G.departure slots A cap
  let reserve := G.assignment A slots cap label (G.validLabels_departure slots A cap) finished
  obtain ⟨report, ok⟩ := Greedy.exists_valid N xs F hd
  refine ⟨Greedy.combine ok reserve, fun x => ?_⟩
  have h := Greedy.combine_spec ok reserve x
  cases he : Greedy.combine ok reserve x with
  | inl r => simpa only [he] using h
  | inr z =>
    rw [he] at h
    obtain ⟨hx, rfl⟩ := h
    change G.owner label x.val = G.src x.val ∨ G.owner label x.val = G.dst x.val
    unfold ReserveGraph.owner
    split <;> simp

end ThreeFlat.Concentrator

end OAI
