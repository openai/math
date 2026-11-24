import OAI.Computability.VPVNP.RankCoordinateSelect
import OAI.Computability.VPVNP.RankCoordinateCramer
import OAI.Computability.VPVNP.RankCoordinateBanks
import OAI.Computability.VPVNP.RankCoordinateSubmatrix
import OAI.Computability.VPVNP.RankCoordinateReplacement

/-! # Physical coefficient readers for the two Cramer minors

One bank supplies each greedy selector and a third supplies the underlying
scalar reader. A target-row read uses the same selected column as an
ordinary entry. The numerator stores its replacement ordinal separately
from these three banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate

open RAMTape BurstRAM Dispatch UniversalCountStack Cursor

/-- Stack addresses for the greedy selector's controller words and its prefix-rank workspace. -/
abbrev Select.Side (K : Type) := PrefixWorkspace.Port (PrefixPort K)

namespace SelectedMinor

/-- Disjoint stack addresses for the row selector, column selector, and underlying scalar
reader. -/
abbrev Host (K R : Type) := ThreeBanks.Host (Select.Side K) (Select.Side K) R
/-- Stack addresses for the selected submatrix's two saved indices and its three reader banks. -/
abbrev Work (K R : Type) := Submatrix.Work (Host K R)

variable {K R : Type} [Fintype K] [DecidableEq K] [DecidableEq R] {p e n m w v d B S A E Ba : ℕ} {c : SliceArithmetic.Vector p e}

/-- Compare the prefix scan addresses used when locating a pivot for a Cramer minor. -/
local instance : DecidableEq (PrefixPort K) := inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))
/-- Decide equality of template, work, and scratch addresses within a pivot selector. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) := fun a b => PrefixWorkspace.instDecidableEqAux a b
/-- Decide equality of controller and workspace stack addresses in a greedy selector bank. -/
local instance : DecidableEq (Select.Side K) := inferInstanceAs (DecidableEq (PrefixWords.Port (PrefixWorkspace.Aux (PrefixPort K))))
/-- Compare stack addresses by bank and then by their row-selector, column-selector, or
scalar-reader label. -/
local instance : DecidableEq (Host K R) := inferInstanceAs (DecidableEq (Select.Side K ⊕ (Select.Side K ⊕ R)))
/-- Decide equality of the two saved-index addresses and the auxiliary bank addresses for a
minor read. -/
local instance : DecidableEq (Work K R) := fun a b => Submatrix.instDecidableEqWork a b

/-- Idle state of an ordinal selector, with its rank template configured for a matrix with
`cols` columns. -/
def selectorBank (w v cols : ℕ) (c : SliceArithmetic.Vector p e) (base : Stacks K) :=
  OrdinalABI.idle (w := w) (Select.side w v cols c base)

/-- The row and column selectors are in their designated idle states and the scalar reader
satisfies its readiness predicate. -/
def Ready (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (base : Stacks K) (ready : Stacks R → Prop) :=
  ThreeBanks.Ready (· = selectorBank w v m c base) (· = selectorBank w v n c base) ready

/-- Combine idle selectors for the matrix and its transpose with the supplied scalar-reader
stacks. -/
def initial (w v n m : ℕ) (c : SliceArithmetic.Vector p e) (base : Stacks K) (raw : Stacks R) : Stacks (Host K R) :=
  Sum.elim (selectorBank w v m c base) (Sum.elim (selectorBank w v n c base) raw)

omit [Fintype K] [DecidableEq R] in
theorem initial_ready {ready : Stacks R → Prop} (base : Stacks K) (raw : Stacks R) (hr : ready raw) :
    Ready w v n m c base ready (initial w v n m c base raw) := ⟨rfl,rfl,hr⟩

/-- Pivot selection is always performed on the original relation matrix.
The final scalar can be read from that matrix or from a powered target row. -/
def restrictEntry (read : FiniteRoutine (MacaulayRead.Port K)) (entry : FiniteRoutine (MacaulayRead.Port R)) : FiniteRoutine (MacaulayRead.Port (Work K R)) :=
  Submatrix.minorRead (OrdinalRead.onAux ThreeBanks.left (OrdinalABI.machine (Select.rows read)))
    (OrdinalRead.onAux ThreeBanks.middle (OrdinalABI.machine (Select.columns read)))
    (MacaulayRead.onAux ThreeBanks.right entry)

/-- Uniform stack-length bound for selector calls, scalar reads, and the stored input banks. -/
def space (K : Type) [Fintype K] (d w v e A S : ℕ) :=
  max (Select.scanSpace K d w v e A S + OrdinalABI.overhead w) (max S A)

/-- Step bound for selecting an original row and column, reading their scalar entry, and
handling the two address words. -/
def time (K : Type) [Fintype K] (n m d w v e B A S E : ℕ) :=
  (Select.scanTime K n d w v e B A S+OrdinalABI.overhead w) +
  (Select.scanTime K m d w v e B A S+OrdinalABI.overhead w) + E + 2*(w+1)


omit [DecidableEq R] in
theorem ready_length {pivot : Stacks K → Prop} {ready : Stacks R → Prop} (base : Stacks K) (hr : pivot base)
    (ha : ∀ a, pivot a → ∀ k, (a k).length ≤ A) (he : ∀ a, ready a → ∀ k, (a k).length ≤ A) (hn : n < 2^w) (hm : m < 2^w)
    (s : Stacks (Host K R)) (h : Ready w v n m c base ready s) (k : Host K R) :
    (s k).length ≤ space K d w v e A S := by
  let cap := space K d w v e A S
  have hsc : Select.scanSpace K d w v e A S ≤ cap := (Nat.le_add_right _ _).trans (le_max_left ..)
  have hw : w ≤ cap := ((Nat.le_add_right _ _).trans (le_max_left ..)).trans hsc
  have hi (cols : ℕ) (hcols : cols < 2^w) (a : Stacks (Select.Side K))
      (heq : a = selectorBank w v cols c base) (j : Select.Side K) : (a j).length ≤ cap := by
    subst a
    cases j with
    | inl j => exact (RegisterTable.bank_length_le Fin.elim0 0 _ j).trans hw
    | inr j => exact (Select.side_length c base hr ha hcols j).trans hsc
  exact ThreeBanks.length_le (hi m hm) (hi n hn)
    (fun b hb j => (he b hb j).trans ((le_max_right ..).trans (le_max_right ..))) h k

omit [DecidableEq R] in
theorem den_ready_length {pivot : Stacks K → Prop} {ready : Stacks R → Prop} (base : Stacks K) (hr : pivot base)
    (ha : ∀ a, pivot a → ∀ k, (a k).length ≤ A) (he : ∀ a, ready a → ∀ k, (a k).length ≤ A) (hn : n < 2^w) (hm : m < 2^w)
    (s : Stacks (Work K R)) (h : Submatrix.Ready (Ready w v n m c base ready) s) (k : Work K R) :
    (s k).length ≤ space K d w v e A S := by
  obtain ⟨b, hb, rfl⟩ := h
  cases k with
  | row | col => exact Nat.zero_le _
  | aux k => exact ready_length base hr ha he hn hm _ hb k

omit [DecidableEq R] in
theorem num_ready_length {pivot : Stacks K → Prop} {ready : Stacks R → Prop} (base : Stacks K) (hr : pivot base)
    (ha : ∀ a, pivot a → ∀ k, (a k).length ≤ A) (he : ∀ a, ready a → ∀ k, (a k).length ≤ A) (hn : n < 2^w) (hm : m < 2^w) (i : ℕ)
    (s : Stacks (Replacement.Work (Work K R)))
    (h : Replacement.Ready w i (Submatrix.Ready (Ready w v n m c base ready)) s) (k : Replacement.Work (Work K R)) :
    (s k).length ≤ space K d w v e A S := by
  obtain ⟨b, hb, rfl⟩ := h
  have hw : w ≤ space K d w v e A S :=
    (((Nat.le_add_right w _).trans (le_max_left ..)).trans (Nat.le_add_right (Select.scanSpace K d w v e A S) _)).trans (le_max_left ..)
  rcases k with j | k
  · cases j with
    | pub j => exact j.elim0
    | reg j => fin_cases j <;> simp [Replacement.workBank, length_digits]; exact hw
    | persistent => exact (length_wordBits (0 : Word w)).le.trans hw
    | work j => exact Nat.zero_le _
    | logPort j => cases j <;> exact Nat.zero_le _
  · exact den_ready_length base hr ha he hn hm _ hb k

private theorem width_le (hw : gramWidth d ≤ w) : d ≤ w := by
  have h : 2*d+7 ≤ (2*d+7)*(max widthFactor control.wordFactor+1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold gramWidth at hw
  omega

variable [Fact p.Prime] [NeZero e] [Fact (Irreducible (SliceArithmetic.modulus c))]
    [DecidableEq (AdjoinRoot (SliceArithmetic.modulus c))]

/-- Column indices that form the nonsingular coordinate minor of the interpreted matrix's
greedy row basis. -/
abbrev cols (M : Matrix (Fin n) (Fin m) (Scalar c)) :=
  let L := M.map (Scalar.interpretation c)
  coordinateColumns (greedyRowBasis L) (greedyRowBasis_fullRank L)

/-- Square submatrix of `D` at the greedy row and column indices chosen from the interpreted
pivot matrix `M`. -/
abbrev selected (M D : Matrix (Fin n) (Fin m) (Scalar c)) :=
  D.submatrix (greedyRowIndex (M.map (Scalar.interpretation c))) (cols M)

/-- Complete denominator or selected-target entry reader from the physical
base scalar queries. Both true pivot selectors use the same live matrix. -/
theorem restrictEntry_correctSpace (M D : Matrix (Fin n) (Fin m) (Scalar c))
    (read : FiniteRoutine (MacaulayRead.Port K)) (entry : FiniteRoutine (MacaulayRead.Port R)) {pivot : Stacks K → Prop} {ready : Stacks R → Prop}
    (hc : MacaulayRead.CorrectSpace read M w v B S pivot)
    (he : MacaulayRead.CorrectSpace entry D w v E S ready)
    (ha : ∀ s, pivot s → ∀ k, (s k).length ≤ A) (hb : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (hrSize : n+n+(n+m)*n+m+8 < 2^d) (hcSize : m+m+(m+n)*m+n+8 < 2^d)
    (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : pivot base) :
    MacaulayRead.CorrectSpace (restrictEntry read entry) (selected M D) w v (time K n m d w v e B A S E)
      (space K d w v e A S) (Submatrix.Ready (Ready w v n m c base ready)) := by
  let cap := space K d w v e A S
  have hp : 2^d ≤ 2^w := Nat.pow_le_pow_right (by decide) (width_le hw)
  have safe := ready_length (d := d) (S := S) (c := c) (v := v) base hr ha hb
    (by omega : n < 2^w) (by omega : m < 2^w)
  have rows := Select.row_correctSpace M read hc ha hrSize hw hv base hr
  have columns := Select.column_correctSpace M read hc ha hcSize hw hv base hr
  have rs := rows.onAux (ready := Ready w v n m c base ready) (A := cap) ThreeBanks.left ThreeBanks.left_injective
    (fun _ h => ThreeBanks.project_left h) (fun _ _ h ho => ThreeBanks.preserve_left h ho) (fun s h k _ => safe s h k)
  have cs := columns.onAux (ready := Ready w v n m c base ready) (A := cap) ThreeBanks.middle ThreeBanks.middle_injective
    (fun _ h => ThreeBanks.project_middle h) (fun _ _ h ho => ThreeBanks.preserve_middle h ho) (fun s h k _ => safe s h k)
  have es := he.onAux (ready := Ready w v n m c base ready) (A := cap) ThreeBanks.right ThreeBanks.right_injective
    (fun _ h => ThreeBanks.project_right h) (fun _ _ h ho => ThreeBanks.preserve_right h ho) (fun s h k _ => safe s h k)
  rw [max_eq_right (show Select.scanSpace K d w v e A S+OrdinalABI.overhead w ≤ cap from le_max_left ..)] at rs cs
  rw [max_eq_right (show S ≤ cap from (le_max_left ..).trans (le_max_right ..))] at es
  exact Submatrix.correctSpace rs cs es

/-- Read a Cramer numerator entry, using the target at the selected column on the replacement
row and the ordinary minor entry elsewhere. -/
def numerator (read : FiniteRoutine (MacaulayRead.Port K)) (ordinary target : FiniteRoutine (MacaulayRead.Port R)) :=
  Replacement.numerator (restrictEntry read ordinary) (restrictEntry read target)

/-- The native numerator has the chosen dense row replaced by the target,
evaluated at exactly the selected original columns. -/
theorem numerator_correctSpace (M : Matrix (Fin n) (Fin m) (Scalar c)) (T : Fin m → Scalar c)
    (read : FiniteRoutine (MacaulayRead.Port K)) (ordinary target : FiniteRoutine (MacaulayRead.Port R)) {pivot : Stacks K → Prop} {ready : Stacks R → Prop}
    (hc : MacaulayRead.CorrectSpace read M w v B S pivot)
    (ho : MacaulayRead.CorrectSpace ordinary M w v Ba S ready)
    (ht : MacaulayRead.CorrectSpace target (fun _ j => T j : Matrix (Fin n) (Fin m) _) w v E S ready)
    (ha : ∀ s, pivot s → ∀ k, (s k).length ≤ A) (hb : ∀ s, ready s → ∀ k, (s k).length ≤ A)
    (hrSize : n+n+(n+m)*n+m+8 < 2^d) (hcSize : m+m+(m+n)*m+n+8 < 2^d)
    (hw : gramWidth d ≤ w) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (base : Stacks K) (hr : pivot base) (i : Fin (rankQuery (M.map (Scalar.interpretation c)))) :
    MacaulayRead.CorrectSpace (numerator read ordinary target) ((selected M M).updateRow i (T ∘ cols M)) w v
      (20*w+10+(max (time K n m d w v e B A S Ba) (time K n m d w v e B A S E)+1))
      (max (space K d w v e A S) (w+(20*w+10)))
      (Replacement.Ready w i (Submatrix.Ready (Ready w v n m c base ready))) := by
  have dn := restrictEntry_correctSpace M M read ordinary hc ho ha hb hrSize hcSize hw hv base hr
  have tg := restrictEntry_correctSpace M _ read target hc ht ha hb hrSize hcSize hw hv base hr
  have hn : n ≤ 2^w := (show n ≤ 2^d by omega).trans (Nat.pow_le_pow_right (by decide) (width_le hw))
  apply Replacement.correctSpace dn tg i
  rw [rankQuery_eq]
  exact (by simpa using (M.map (Scalar.interpretation c)).rank_le_card_height : _ ≤ n).trans hn

/-- The interpreted denominator matrix is Appendix D.2's canonical square minor. -/
theorem selected_map (M : Matrix (Fin n) (Fin m) (Scalar c)) :
    (selected M M).map (Scalar.interpretation c) =
      (greedyRowBasis (M.map (Scalar.interpretation c))).submatrix id (cols M) := rfl

theorem numerator_map (M : Matrix (Fin n) (Fin m) (Scalar c)) (T : Fin m → Scalar c)
    (i : Fin (rankQuery (M.map (Scalar.interpretation c)))) :
    ((selected M M).updateRow i (T ∘ cols M)).map (Scalar.interpretation c) =
      replacedMinor (greedyRowBasis (M.map (Scalar.interpretation c))) (cols M) ((Scalar.interpretation c) ∘ T) i := by
  ext j k
  by_cases h : j = i
  · subst j; simp [replacedMinor, Matrix.map_apply]
  · simp only [Matrix.map_apply, replacedMinor, Matrix.updateRow_ne h]
    rfl

end SelectedMinor
end RankQuery.Stack.Coordinate

end

end VPVNP
end Computability
end OAI
