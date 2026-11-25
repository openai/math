import OAI.Computability.BorderVNP.CellGuessBlock

/-!
# Disjoint exhaustive auxiliary flag storage

A cell puts the finite flag slabs consecutively at the top of its value stack.
The row-major equivalence occupies exactly the sum of the slab sizes. Every
guessed bit belongs to a checked slab, including when some slab sizes vanish.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.AuxSlabs

variable {n : ℕ}

/-- Starting stack offset of a slab, after all preceding slabs in row order. -/
def offset (size : Fin n → ℕ) (r : Fin n) : ℕ :=
  ∑ i : Fin r.val, size (Fin.castLE r.isLt.le i)

/-- The slab view of a single full physical flag vector. -/
def view (size : Fin n → ℕ) (x : Fin (∑ r, size r) → Bool) (r : Fin n) (i : Fin (size r)) : Bool :=
  x (finSigmaFinEquiv ⟨r,i⟩)

/-- Pack all prescribed slab values into the unique physical bit vector. -/
def pack (size : Fin n → ℕ) (values : ∀ r, Fin (size r) → Bool) (k : Fin (∑ r, size r)) : Bool :=
  let q := (finSigmaFinEquiv (n := size)).symm k
  values q.1 q.2

/-- Natural-address reads from the prepended physical stack agree with the slab view. -/
theorem lookup_slab (size : Fin n → ℕ) (x : Fin (∑ r, size r) → Bool) (tail : List Bool)
    (r : Fin n) (i : Fin (size r)) :
    lookup (List.ofFn x ++ tail) (offset size r + i.val) = view size x r i := by
  rw [show offset size r + i.val = (finSigmaFinEquiv (n := size) ⟨r,i⟩).val from
    (finSigmaFinEquiv_apply (n := size) ⟨r,i⟩).symm]
  exact lookup_prefix x tail _

/-- All rows of the packed vector return exactly their stipulated flags. -/
theorem view_pack (size : Fin n → ℕ) (values : ∀ r, Fin (size r) → Bool) (r : Fin n) :
    view size (pack size values) r = values r := by
  funext i
  exact congrArg (fun (q : Σ r, Fin (size r)) => values q.1 q.2)
    ((finSigmaFinEquiv (n := size)).symm_apply_apply ⟨r, i⟩)

/-- Checking every slab fixes the entire vector, with no unexamined padding slots. -/
theorem valid_iff (size : Fin n → ℕ) (canonical : ∀ r, Fin (size r) → Bool)
    (valid : Fin n → Prop) (check : ∀ r, (Fin (size r) → Bool) → Prop)
    (hcheck : ∀ r y, check r y ↔ valid r ∧ y = canonical r)
    (x : Fin (∑ r, size r) → Bool) :
    (∀ r, check r (view size x r)) ↔ (∀ r, valid r) ∧ x = pack size canonical := by
  constructor
  · intro h
    refine ⟨fun r => ((hcheck r _).1 (h r)).1, ?_⟩
    funext k
    obtain ⟨⟨r,i⟩, rfl⟩ := (finSigmaFinEquiv (n := size)).surjective k
    change view size x r i = view size (pack size canonical) r i
    rw [view_pack, ((hcheck r _).1 (h r)).2]
  · rintro ⟨h, rfl⟩ r
    exact (hcheck r _).2 ⟨h r, view_pack size canonical r⟩

open scoped Classical in
/-- The signed (or more general additive) sum over all slab guesses retains
one continuation value exactly when every original row is valid. -/
theorem sum_checked {M : Type*} [AddCommMonoid M] (size : Fin n → ℕ)
    (canonical : ∀ r, Fin (size r) → Bool) (valid : Fin n → Prop)
    (check : ∀ r, (Fin (size r) → Bool) → Prop)
    (hcheck : ∀ r y, check r y ↔ valid r ∧ y = canonical r)
    (weight : (Fin (∑ r, size r) → Bool) → M) :
    (∑ x, if ∀ r, check r (view size x r) then weight x else 0) =
      if ∀ r, valid r then weight (pack size canonical) else 0 := by
  classical
  by_cases h : ∀ r, valid r <;> simp [valid_iff size canonical valid check hcheck, h]

end CellSparse.AuxSlabs

namespace CellMacro

open scoped Classical

/-- Execute the actual guesses, checker, and deterministic flag disposal before
an arbitrary signed continuation. A forced vector contributes exactly once. -/
theorem value_uniqueBlock (n : ℕ) (canonical : Fin n → Bool) (test : Prop) (check : List Op)
    (ops : List Op) (f : Flags) (bank : List Bool)
    (hcheck : ∀ (x : Fin n → Bool) (tail : List Op),
      value (check ++ tail) f (List.ofFn x ++ bank) =
        value tail ⟨f.ok && decide (test ∧ x = canonical), f.minus⟩ (List.ofFn x ++ bank)) :
    value (List.replicate n .guess ++ check ++ discardBlock n ++ ops) f bank =
      if test then value ops f bank else 0 := by
  classical
  simp only [List.append_assoc]
  rw [value_guessBlock]
  have step (x : Fin n → Bool) :
      value (check ++ (discardBlock n ++ ops)) f (List.ofFn x ++ bank) =
        if test ∧ x = canonical then value ops f bank else 0 := by
    rw [hcheck]
    have hd := value_discardBlock (List.ofFn x) bank ops
      (⟨f.ok && decide (test ∧ x = canonical), f.minus⟩ : Flags)
    rw [List.length_ofFn] at hd
    rw [hd]
    by_cases h : test ∧ x = canonical
    · cases f
      simp [h]
    · simp [h, value_failed]
  simp_rw [step]
  by_cases h : test <;> simp [h]

/-- Sum over the actual internal wire guesses, followed by the exhaustive auxiliary
flag block. A successful continuation sees the original wire bank and its supplied
external suffix. Every rejected wire assignment contributes zero. -/
theorem value_wireAndAux (wires aux : ℕ)
    (canonical : (Fin wires → Bool) → Fin aux → Bool) (test : (Fin wires → Bool) → Prop)
    (check ops : List Op) (f : Flags) (external : List Bool)
    (hcheck : ∀ (w : Fin wires → Bool) (x : Fin aux → Bool) (tail : List Op),
      value (check ++ tail) f (List.ofFn x ++ (List.ofFn w ++ external)) =
        value tail ⟨f.ok && decide (test w ∧ x = canonical w), f.minus⟩
          (List.ofFn x ++ (List.ofFn w ++ external))) :
    value (List.replicate wires .guess ++ (List.replicate aux .guess ++ check ++ discardBlock aux ++ ops))
        f external =
      ∑ w, if test w then value ops f (List.ofFn w ++ external) else 0 := by
  rw [value_guessBlock]
  exact Finset.sum_congr rfl fun w _ =>
    value_uniqueBlock aux (canonical w) (test w) check ops f (List.ofFn w ++ external) (hcheck w)

end CellMacro

end BorderVNP
end Computability
end OAI
