import OAI.Computability.VPVNP.PermanentEquality
import OAI.Computability.VPVNP.PermanentRings
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The cycle-cover graph for exact-one clauses

For each occurrence `g` there are three internal vertices. Its first port meets the
arc of the variable ring corresponding to the satisfying literal. Its second port
meets the loop of its clause. Separate occurrence gadgets distinguish all parallel
clause loops. One unmarked row on each ring carries the weight of a true assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

/-- Vertices outside the equality gadgets, consisting of variable-ring rows and clause
vertices. -/
abbrev Exterior (k m c : ℕ) := RingRow k m ⊕ Fin c
/-- The three internal vertices of each literal occurrence's equality gadget. -/
abbrev Interior (m : ℕ) := Fin m × Fin 3
/-- The full index set of the permanent matrix, including the equality gadgets, rings, and
clauses. -/
abbrev Vertex (k m c : ℕ) := Interior m ⊕ Exterior k m c

variable {k m c : ℕ} (occ : Fin m → Fin k × Fin c × Bool)

/-- The ring row assigned to an occurrence, on the ring of that occurrence's variable. -/
def markedPosition (g : Fin m) : RingRow k m := ((occ g).1, ⟨g.val, by omega⟩)

/-- The marked arc exists only on the ring of the occurrence's variable and only in
its satisfying direction. -/
def markedPort (u : RingRow k m) (choice : Bool) : Option (Fin m) :=
  if h : u.2.val < m then
    let g : Fin m := ⟨u.2.val, h⟩
    if (occ g).1 = u.1 ∧ choice = (occ g).2.2 then some g else none
  else none

theorem markedPort_eq_some (u : RingRow k m) (a : Bool) (g : Fin m) :
    markedPort occ u a = some g ↔ u = markedPosition occ g ∧ a = (occ g).2.2 := by
  rcases u with ⟨v, j⟩
  by_cases h : j.val < m
  · let z : Fin m := ⟨j.val, h⟩
    simp only [markedPort, h, dite_true]
    change (if (occ z).1 = v ∧ a = (occ z).2.2 then some z else none) = some g ↔ _
    split_ifs with hz
    · constructor
      · rintro hg
        obtain rfl := Option.some.inj hg
        exact ⟨Prod.ext hz.1.symm (Fin.ext rfl), hz.2⟩
      · rintro ⟨hpos, _⟩
        congr 1
        exact Fin.ext (congrArg (fun u : RingRow k m => u.2.val) hpos)
    · simp
      intro hpos hbit
      have he : z = g := Fin.ext (congrArg (fun u : RingRow k m => u.2.val) hpos)
      exact hz ⟨he ▸ (congrArg Prod.fst hpos).symm, he ▸ hbit⟩
  · simp [markedPort, h]
    intro hpos _
    have := congrArg (fun u : RingRow k m => u.2.val) hpos
    change j.val = g.val at this
    omega

/-- Destination of a ring arc, before the gadget's internal rows are expanded. -/
def ringEntry (u : RingRow k m) (a : Bool) : Vertex k m c :=
  (markedPort occ u a).elim (.inr (.inl (ringTarget u a))) (fun g => .inl (g, 0))

/-- The exterior ring vertex reached when an occurrence gadget takes the satisfying ring
direction. -/
def ringExit (g : Fin m) : Exterior k m c := .inl (ringTarget (markedPosition occ g) (occ g).2.2)

/-- The clause vertex connected to the outgoing clause port of this occurrence. -/
def clauseExit (g : Fin m) : Exterior k m c := .inr (occ g).2.1

/-- A true ring direction uses a variable label only on the dedicated row `m`. -/
def ringLabel {F : Type*} [One F] (u : RingRow k m) (a : Bool) : Fin k ⊕ F :=
  if a = true ∧ u.2.val = m then .inl u.1 else .inr 1

/-- Evaluate a ring arc at the supplied weights. Only the true direction on the dedicated row
`m` contributes the variable weight. -/
def ringWeight {R : Type*} [One R] (w : Fin k → R) (u : RingRow k m) (a : Bool) : R :=
  (ringLabel u a).elim w id

/-- The two ring arcs have distinct endpoints, including at a marked occurrence. -/
theorem ringEntry_ne (u : RingRow k m) : ringEntry occ u false ≠ ringEntry occ u true := by
  intro he
  cases h₀ : markedPort occ u false with
  | none =>
    cases h₁ : markedPort occ u true with
    | none =>
      simp [ringEntry, h₀, h₁, ringTarget] at he
      have hz : (0 : Fin (m + 2)) = 1 := add_left_cancel (a := u.2)
        (by simpa using congrArg Prod.snd he)
      exact zero_ne_one hz
    | some g => simp [ringEntry, h₀, h₁] at he
  | some g =>
    cases h₁ : markedPort occ u true with
    | none => simp [ringEntry, h₀, h₁] at he
    | some z =>
      have eq : g = z := by simpa [ringEntry, h₀, h₁] using he
      subst z
      have ha := (markedPort_eq_some occ _ _ _).mp h₀
      have hb := (markedPort_eq_some occ _ _ _).mp h₁
      exact Bool.false_ne_true (ha.2.trans hb.2.symm)

/-- Every adjacency entry is a single variable or a single scalar. -/
def graphLabels {F : Type*} [CommRing F] (b : F) : Vertex k m c → Vertex k m c → Fin k ⊕ F
  | .inl (g, i), .inl (h, j) => .inr (if g = h then equalityMatrix b i j else 0)
  | .inl (g, i), .inr v => .inr (if (i = 0 ∧ v = ringExit occ g) ∨
      (i = 1 ∧ v = clauseExit occ g) then 1 else 0)
  | .inr (.inl u), v => if v = ringEntry occ u false then ringLabel u false else
      if v = ringEntry occ u true then ringLabel u true else .inr 0
  | .inr (.inr a), .inl (g, j) => .inr (if (occ g).2.1 = a ∧ j = 1 then 1 else 0)
  | .inr (.inr _), .inr _ => .inr 0

/-- The matrix obtained by evaluating all arc labels of the permanent gadget at the specified
weights and equality-gadget parameter. -/
def graphMatrix {R : Type*} [CommRing R] (w : Fin k → R) (b : R) : Matrix (Vertex k m c) (Vertex k m c) R :=
  fun u v => (graphLabels occ b u v).elim w id

end PermanentReduction

end VPVNP
end Computability
end OAI
