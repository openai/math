import OAI.ThreeFlat.Diagonal.TickChronology
import OAI.ThreeFlat.Diagonal.TickBitRule

namespace OAI
/-! # Bitwise guards on the diagonal tick's shared auxiliary register

The marker occupies bit zero. The persistent fields hold the compression
history and the final wire bits. The active pair field follows them. All
remaining bits must be zero. Epochs can select different active pair lengths.
-/

namespace ThreeFlat.Diagonal.TickAuxiliary
open TickChronology

/-- Absolute exclusive ends of the persistent fields and current group pairs. -/
structure Layout (a : ℕ) where
  wiresEnd : ℕ
  pairsEnd : ℕ
  marker : 0 < wiresEnd
  ordered : wiresEnd ≤ pairsEnd
  fits : pairsEnd ≤ a

def markerRule : Phase → Rule
  | .opening => .zeroOne | .closing => .oneZero | _ => .bothOne

def historyRule : Phase → Rule
  | .opening => .oldZero | .closing => .newZero | _ => .same

def pairRule : Phase → Rule
  | .opening | .closing => .bothZero
  | .propose => .oldZero | .clear => .newZero | _ => .same

def Layout.rule {a : ℕ} (L : Layout a) (p : Phase) (run : Bool) (i : ℕ) : Rule :=
  if !run then .bothZero else if i = 0 then markerRule p else
  if i < L.wiresEnd then historyRule p else if i < L.pairsEnd then pairRule p else .bothZero

def Layout.accepts {a : ℕ} (L : Layout a) (p : Phase) (run : Bool) (old new : Fin a → Bool) : Prop :=
  ∀ i, (L.rule p run i.val).holds (old i) (new i)

theorem identity_iff {a : ℕ} (L : Layout a) (p : Phase) (old new : Fin a → Bool) :
    L.accepts p false old new ↔ old = (fun _ => false) ∧ new = (fun _ => false) := by
  simp [Layout.accepts, Layout.rule, Rule.holds, funext_iff, forall_and]

/-- The four ranges suffice to validate the full physical register. -/
theorem split_run {a : ℕ} (L : Layout a) (p : Phase) (old new : Fin a → Bool) :
    L.accepts p true old new ↔
      (∀ i : Fin a, i.val = 0 → (markerRule p).holds (old i) (new i)) ∧
      (∀ i : Fin a, i.val ≠ 0 → i.val < L.wiresEnd → (historyRule p).holds (old i) (new i)) ∧
      (∀ i : Fin a, L.wiresEnd ≤ i.val → i.val < L.pairsEnd → (pairRule p).holds (old i) (new i)) ∧
      (∀ i : Fin a, L.pairsEnd ≤ i.val → old i = false ∧ new i = false) := by
  have h₁ := L.marker
  have h₂ := L.ordered
  constructor
  · intro accepted
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i h
      simpa [Layout.rule,h] using accepted i
    · intro i h h'
      simpa [Layout.rule,h,h'] using accepted i
    · intro i h h'
      simpa [Layout.rule, show i.val ≠ 0 by omega, not_lt.mpr h, h'] using accepted i
    · intro i h
      simpa [Layout.rule, show i.val ≠ 0 by omega, show ¬ i.val < L.wiresEnd by omega,
        not_lt.mpr h, Rule.holds] using accepted i
  · rintro ⟨hm, hw, hp, hz⟩ i
    by_cases hi : i.val = 0
    · simpa [Layout.rule, hi] using hm i hi
    · by_cases hx : i.val < L.wiresEnd
      · simpa [Layout.rule,hi,hx] using hw i hi hx
      · by_cases hy : i.val < L.pairsEnd
        · simpa [Layout.rule,hi,hx,hy] using hp i (Nat.le_of_not_gt hx) hy
        · simpa [Layout.rule,hi,hx,hy,Rule.holds] using hz i (Nat.le_of_not_gt hy)

/-- Exactly one of the two adjacent marker bits determines the chosen branch. -/
def branch {a : ℕ} (L : Layout a) (p : Phase) (old new : Fin a → Bool) : Bool :=
  let i : Fin a := ⟨0, lt_of_lt_of_le L.marker (L.ordered.trans L.fits)⟩
  if p = .opening then new i else old i

theorem branch_eq_of_accepts {a : ℕ} (L : Layout a) (p : Phase)
    (run : Bool) (old new : Fin a → Bool) (h : L.accepts p run old new) :
    branch L p old new = run := by
  let i : Fin a := ⟨0, lt_of_lt_of_le L.marker (L.ordered.trans L.fits)⟩
  have hm := h i
  cases run <;> cases p <;>
    simp_all [branch, i, Layout.rule, markerRule, Rule.holds]

end ThreeFlat.Diagonal.TickAuxiliary

end OAI
