import OAI.ThreeFlat.Diagonal.HistoryContraction
import OAI.ThreeFlat.RAM.HistoryNodeDirectory

namespace OAI
/-! # Chronological parent records from the actual history placement maps -/

namespace ThreeFlat.Diagonal.HistoryContraction.Plan

open RAM.HistoryNodeDirectory

variable {F : Type*} [CommSemiring F] {S : Shape}

/-- Each site occupies one compact directory row in the local stage order. -/
def numNodes : {S : Shape} → (P : Plan F S) → P.History → ℕ
  | S,.done _,_ => Fintype.card S.Site
  | S,.step _ next,h => Fintype.card S.Site+(next h.1).numNodes h.2

variable (sites : ∀ X : Shape, Fin (Fintype.card X.Site) ≃ X.Site)

def firstIndex : {S : Shape} → (P : Plan F S) → (h : P.History) → S.Site → Fin (P.numNodes h)
  | S,.done _,_,v => (sites S).symm v
  | S,.step _ next,h,v => ((sites S).symm v).castAdd ((next h.1).numNodes h.2)

private def prepend {c n : ℕ} (later : Chronology n) (enter : Fin c → Fin n) : Chronology (c+n) where
  firstFinal := c+later.firstFinal
  bounded := Nat.add_le_add_left later.bounded _
  parent := Fin.append (fun i => Fin.natAdd c (enter i)) (fun i => Fin.natAdd c (later.parent i))
  later := by
    intro i
    refine Fin.addCases (fun u => ?_) (fun u => ?_) i
    · intro _
      simp only [Fin.val_castAdd,Fin.append_left,Fin.val_natAdd]
      have := u.isLt
      omega
    · simp only [Fin.val_natAdd,Fin.append_right,Nat.add_lt_add_iff_left]
      exact later.later u

private theorem root_right {c n : ℕ} (later : Chronology n) (enter : Fin c → Fin n) (j : Fin n) :
    (prepend later enter).root (Fin.natAdd c j) = later.root j := by
  induction j using Chronology.root.induct later with
  | case1 j yes ih =>
    conv_lhs => rw [Chronology.root]
    conv_rhs => rw [Chronology.root]
    simp only [prepend,Fin.val_natAdd,Nat.add_lt_add_iff_left,yes,Fin.append_right]
    exact ih
  | case2 j no =>
    conv_lhs => rw [Chronology.root]
    conv_rhs => rw [Chronology.root]
    simp only [prepend,Fin.val_natAdd,Nat.add_lt_add_iff_left,no,dite_false,Nat.add_sub_add_left]

private theorem root_left {c n : ℕ} (later : Chronology n) (enter : Fin c → Fin n) (j : Fin c) :
    (prepend later enter).root (j.castAdd n) = later.root (enter j) := by
  have earlier : j.val < c+later.firstFinal := by have := j.isLt; omega
  rw [Chronology.root]
  simp only [prepend,Fin.val_castAdd,earlier,Fin.append_left]
  exact root_right later enter _

/-- A genuine history provides dense compact node IDs. The old record's
parent is precisely `R.owner` in the next chronological stage. -/
def chronology : {S : Shape} → (P : Plan F S) → (h : P.History) → Chronology (P.numNodes h)
  | _,.done _,_ => ⟨0,Nat.zero_le _,id,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  | S,.step R next,h => prepend (chronology (next h.1) h.2) (fun j => (next h.1).firstIndex sites h.2 (R.owner h.1 (sites S j)))

theorem root_destination (P : Plan F S) (h : P.History) (v : S.Site) :
    (P.chronology sites h).root (P.firstIndex sites h v) = ((sites (P.finish h)).symm (P.destination h v)).val := by
  induction P with
  | done S =>
    rw [Chronology.root]
    simp [chronology,finish,firstIndex,destination]; rfl
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    refine (root_left ((next t).chronology sites h)
      (fun j => (next t).firstIndex sites h (R.owner t (sites _ j))) ((sites _).symm v)).trans ?_
    rw [Equiv.apply_symm_apply]
    exact ih t h (R.owner t v)

end ThreeFlat.Diagonal.HistoryContraction.Plan

end OAI
