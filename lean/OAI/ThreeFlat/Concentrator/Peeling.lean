import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

namespace OAI
/-! # Local certificates for the reserve matching

A request is a directed edge and can use a slot at either endpoint. Each vertex
has `slots` reserve slots. Vertices with at most that many live requests leave
in the next synchronous round. Parallel edges are distinct requests. A loop
uses one slot at its endpoint.
-/

namespace ThreeFlat.Concentrator

variable {E V : Type*} [DecidableEq V]

/-- The two choices of reserve vertex for each candidate request. -/
structure ReserveGraph (E V : Type*) where
  src : E → V
  dst : E → V

namespace ReserveGraph

variable (G : ReserveGraph E V) (slots : ℕ)

def incident (S : Finset E) (v : V) : Finset E :=
  S.filter fun e => G.src e = v ∨ G.dst e = v

def step (S : Finset E) : Finset E :=
  S.filter fun e => slots < (G.incident S (G.src e)).card ∧
    slots < (G.incident S (G.dst e)).card

def live (A : Finset E) : ℕ → Finset E
  | 0 => A
  | n + 1 => G.step slots (live A n)

theorem live_antitone (A : Finset E) : Antitone (G.live slots A) :=
  antitone_nat_of_succ_le fun _ => Finset.filter_subset _ _

theorem incident_mono {S T : Finset E} (h : S ⊆ T) (v : V) :
    G.incident S v ⊆ G.incident T v :=
  Finset.filter_subset_filter _ h

variable (A : Finset E) (cap : ℕ)

private theorem exists_round (v : V) :
    ∃ t : ℕ, t = cap ∨ (G.incident (G.live slots A t) v).card ≤ slots :=
  ⟨cap, Or.inl rfl⟩

/-- The first eligible round, with `cap` representing no earlier departure. -/
noncomputable def departure (v : V) : ℕ :=
  Nat.find (G.exists_round slots A cap v)

theorem departure_le (v : V) : G.departure slots A cap v ≤ cap :=
  Nat.find_min' (G.exists_round slots A cap v) (Or.inl rfl)

theorem departure_le_iff {t : ℕ} (ht : t < cap) (v : V) :
    G.departure slots A cap v ≤ t ↔ (G.incident (G.live slots A t) v).card ≤ slots := by
  constructor
  · intro h
    have spec := Nat.find_spec (G.exists_round slots A cap v)
    change G.departure slots A cap v = cap ∨
      (G.incident (G.live slots A (G.departure slots A cap v)) v).card ≤ slots at spec
    rcases spec with heq | hd
    · omega
    · exact (Finset.card_le_card (G.incident_mono ((G.live_antitone slots A) h) v)).trans hd
  · intro h
    exact Nat.find_min' (G.exists_round slots A cap v) (Or.inr h)

/-- Live edges reconstructed solely from the two endpoint labels. -/
def reportedLive (label : V → ℕ) (t : ℕ) : Finset E :=
  A.filter fun e => t ≤ label (G.src e) ∧ t ≤ label (G.dst e)

theorem live_eq_reported {t : ℕ} (ht : t ≤ cap) :
    G.live slots A t = G.reportedLive A (G.departure slots A cap) t := by
  induction t with
  | zero => simp [live, reportedLive]
  | succ t ih =>
    have ht' : t < cap := ht
    ext e
    have hp := Finset.ext_iff.mp (ih ht'.le) e
    simp only [reportedLive, Finset.mem_filter] at hp
    simp only [live, step, reportedLive, Finset.mem_filter]
    have hl (v : V) : slots < (G.incident (G.live slots A t) v).card ↔
        t < G.departure slots A cap v := by
      simpa only [not_le] using not_congr (G.departure_le_iff slots A cap ht' v).symm
    rw [hl, hl, hp]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h =>
      ⟨⟨h.1, Nat.le_of_succ_le h.2.1, Nat.le_of_succ_le h.2.2⟩, h.2⟩⟩

/-- A vertex verifies each threshold against the original activity bits and
the labels at the other ends of its incident edges. -/
def ValidLabels (label : V → ℕ) : Prop :=
  (∀ v, label v ≤ cap) ∧ ∀ v t, t < cap →
    (label v ≤ t ↔ (G.incident (G.reportedLive A label t) v).card ≤ slots)

theorem validLabels_departure : G.ValidLabels slots A cap (G.departure slots A cap) := by
  refine ⟨G.departure_le slots A cap, fun v t ht => ?_⟩
  rw [← G.live_eq_reported slots A cap ht.le]
  exact G.departure_le_iff slots A cap ht v

theorem ValidLabels.eq_departure {label : V → ℕ} (h : G.ValidLabels slots A cap label) :
    label = G.departure slots A cap := by
  have same : ∀ t ≤ cap, G.reportedLive A label t = G.live slots A t := by
    intro t ht
    induction t with
    | zero => simp [reportedLive, live]
    | succ t ih =>
      have ht' : t < cap := ht
      have hprev := ih ht'.le
      ext e
      have hp := Finset.ext_iff.mp hprev e
      simp only [reportedLive, Finset.mem_filter] at hp
      simp only [reportedLive, live, step, Finset.mem_filter]
      have hl (v : V) : slots < (G.incident (G.live slots A t) v).card ↔ t < label v := by
        rw [← hprev]
        simpa only [not_le] using not_congr (h.2 v t ht').symm
      rw [hl, hl, ← hp]
      exact ⟨fun h => ⟨⟨h.1, Nat.le_of_succ_le h.2.1, Nat.le_of_succ_le h.2.2⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
  funext v
  have eqs (t : ℕ) (ht : t < cap) : label v ≤ t ↔ G.departure slots A cap v ≤ t := by
    rw [h.2 v t ht, same t ht.le, G.departure_le_iff slots A cap ht v]
  have h₁ := h.1 v
  have h₂ := G.departure_le slots A cap v
  apply le_antisymm
  · by_contra! hlt
    exact (not_le.mpr hlt) ((eqs _ (by omega)).2 le_rfl)
  · by_contra! hlt
    exact (not_le.mpr hlt) ((eqs _ (by omega)).1 le_rfl)

/-- Every activity mask has exactly one locally accepting set of labels. -/
theorem existsUnique_validLabels : ∃! label, G.ValidLabels slots A cap label :=
  ⟨_, G.validLabels_departure slots A cap, fun _ h => h.eq_departure G slots A cap⟩

end ReserveGraph
end ThreeFlat.Concentrator

end OAI
