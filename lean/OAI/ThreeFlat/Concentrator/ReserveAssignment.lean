import OAI.ThreeFlat.Concentrator.Peeling
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Assigning peeled requests to reserve slots

An edge leaves at the earlier departure of its two endpoints, with the source
winning a tie. Its local slot is its index in the ordered list of requests
at the winning vertex at that round.
-/

namespace ThreeFlat.Concentrator.ReserveGraph

variable {E V : Type*} [LinearOrder E] [DecidableEq V]
variable (G : ReserveGraph E V)

def owner (label : V → ℕ) (e : E) : V :=
  if label (G.src e) ≤ label (G.dst e) then G.src e else G.dst e

omit [LinearOrder E] [DecidableEq V] in
private theorem owner_time_le (label : V → ℕ) (e : E) :
    label (G.owner label e) ≤ label (G.src e) ∧ label (G.owner label e) ≤ label (G.dst e) := by
  unfold owner
  split <;> omega

def batch (A : Finset E) (label : V → ℕ) (v : V) : Finset E :=
  G.incident (G.reportedLive A label (label v)) v

omit [LinearOrder E] in
private theorem mem_owner_batch {A : Finset E} (label : V → ℕ) {e : E} (he : e ∈ A) :
    e ∈ G.batch A label (G.owner label e) := by
  have ht := G.owner_time_le label e
  simp only [batch, incident, reportedLive, Finset.mem_filter]
  exact ⟨⟨he, ht⟩, by unfold owner; split <;> simp⟩

omit [LinearOrder E] in
private theorem batch_card_le {A : Finset E} {slots cap : ℕ} {label : V → ℕ}
    (ok : G.ValidLabels slots A cap label) (doneAtCap : G.live slots A cap = ∅) (v : V) :
    (G.batch A label v).card ≤ slots := by
  rcases lt_or_eq_of_le (ok.1 v) with ht | hcap
  · exact (ok.2 v _ ht).mp le_rfl
  · have h := G.live_eq_reported slots A cap (le_refl cap)
    rw [← ok.eq_departure G slots A cap, doneAtCap] at h
    simp [batch, hcap, ← h, incident]

/-- The ordered slots determined by valid reports form a matching of all
active requests. The endpoint and local slot depend only on the reports
needed to reconstruct that endpoint's incident requests. -/
noncomputable def assignment (A : Finset E) (slots cap : ℕ) (label : V → ℕ)
    (ok : G.ValidLabels slots A cap label) (doneAtCap : G.live slots A cap = ∅) :
    A ↪ V × Fin slots := by
  let pos (v : V) : G.batch A label v ↪ Fin slots :=
    ((G.batch A label v).orderIsoOfFin rfl).symm.toEquiv.toEmbedding.trans
      (Fin.castLEEmb (G.batch_card_le ok doneAtCap v))
  have same_edge {v u : V} (a : G.batch A label v) (b : G.batch A label u)
      (hv : v = u) (hi : pos v a = pos u b) : a.val = b.val := by
    subst u
    exact congrArg Subtype.val ((pos v).injective hi)
  exact
    { toFun := fun e => (G.owner label e, pos _ ⟨e, G.mem_owner_batch label e.property⟩)
      inj' := by
        rintro ⟨e, he⟩ ⟨f, hf⟩ h
        exact Subtype.ext (same_edge ⟨e, G.mem_owner_batch label he⟩
          ⟨f, G.mem_owner_batch label hf⟩ (congrArg Prod.fst h) (congrArg Prod.snd h)) }

@[simp] theorem assignment_fst (A : Finset E) (slots cap : ℕ) (label : V → ℕ)
    (ok : G.ValidLabels slots A cap label) (doneAtCap : G.live slots A cap = ∅) (e : A) :
    (G.assignment A slots cap label ok doneAtCap e).1 = G.owner label e := rfl

end ThreeFlat.Concentrator.ReserveGraph

end OAI
