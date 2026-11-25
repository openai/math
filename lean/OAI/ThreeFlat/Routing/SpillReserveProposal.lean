import OAI.ThreeFlat.Concentrator.ReserveAssignment
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Local proposals for the peeled reserve graph -/

namespace ThreeFlat.Routing.Spill

open Concentrator

variable {E V : Type*} [LinearOrder E] [DecidableEq V] (G : ReserveGraph E V)

/-- At round `t`, a live request uses its first eligible endpoint, with the
source winning ties. Its slot counts the smaller live requests at this vertex. -/
def roundProposes (slots : ℕ) (A : Finset E) (t : ℕ) (e : E) (v : V) (j : Fin slots) : Prop :=
  e ∈ G.live slots A t ∧
    ((v = G.src e ∧ (G.incident (G.live slots A t) (G.src e)).card ≤ slots) ∨
     (v = G.dst e ∧ slots < (G.incident (G.live slots A t) (G.src e)).card ∧
       (G.incident (G.live slots A t) (G.dst e)).card ≤ slots)) ∧
    ((G.incident (G.live slots A t) v).filter (fun f => f < e)).card = j.val

private theorem orderIndex_eq_card (s : Finset E) (x : s) :
    ((s.orderIsoOfFin rfl).symm x).val = (s.filter (fun y => y < x.val)).card := by
  let f := s.orderIsoOfFin rfl
  change (f.symm x).val = _
  rw [← Fin.card_Iio]
  apply Finset.card_bij (fun i _ => (f i).val)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨(f i).property, ?_⟩
    change f i < x
    exact (f.lt_iff_lt.mpr (Finset.mem_Iio.mp hi)).trans_eq (f.apply_symm_apply x)
  · intro i _ j _ heq
    exact f.injective (Subtype.ext heq)
  · intro y hy
    let z : s := ⟨y,(Finset.mem_filter.mp hy).1⟩
    exact ⟨f.symm z, Finset.mem_Iio.mpr
      (f.symm.lt_iff_lt.mpr (show z < x from (Finset.mem_filter.mp hy).2)),
      congrArg Subtype.val (f.apply_symm_apply z)⟩

omit [LinearOrder E] [DecidableEq V] in
private theorem winner_le (D : V → ℕ) (e : E) :
    D (G.owner D e) ≤ D (G.src e) ∧ D (G.owner D e) ≤ D (G.dst e) := by
  unfold ReserveGraph.owner
  split <;> omega

private theorem assignment_position (A : Finset E) (slots cap : ℕ) (D : V → ℕ)
    (ok : G.ValidLabels slots A cap D) (done : G.live slots A cap = ∅) (e : A) :
    (G.assignment A slots cap D ok done e).2.val =
      ((G.batch A D (G.owner D e.val)).filter (fun f => f < e.val)).card := by
  let s := G.batch A D (G.owner D e.val)
  have he : e.val ∈ s := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨e.property, winner_le G D e.val⟩, ?_⟩
    unfold ReserveGraph.owner
    split <;> simp
  exact orderIndex_eq_card s ⟨e.val, he⟩

omit [LinearOrder E] in
private theorem endpoint_at_round (D : V → ℕ) (e : E) (v : V) (t : ℕ)
    (hs : t ≤ D (G.src e)) (hd : t ≤ D (G.dst e)) :
    ((v = G.src e ∧ D (G.src e) ≤ t) ∨
      (v = G.dst e ∧ t < D (G.src e) ∧ D (G.dst e) ≤ t)) ↔
      v = G.owner D e ∧ t = D v := by
  unfold ReserveGraph.owner
  by_cases h : D (G.src e) ≤ D (G.dst e)
  · rw [ite_eq_left h]
    constructor
    · rintro (⟨rfl, h'⟩ | ⟨rfl, h', h''⟩)
      · exact ⟨rfl, le_antisymm hs h'⟩
      · omega
    · rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl,le_rfl⟩
  · rw [ite_eq_right h]
    constructor
    · rintro (⟨rfl,h'⟩ | ⟨rfl,h',h''⟩)
      · omega
      · exact ⟨rfl,le_antisymm hd h''⟩
    · rintro ⟨rfl,rfl⟩
      exact Or.inr ⟨rfl,lt_of_not_ge h,le_rfl⟩

theorem exists_roundProposes_iff_assignment (slots cap : ℕ) (A : Finset E)
    (done : G.live slots A cap = ∅) (e : E) (v : V) (j : Fin slots) :
    (∃ t < cap, roundProposes G slots A t e v j) ↔ ∃ he : e ∈ A,
      G.assignment A slots cap (G.departure slots A cap)
        (G.validLabels_departure slots A cap) done ⟨e,he⟩ = (v,j) := by
  let D := G.departure slots A cap
  have live_iff (t : ℕ) (ht : t ≤ cap) :
      e ∈ G.live slots A t ↔ e ∈ A ∧ t ≤ D (G.src e) ∧ t ≤ D (G.dst e) := by
    rw [G.live_eq_reported slots A cap ht]
    exact Finset.mem_filter
  have endpoints (t : ℕ) (ht : t < cap) (hs : t ≤ D (G.src e)) (hd : t ≤ D (G.dst e)) :
      ((v = G.src e ∧ (G.incident (G.live slots A t) (G.src e)).card ≤ slots) ∨
       (v = G.dst e ∧ slots < (G.incident (G.live slots A t) (G.src e)).card ∧
          (G.incident (G.live slots A t) (G.dst e)).card ≤ slots)) ↔
        v = G.owner D e ∧ t = D v := by
    have hel (u : V) := G.departure_le_iff slots A cap ht u
    rw [← hel, ← hel, show slots < (G.incident (G.live slots A t) (G.src e)).card ↔
      t < D (G.src e) by simpa only [not_le] using not_congr (hel (G.src e)).symm]
    exact endpoint_at_round G D e v t hs hd
  constructor
  · rintro ⟨t, ht, alive, choose, pos⟩
    obtain ⟨he,hs,hd⟩ := (live_iff t ht.le).mp alive
    obtain ⟨hv, htime⟩ := (endpoints t ht hs hd).mp choose
    refine ⟨he, Prod.ext hv.symm ?_⟩
    apply Fin.ext
    change t = G.departure slots A cap v at htime
    rw [assignment_position G, ← hv, ReserveGraph.batch, ← htime, ← G.live_eq_reported slots A cap ht.le]
    exact pos
  · rintro ⟨he, hassign⟩
    have hv : v = G.owner D e := (congrArg Prod.fst hassign).symm
    obtain ⟨hs,hd⟩ := winner_le G D e
    rw [← hv] at hs hd
    have ht : D v < cap := by
      by_contra! hge
      have live := (live_iff cap le_rfl).mpr ⟨he,hge.trans hs,hge.trans hd⟩
      simp [done] at live
    refine ⟨D v, ht, (live_iff _ ht.le).mpr ⟨he,hs,hd⟩,
      (endpoints _ ht hs hd).mpr ⟨hv,rfl⟩, ?_⟩
    have pos := congrArg (fun z : V × Fin slots => z.2.val) hassign
    change (G.assignment A slots cap D _ done ⟨e,he⟩).2.val = j.val at pos
    rw [assignment_position G, ← hv, ReserveGraph.batch, ← G.live_eq_reported slots A cap ht.le] at pos
    exact pos

/-- On any activity mask, the edges lacking a proposal by the deadline
are precisely the surviving active edges. -/
theorem exists_proposal_iff_removed (slots cap : ℕ) (A : Finset E) (e : E) :
    (∃ t < cap, ∃ v j, roundProposes G slots A t e v j) ↔
      e ∈ A ∧ e ∉ G.live slots A cap := by
  constructor
  · rintro ⟨t, ht, v, j, hLive, hchoose, -⟩
    have started : e ∈ G.live slots A 0 := G.live_antitone slots A (Nat.zero_le t) hLive
    refine ⟨started, fun hend => ?_⟩
    have hnext : e ∈ G.live slots A (t+1) := G.live_antitone slots A ht hend
    obtain ⟨_,hs,hd⟩ := Finset.mem_filter.mp hnext
    rcases hchoose with ⟨_, hv⟩ | ⟨_, _, hv⟩
    · exact (not_lt_of_ge hv) hs
    · exact (not_lt_of_ge hv) hd
  · rintro ⟨he, hend⟩
    have drop (k : ℕ) (hk : e ∉ G.live slots A k) :
        ∃ t < k, e ∈ G.live slots A t ∧ e ∉ G.live slots A (t + 1) := by
      induction k with
      | zero => exact (hk he).elim
      | succ k ih =>
        by_cases h : e ∈ G.live slots A k
        · exact ⟨k, k.lt_succ_self, h, hk⟩
        · obtain ⟨t, ht, prev, next⟩ := ih h
          exact ⟨t, ht.trans (Nat.lt_succ_self _), prev, next⟩
    obtain ⟨t, ht, hLive, hnext⟩ := drop cap hend
    let live := G.live slots A t
    have position (v : V) (hv : G.src e = v ∨ G.dst e = v)
        (small : (G.incident live v).card ≤ slots) :
        ∃ j : Fin slots, ((G.incident live v).filter (fun f => f < e)).card = j.val := by
      have hi : e ∈ G.incident live v := Finset.mem_filter.mpr ⟨hLive, hv⟩
      have smaller : (G.incident live v).filter (fun f => f < e) ⊂ G.incident live v :=
        Finset.filter_ssubset.mpr ⟨e, hi, lt_irrefl e⟩
      exact ⟨⟨_, (Finset.card_lt_card smaller).trans_le small⟩, rfl⟩
    by_cases hs : (G.incident live (G.src e)).card ≤ slots
    · obtain ⟨j,hj⟩ := position _ (Or.inl rfl) hs
      exact ⟨t,ht,_,j,hLive,Or.inl ⟨rfl,hs⟩,hj⟩
    · have hs' := lt_of_not_ge hs
      have hd : (G.incident live (G.dst e)).card ≤ slots := by
        by_contra! h
        exact hnext (Finset.mem_filter.mpr ⟨hLive,hs',h⟩)
      obtain ⟨j,hj⟩ := position _ (Or.inr rfl) hd
      exact ⟨t,ht,_,j,hLive,Or.inr ⟨rfl,hs',hd⟩,hj⟩

end ThreeFlat.Routing.Spill

end OAI
