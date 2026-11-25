import OAI.ThreeFlat.Routing.SpillReserveProposal
import OAI.ThreeFlat.Routing.SpillReserveSelectorNetwork

namespace OAI
/-! # Correctness of reserve output selectors on the canonical peeling trace -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {E V : Type*} [Fintype E] [Fintype V] [LinearOrder E] [DecidableEq V]
variable (G : ReserveGraph E V)

/-- The report combines the initial active-edge mask with the subsequent peeling trace. -/
def reserveReports (slots cap : ℕ) (A : Finset E) : E ⊕ Round E V cap → Bool :=
  Sum.elim (fun e => decide (e ∈ A)) (reserveTrace G slots cap A)

omit [Fintype E] [Fintype V] in
private theorem read_before (slots cap : ℕ) (A : Finset E) (e : E) (t : Fin cap) :
    reserveReports G slots cap A (reserveBefore e t) = decide (e ∈ G.live slots A t.val) := by
  by_cases ht : t.val = 0
  · simp [reserveReports,reserveBefore,ht,ReserveGraph.live]
  · simp [reserveReports,reserveBefore,ht,reserveTrace,Nat.sub_add_cancel (by omega : 1 ≤ t.val)]

omit [Fintype E] [Fintype V] in
private theorem read_vertex (slots cap : ℕ) (A : Finset E) (v : V) (t : Fin cap) :
    reserveReports G slots cap A (.inr (.inl (v,t))) =
      decide ((G.incident (G.live slots A t.val) v).card ≤ slots) := by
  simp [reserveReports,reserveTrace,G.departure_le_iff slots A cap t.isLt]

omit [Fintype V] in
private theorem count_smaller (S : Finset E) (v : V) (e : E) :
    ((Finset.univ : Finset (Adjacent G v)).filter (fun i => i.val < e ∧ i.val ∈ S)).card =
      ((G.incident S v).filter (fun f => f < e)).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    obtain ⟨lt,hin⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hin,i.property⟩,lt⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro i hi
    obtain ⟨hi,lt⟩ := Finset.mem_filter.mp hi
    obtain ⟨hin,hadj⟩ := Finset.mem_filter.mp hi
    exact ⟨⟨i,hadj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt,hin⟩,rfl⟩

omit [Fintype V] in
/-- The directed selector convention counts a loop once, at the source endpoint. -/
theorem reserveProposal_trace_iff (slots cap : ℕ) (A : Finset E) (e : E)
    (side : Bool) (j : Fin slots) (t : Fin cap) :
    reserveProposal G (reserveReports G slots cap A) (e,side,j) t = true ↔
      roundProposes G slots A t.val e (reserveEnd G (e,side,j)) j ∧
        (side = true → G.src e ≠ G.dst e) := by
  rw [reserveProposal_eq]
  simp only [read_before,read_vertex,decide_eq_true_eq,count_smaller, Bool.and_eq_true]
  cases side <;> by_cases eq : G.src e = G.dst e
  all_goals simp [reserveEnd,roundProposes,eq,Ne.symm,not_le] <;> aesop

omit [Fintype V] in
theorem reservePick_iff_assignment (slots cap : ℕ) (A : Finset E)
    (done : G.live slots A cap = ∅) (e : E) (side : Bool) (j : Fin slots) :
    reservePick G (reserveReports G slots cap A) (e,side,j) = true ↔
      (∃ he : e ∈ A, G.assignment A slots cap (G.departure slots A cap)
        (G.validLabels_departure slots A cap) done ⟨e,he⟩ = (reserveEnd G (e,side,j),j)) ∧
      (side = true → G.src e ≠ G.dst e) := by
  rw [← exists_roundProposes_iff_assignment, reservePick, decide_eq_true_eq]
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨a,b⟩ := (reserveProposal_trace_iff G slots cap A e side j t).mp ht
    exact ⟨⟨t.val,t.isLt,a⟩,b⟩
  · rintro ⟨⟨t,ht,a⟩,b⟩
    exact ⟨⟨t,ht⟩,(reserveProposal_trace_iff G slots cap A e side j ⟨t,ht⟩).mpr ⟨a,b⟩⟩

omit [Fintype V] in
/-- A request has a selected destination exactly when it starts active and peels by the deadline. -/
theorem reservePick_iff_removed (slots cap : ℕ) (A : Finset E) (e : E) :
    (∃ side : Bool, ∃ j : Fin slots, reservePick G (reserveReports G slots cap A) (e,side,j) = true) ↔
      e ∈ A ∧ e ∉ G.live slots A cap := by
  rw [← exists_proposal_iff_removed G slots cap A e]
  constructor
  · rintro ⟨side,j,ok⟩
    obtain ⟨t,ht⟩ := (of_decide_eq_true ok : ∃ t : Fin cap, _)
    exact ⟨t,t.isLt,_,j,((reserveProposal_trace_iff G slots cap A e side j t).mp ht).1⟩
  · rintro ⟨t,ht,v,j,hv⟩
    have claim (side : Bool) (hside : reserveEnd G (e,side,j) = v)
        (ok : side = true → G.src e ≠ G.dst e) :
        reservePick G (reserveReports G slots cap A) (e,side,j) = true := by
      apply decide_eq_true
      refine ⟨⟨t,ht⟩, (reserveProposal_trace_iff G slots cap A e side j ⟨t,ht⟩).mpr ?_⟩
      exact ⟨hside.symm ▸ hv,ok⟩
    by_cases hs : G.src e = v
    · exact ⟨false,j,claim false (by simpa [reserveEnd] using hs) (by simp)⟩
    · obtain ⟨_,hchoose,_⟩ := hv
      rcases hchoose with h | h
      · exact (hs h.1.symm).elim
      · exact ⟨true,j,claim true (by simpa [reserveEnd] using h.1.symm) (fun _ he => hs (he.trans h.1.symm))⟩

/-- The final live wire exposes a still-active unmatched request. With no rounds,
the initial active-edge wire carries this bit. -/
def reserveUnassigned {cap : ℕ} (a : E ⊕ Round E V cap → Bool) (e : E) : Bool :=
  if h : cap = 0 then a (.inl e) else a (.inr (.inr (e, ⟨cap-1,by omega⟩)))

omit [Fintype V] in
theorem reserveUnassigned_trace (slots cap : ℕ) (A : Finset E) (e : E) :
    reserveUnassigned (reserveReports G slots cap A) e =
      decide (e ∈ A ∧ ¬∃ side : Bool, ∃ j : Fin slots, reservePick G (reserveReports G slots cap A) (e,side,j) = true) := by
  have sub : G.live slots A cap ⊆ A := G.live_antitone slots A (Nat.zero_le cap)
  have heq : reserveUnassigned (reserveReports G slots cap A) e = decide (e ∈ G.live slots A cap) := by
    by_cases h : cap = 0
    · simp [reserveUnassigned,reserveReports,h,ReserveGraph.live]
    · simp [reserveUnassigned,reserveReports,h,reserveTrace,Nat.sub_add_cancel (by omega : 1 ≤ cap)]
  rw [heq]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, reservePick_iff_removed]
  exact ⟨fun h => ⟨sub h,fun q => q.2 h⟩,fun ⟨h,hn⟩ => Classical.byContradiction fun h' => hn ⟨h,h'⟩⟩

end ThreeFlat.Routing.Spill

end
end OAI
