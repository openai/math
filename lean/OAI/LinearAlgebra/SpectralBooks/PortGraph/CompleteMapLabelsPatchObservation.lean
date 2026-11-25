import OAI.LinearAlgebra.SpectralBooks.PortGraph.CompleteMapLabelsViews

/-! # One-step records throughout the ball observed by a map label -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PortGraph.MapLabels

open PlanarPatch PlanarCertSize

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)

/-- Adjacency of distinct vertices is witnessed by a departure and an arrival slot. -/
theorem adj_iff_step {v w : V} :
    (underlying M.graph.tail M.graph.head).Adj v w ↔
      v ≠ w ∧ ∃ i j, M.graph.portStep M.slots v i = some (w,j) := by
  constructor
  · rintro ⟨hne,e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨hne, _, _, portStep_port _ _ (v := M.graph.tail e) ⟨(e,false),rfl⟩⟩
    · exact ⟨hne, _, _, portStep_port _ _ (v := M.graph.head e) ⟨(e,true),rfl⟩⟩
  · rintro ⟨hne,i,j,h⟩
    by_cases hp : ∃ p, M.slots v p = i
    · obtain ⟨⟨⟨e,s⟩,rfl⟩,rfl⟩ := hp
      rw [portStep_port] at h
      have hh := congrArg Prod.fst (Option.some.inj h)
      cases s
      · exact ⟨hne, e, Or.inl ⟨rfl,hh⟩⟩
      · exact ⟨hne, e, Or.inr ⟨hh,rfl⟩⟩
    · rw [portStep_missing _ _ _ _ hp] at h
      contradiction

variable {A : Type*}

/-- Keep the centered one-step view of every vertex reached in at most `r` steps. -/
def patchRows : (r : ℕ) → PortView A (r+1) → Finset (PortView A 1)
  | 0, z => {z}
  | r+1, z => by
      classical
      exact insert (PortView.shorten (show 1 ≤ r+1+1 by omega) z)
        (Finset.univ.biUnion fun i : Fin 4 =>
          match z.2 i with
          | none => ∅
          | some (_,s) => patchRows r s)

theorem patchRows_actual (b : V → A) (r : ℕ) (v : V) (s : PortView A 1) :
    s ∈ patchRows r (PortView.actual M.slots b (r+1) v) ↔
      ∃ w, (underlying M.graph.tail M.graph.head).edist v w ≤ r ∧
        PortView.actual M.slots b 1 w = s := by
  classical
  let G := underlying M.graph.tail M.graph.head
  induction r generalizing v with
  | zero =>
    simp [patchRows, eq_comm (a := s)]
  | succ r ih =>
    have mem : s ∈ patchRows (r+1) (PortView.actual M.slots b (r+1+1) v) ↔
        PortView.actual M.slots b 1 v = s ∨
          ∃ w i j, M.graph.portStep M.slots v i = some (w,j) ∧
            s ∈ patchRows r (PortView.actual M.slots b (r+1) w) := by
      rw [patchRows, Finset.mem_insert, PortView.shorten_actual]
      apply or_congr eq_comm
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩
        change s ∈ (match (M.graph.portStep M.slots v i).map (fun a => (a.2, PortView.actual M.slots b (r+1) a.1)) with
          | none => ∅ | some (_,z) => patchRows r z) at hi
        cases h : M.graph.portStep M.slots v i with
        | none => simp [h] at hi
        | some p => exact ⟨p.1, i, p.2, h, by simpa [h] using hi⟩
      · rintro ⟨w,i,j,h,hs⟩
        exact ⟨i, by simpa [PortView.actual,h] using hs⟩
    rw [mem]
    constructor
    · rintro (hc | ⟨w,i,j,h,hw⟩)
      · exact ⟨v, by simp, hc⟩
      · obtain ⟨y,hy,hys⟩ := (ih w).mp hw
        have hd : G.edist v w ≤ 1 := SimpleGraph.edist_le_one_iff_adj_or_eq.mpr <| by
          by_cases hv : v = w
          · exact Or.inr hv
          · exact Or.inl ((adj_iff_step M).mpr ⟨hv,i,j,h⟩)
        exact ⟨y, SimpleGraph.edist_triangle.trans
          (by simpa [add_comm] using add_le_add hd hy), hys⟩
    · rintro ⟨y,hy,hys⟩
      have hc : G.Connected := underlying_connected_of_connectedFrom _ _ M.connected
      obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_edist v y
      have hp' : p.length ≤ r+1 := by exact_mod_cast hp.trans_le hy
      cases p with
      | nil => exact Or.inl hys
      | @cons _ w _ a p =>
        obtain ⟨_, i,j,hs⟩ := (adj_iff_step M).mp a
        refine Or.inr ⟨w,i,j,hs,(ih w).mpr ⟨y,p.edist_le.trans ?_,hys⟩⟩
        exact_mod_cast Nat.le_of_succ_le_succ hp'

end PortGraph.MapLabels

end

end SpectralBooks
end LinearAlgebra
end OAI
