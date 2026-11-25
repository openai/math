import OAI.Hierarchy.GraphContractions

namespace OAI
/-! # Finite paths in the graph contraction classification -/

namespace Hierarchy.IncidenceGraph

/-- The edge numbered `i` joins vertices `i` and `i+1` in the path on `n` vertices. -/
def path (n : ℕ) : IncidenceGraph where
  V := Fin n
  E := Fin (n - 1)
  left i := ⟨i.val, by have := i.isLt; omega⟩
  right i := ⟨i.val + 1, by have := i.isLt; omega⟩
  loopless i h := by
    have bad := congrArg Fin.val h
    change i.val = i.val + 1 at bad
    omega

@[simp] theorem path_order (n : ℕ) : Fintype.card (path n).V = n := Fintype.card_fin n

theorem path_incident_cases {n : ℕ} {v : Fin n} (e : (path n).Incident v) :
    e.1.val = v.val ∨ e.1.val + 1 = v.val := by
  rcases e.property with h | h
  · exact Or.inl (congrArg Fin.val h)
  · exact Or.inr (congrArg Fin.val h)

/-- The two possible incident edges are distinguished by whether they start at the vertex. -/
theorem path_degree_le (n : ℕ) (v : (path n).V) : (path n).degree v ≤ 2 := by
  let side : (path n).Incident v → Bool := fun e => decide (e.1.val = v.val)
  have inj : Function.Injective side := by
    intro e f h
    have same : (e.1.val = v.val) ↔ (f.1.val = v.val) := by
      simpa [side] using h
    have he := path_incident_cases e
    have hf := path_incident_cases f
    apply Subtype.ext
    apply Fin.ext
    omega
  simpa [degree] using Fintype.card_le_of_injective side inj

/-- All pairs of vertices lie in the same component, including when the path has just one vertex. -/
theorem path_connected (n : ℕ) (u v : (path n).V) : (path n).Connected u v := by
  let first : Fin n := ⟨0, by have := u.isLt; omega⟩
  have fromFirst (k : ℕ) (hk : k < n) :
      (path n).Connected first ⟨k, hk⟩ ∧ (path n).Connected ⟨k, hk⟩ first := by
    induction k with
    | zero => exact ⟨.refl, .refl⟩
    | succ k ih =>
      let prior : Fin n := ⟨k, by omega⟩
      let edge : Fin (n - 1) := ⟨k, by omega⟩
      obtain ⟨forward, backward⟩ := ih prior.isLt
      exact ⟨forward.tail ⟨edge, Or.inl ⟨rfl, rfl⟩⟩,
        backward.head ⟨edge, Or.inr ⟨rfl, rfl⟩⟩⟩
  exact (fromFirst u.val u.isLt).2.trans (fromFirst v.val v.isLt).1

theorem path_component (n : ℕ) (v : (path n).V) : (path n).component v = Finset.univ := by
  classical
  ext w
  simp [component, path_connected]

@[simp] theorem path_component_card (n : ℕ) (v : (path n).V) :
    ((path n).component v).card = n := by rw [path_component]; exact path_order n

/-- Every tail contains a component larger than any prescribed constant. -/
theorem path_component_growth (b start : ℕ) :
    ∃ n, start ≤ n ∧ ∃ v : (path n).V, b < ((path n).component v).card := by
  let n := max b start + 1
  have hb := le_max_left b start
  have hs := le_max_right b start
  let v : (path n).V := (⟨0, Nat.zero_lt_succ _⟩ : Fin n)
  refine ⟨n, by dsimp [n]; omega, v, ?_⟩
  exact (show b < n by dsimp [n]; omega).trans_eq (path_component_card n v).symm

/-- No constant bounds the component orders of the path family. -/
theorem path_component_unbounded :
    ¬ ∃ b : ℕ, ∀ n (v : (path n).V), ((path n).component v).card ≤ b := by
  rintro ⟨b, bound⟩
  obtain ⟨n, _, v, bigger⟩ := path_component_growth b 0
  exact (bound n v).not_gt bigger

/-- At a cut after the first `k` vertices, only the edge from `k-1` to `k` can cross. -/
theorem path_cutwidth (n : ℕ) : (path n).CutwidthAtMost 1 := by
  classical
  let order : (path n).V ≃ Fin (Fintype.card (path n).V) := finCongr (path_order n).symm
  refine ⟨order, fun k => Finset.card_le_one.2 ?_⟩
  intro e he f hf
  have crossing (i : (path n).E) (hi : i ∈ (path n).cutEdges order k) :
      i.val + 1 = k := by
    have h := (Finset.mem_filter.mp hi).2
    change ¬ (i.val < k ↔ i.val + 1 < k) at h
    omega
  exact Fin.ext (by have := crossing e he; have := crossing f hf; omega)

end Hierarchy.IncidenceGraph

end OAI
