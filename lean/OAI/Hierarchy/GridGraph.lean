import OAI.Hierarchy.PathWitness

namespace OAI
/-! # Vertices and edges of the finite square grid -/

namespace Hierarchy.SquareGrid

open IncidenceGraph

/-- In each summand the first coordinate selects a line and the second selects a path edge. -/
def graph (n : ℕ) : IncidenceGraph where
  V := Fin n × Fin n
  E := (Fin n × Fin (n-1)) ⊕ (Fin n × Fin (n-1))
  left := Sum.elim (fun e => (e.1, (path n).left e.2)) (fun e => ((path n).left e.2, e.1))
  right := Sum.elim (fun e => (e.1, (path n).right e.2)) (fun e => ((path n).right e.2, e.1))
  loopless := by
    rintro (e | e) h
    · exact (path n).loopless e.2 (congrArg Prod.snd h)
    · exact (path n).loopless e.2 (congrArg Prod.fst h)

@[simp] theorem card_vertices (n : ℕ) : Fintype.card (graph n).V = n^2 := by
  change Fintype.card (Fin n × Fin n) = n^2
  simp [pow_two]

theorem row_adj {k : ℕ} (u : Fin (k+1)) (t : Fin k) :
    (graph (k+1)).Adjacent (u,t.castSucc) (u,t.succ) :=
  ⟨Sum.inl (u,t), Or.inl ⟨rfl,rfl⟩⟩

theorem col_adj {k : ℕ} (u : Fin (k+1)) (t : Fin k) :
    (graph (k+1)).Adjacent (t.castSucc,u) (t.succ,u) :=
  ⟨Sum.inr (u,t), Or.inl ⟨rfl,rfl⟩⟩

/-- Forget the fixed coordinate to identify an incident edge in its row or column. -/
private def project {n : ℕ} (v : (graph n).V) :
    (graph n).Incident v → (path n).Incident v.2 ⊕ (path n).Incident v.1
  | ⟨.inl (_,t), h⟩ => .inl ⟨t, h.imp (congrArg Prod.snd) (congrArg Prod.snd)⟩
  | ⟨.inr (_,t), h⟩ => .inr ⟨t, h.imp (congrArg Prod.fst) (congrArg Prod.fst)⟩

private def liftEdge {n : ℕ} (v : (graph n).V) :
    (path n).Incident v.2 ⊕ (path n).Incident v.1 → (graph n).E :=
  Sum.elim (fun t => .inl (v.1,t.1)) (fun t => .inr (v.2,t.1))

private theorem lift_project {n : ℕ} (v : (graph n).V) (i : (graph n).Incident v) :
    liftEdge v (project v i) = i.1 := by
  rcases i with ⟨⟨u,t⟩ | ⟨u,t⟩,h⟩
  · have hu : u=v.1 := h.elim (congrArg Prod.fst) (congrArg Prod.fst)
    change Sum.inl (v.1,t) = Sum.inl (u,t)
    rw [hu]
  · have hu : u=v.2 := h.elim (congrArg Prod.snd) (congrArg Prod.snd)
    change Sum.inr (v.2,t) = Sum.inr (u,t)
    rw [hu]

theorem degree_le_four (n : ℕ) (v : (graph n).V) : (graph n).degree v ≤ 4 := by
  let : Fintype ((path n).Incident v.1) := incidentFintype (path n) v.1
  let : Fintype ((path n).Incident v.2) := incidentFintype (path n) v.2
  have inj : Function.Injective (project v) := by
    intro e f h
    exact Subtype.ext ((lift_project v e).symm.trans ((congrArg (liftEdge v) h).trans (lift_project v f)))
  have upper := Fintype.card_le_of_injective (project v) inj
  rw [Fintype.card_sum] at upper
  exact upper.trans (Nat.add_le_add (path_degree_le n v.2) (path_degree_le n v.1))

end Hierarchy.SquareGrid

end OAI
