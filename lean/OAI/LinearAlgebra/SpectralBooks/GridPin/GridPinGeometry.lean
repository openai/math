import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarNumberedRotation
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortPinning

/-! # The rooted rectangular grid with numbered ports

Horizontal edges point to the right, and vertical edges point down. At a
crossing the ports appear in left, top, right, bottom order. Each end of
a line has a single port.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace GridPin

open PortGraph

abbrev Vertex (m n : ℕ) := (Fin m × Bool) ⊕ ((Fin n × Bool) ⊕ (Fin m × Fin n))
abbrev Edge (m n : ℕ) := (Fin m × Fin (n+1)) ⊕ (Fin n × Fin (m+1))

variable {m n : ℕ}

abbrev rowEnd (i : Fin m) (b : Bool) : Vertex m n := Sum.inl (i,b)
abbrev colEnd (j : Fin n) (b : Bool) : Vertex m n := Sum.inr (Sum.inl (j,b))
abbrev cell (i : Fin m) (j : Fin n) : Vertex m n := Sum.inr (Sum.inr (i,j))
abbrev hor (i : Fin m) (k : Fin (n+1)) : Edge m n := Sum.inl (i,k)
abbrev ver (j : Fin n) (k : Fin (m+1)) : Edge m n := Sum.inr (j,k)

def graph (m n : ℕ) : PortGraph (Vertex m n) (Edge m n) where
  tail := Sum.elim (fun (i,k) => Fin.cases (rowEnd i false) (cell i) k)
    (fun (j,k) => Fin.cases (colEnd j false) (fun i => cell i j) k)
  head := Sum.elim (fun (i,k) => Fin.lastCases (rowEnd i true) (cell i) k)
    (fun (j,k) => Fin.lastCases (colEnd j true) (fun i => cell i j) k)

abbrev arity : Vertex m n → ℕ
  | .inl _ | .inr (.inl _) => 1
  | .inr (.inr _) => 4

def dart : (v : Vertex m n) → Fin (arity v) → Edge m n × Bool
  | .inl (i,false), _ => (hor i 0,false)
  | .inl (i,true), _ => (hor i (Fin.last n),true)
  | .inr (.inl (j,false)), _ => (ver j 0,false)
  | .inr (.inl (j,true)), _ => (ver j (Fin.last m),true)
  | .inr (.inr (i,j)), r => ![(hor i j.castSucc,true), (ver j i.castSucc,true),
                                (hor i j.succ,false), (ver j i.succ,false)] r

theorem dart_incident (v : Vertex m n) (r : Fin (arity v)) :
    (graph m n).vertex (dart v r).1 (dart v r).2 = v := by
  rcases v with ⟨i, _|_⟩ | (⟨j, _|_⟩ | ⟨i,j⟩)
  all_goals first | rfl | (change Fin 4 at r; fin_cases r <;> simp [dart, PortGraph.vertex, graph]) |
    simp [dart, PortGraph.vertex, graph]

private theorem dart_injective (v : Vertex m n) : Function.Injective (dart v) := by
  rcases v with ⟨i,b⟩ | (⟨j,b⟩ | ⟨i,j⟩)
  · exact fun _ _ _ => Subsingleton.elim _ _
  · exact fun _ _ _ => Subsingleton.elim _ _
  · change Function.Injective (fun r : Fin 4 => dart (cell i j) r)
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [dart]

private theorem dart_surjective (p : Edge m n × Bool) :
    ∃ r, dart ((graph m n).vertex p.1 p.2) r = p := by
  rcases p with ⟨⟨i,k⟩ | ⟨j,k⟩, _|_⟩
  · induction k using Fin.cases with
    | zero => exact ⟨(0 : Fin 1),rfl⟩
    | succ k => exact ⟨(2 : Fin 4),rfl⟩
  · change ∃ r, dart (Fin.lastCases (rowEnd i true) (cell i) k) r = _
    induction k using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact ⟨(0 : Fin 1), rfl⟩
    | cast k => rw [Fin.lastCases_castSucc]; exact ⟨(0 : Fin 4),rfl⟩
  · induction k using Fin.cases with
    | zero => exact ⟨(0 : Fin 1),rfl⟩
    | succ k => exact ⟨(3 : Fin 4),rfl⟩
  · change ∃ r, dart (Fin.lastCases (colEnd j true) (fun i => cell i j) k) r = _
    induction k using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact ⟨(0 : Fin 1), rfl⟩
    | cast k => rw [Fin.lastCases_castSucc]; exact ⟨(1 : Fin 4),rfl⟩

/-- The four crossing ports are explicitly numbered. Unary vertices have number zero. -/
noncomputable def ports (v : Vertex m n) : Fin (arity v) ≃ (graph m n).Port v :=
  Equiv.ofBijective (fun r => ⟨dart v r, dart_incident v r⟩)
    ⟨fun _ _ h => dart_injective v (congrArg Subtype.val h), by
      rintro ⟨p,rfl⟩
      obtain ⟨r,hr⟩ := dart_surjective p
      exact ⟨r, Subtype.ext hr⟩⟩

theorem port_card (v : Vertex m n) : Fintype.card ((graph m n).Port v) = arity v := by
  simpa using Fintype.card_congr (ports v).symm

noncomputable def numbering (m n : ℕ) : (graph m n).Numbering :=
  fun v => (ports v).symm.trans (finCongr (port_card v).symm)

theorem degree_bound (v : Vertex m n) : Fintype.card ((graph m n).Port v) ≤ 4 := by
  rw [port_card]
  rcases v with _ | (_ | _) <;> simp [arity]

theorem vertex_count (m n : ℕ) : Fintype.card (Vertex m n) = m*n + 2*(m+n) := by
  simp [Vertex]
  omega

theorem edge_count (m n : ℕ) : Fintype.card (Edge m n) = m*(n+1) + n*(m+1) := by
  simp [Edge]

@[simp] theorem hor_tail_zero (i : Fin m) :
    (graph m n).tail (hor i 0) = rowEnd i false := rfl
@[simp] theorem hor_tail_succ (i : Fin m) (j : Fin n) :
    (graph m n).tail (hor i j.succ) = cell i j := rfl
@[simp] theorem hor_head_last (i : Fin m) :
    (graph m n).head (hor i (Fin.last n)) = rowEnd i true := by
  simp [graph, hor, Fin.lastCases_last]
@[simp] theorem hor_head_cast (i : Fin m) (j : Fin n) :
    (graph m n).head (hor i j.castSucc) = cell i j := by
  simp [graph, hor, Fin.lastCases_castSucc]
@[simp] theorem ver_tail_zero (j : Fin n) :
    (graph m n).tail (ver j 0) = colEnd j false := rfl
@[simp] theorem ver_tail_succ (j : Fin n) (i : Fin m) :
    (graph m n).tail (ver j i.succ) = cell i j := rfl
@[simp] theorem ver_head_last (j : Fin n) :
    (graph m n).head (ver j (Fin.last m)) = colEnd j true := by
  simp [graph, ver, Fin.lastCases_last]
@[simp] theorem ver_head_cast (j : Fin n) (i : Fin m) :
    (graph m n).head (ver j i.castSucc) = cell i j := by
  simp [graph, ver, Fin.lastCases_castSucc]

private theorem forward (e : Edge m n) :
    (graph m n).Adj ((graph m n).tail e) ((graph m n).head e) :=
  ⟨e, false, rfl, rfl⟩

private theorem backward (e : Edge m n) :
    (graph m n).Adj ((graph m n).head e) ((graph m n).tail e) :=
  ⟨e, true, rfl, rfl⟩

/-- Every grid vertex is reachable from the first crossing when both classes are nonempty. -/
theorem connected (m n : ℕ) : (graph (m+1) (n+1)).ConnectedFrom (cell 0 0) := by
  let G := graph (m+1) (n+1)
  have vert (j : Fin (n+1)) (i : Fin m) : G.Adj (cell i.castSucc j) (cell i.succ j) := by
    have h := forward (ver j i.castSucc.succ)
    rw [ver_tail_succ, Fin.succ_castSucc, ver_head_cast] at h
    exact h
  have horiz (i : Fin (m+1)) (j : Fin n) : G.Adj (cell i j.castSucc) (cell i j.succ) := by
    have h := forward (hor i j.castSucc.succ)
    rw [hor_tail_succ, Fin.succ_castSucc, hor_head_cast] at h
    exact h
  have cross (i : Fin (m+1)) (j : Fin (n+1)) : Relation.ReflTransGen G.Adj (cell 0 0) (cell i j) := by
    have col0 (i : Fin (m+1)) : Relation.ReflTransGen G.Adj (cell 0 0) (cell i 0) :=
      Fin.inductionOn i .refl fun t ih => ih.tail (vert 0 t)
    exact Fin.inductionOn j (col0 i) fun t ih => ih.tail (horiz i t)
  rintro (⟨i,_|_⟩ | (⟨j,_|_⟩ | ⟨i,j⟩))
  · apply (cross i 0).tail
    have h := backward (hor i (0 : Fin (n+1)).castSucc)
    rw [hor_head_cast, Fin.castSucc_zero, hor_tail_zero] at h
    exact h
  · apply (cross i (Fin.last n)).tail
    have h := forward (hor i (Fin.last n).succ)
    rw [hor_tail_succ, Fin.succ_last, hor_head_last] at h
    exact h
  · apply (cross 0 j).tail
    have h := backward (ver j (0 : Fin (m+1)).castSucc)
    rw [ver_head_cast, Fin.castSucc_zero, ver_tail_zero] at h
    exact h
  · apply (cross (Fin.last m) j).tail
    have h := forward (ver j (Fin.last m).succ)
    rw [ver_tail_succ, Fin.succ_last, ver_head_last] at h
    exact h
  · exact cross i j

end GridPin

end SpectralBooks
end LinearAlgebra
end OAI
