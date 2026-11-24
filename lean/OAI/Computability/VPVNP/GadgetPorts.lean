import OAI.Computability.VPVNP.HamiltonianGadget

/-! # Port neighborhoods of the exact-one Hamiltonian-cycle graph -/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

variable {k h c : ℕ} {occ : Fin h → Fin k × Fin c × Bool}

private theorem prevPort_buffer {i i' : Fin k} {j : Fin h} {b : Bool}
    (t : Fin (h + 1)) (he : prevPort (c := c) i' t = .port i j b) :
    .buffer i' t = portBuffer (c := c) i j b := by
  induction t using Fin.cases with
  | zero => simp at he
  | succ t => simp only [prevPort_succ, Vertex.port.injEq] at he; rcases he with ⟨rfl,rfl,rfl⟩; rfl

private theorem nextPort_buffer {i i' : Fin k} {j : Fin h} {b : Bool}
    (t : Fin (h + 1)) (he : nextPort (c := c) i' t = .port i j b) :
    .buffer i' t = portBuffer (c := c) i j b := by
  induction t using Fin.lastCases with
  | last => simp at he
  | cast t => simp only [nextPort_castSucc, Vertex.port.injEq] at he; rcases he with ⟨rfl,rfl,rfl⟩; rfl

theorem Allowed.from_port {i : Fin k} {j : Fin h} {b : Bool} {v : Vertex k h c}
    (edge : Allowed occ (.port i j b) v) :
    v = portBuffer i j b ∨ (v = .port i j (!b) ∧ ((occ j).1 ≠ i ∨ (occ j).2.2 = b)) ∨
      (v = .clause (occ j).2.1 ∧ (occ j).1 = i ∧ b = !(occ j).2.2) := by
  generalize hs : Vertex.port i j b = u at edge
  cases edge with
  | prevBuffer i' t => exact Or.inl (prevPort_buffer t hs.symm)
  | nextBuffer i' t => exact Or.inl (nextPort_buffer t hs.symm)
  | cross i' j' b' hcross => cases hs; exact Or.inr (Or.inl ⟨rfl, hcross⟩)
  | enterClause j' => cases hs; simp
  | _ => cases hs

theorem Allowed.to_port {i : Fin k} {j : Fin h} {b : Bool} {u : Vertex k h c}
    (edge : Allowed occ u (.port i j b)) :
    u = portBuffer i j b ∨ (u = .port i j (!b) ∧ ((occ j).1 ≠ i ∨ (occ j).2.2 = !b)) ∨
      (u = .clause (occ j).2.1 ∧ (occ j).1 = i ∧ b = (occ j).2.2) := by
  generalize hs : Vertex.port i j b = v at edge
  cases edge with
  | bufferPrev i' t => exact Or.inl (prevPort_buffer t hs.symm)
  | bufferNext i' t => exact Or.inl (nextPort_buffer t hs.symm)
  | cross i' j' b' hcross => cases hs; exact Or.inr (Or.inl (by simpa using hcross))
  | exitClause j' => cases hs; simp
  | _ => cases hs

/-- The buffer next to an endpoint, indexed by its side of the track. -/
def endpointBuffer (i : Fin k) (b : Bool) : Vertex k h c :=
  .buffer i (if b then Fin.last h else 0)

private theorem prevEndpoint_buffer {i i' : Fin k} {b : Bool}
    (t : Fin (h + 1)) (he : prevPort (c := c) i' t = .endpoint i b) :
    .buffer i' t = endpointBuffer (c := c) i b := by
  induction t using Fin.cases with
  | zero => simp only [prevPort_zero, Vertex.endpoint.injEq] at he; rcases he with ⟨rfl,rfl⟩; rfl
  | succ t => simp at he

private theorem nextEndpoint_buffer {i i' : Fin k} {b : Bool}
    (t : Fin (h + 1)) (he : nextPort (c := c) i' t = .endpoint i b) :
    .buffer i' t = endpointBuffer (c := c) i b := by
  induction t using Fin.lastCases with
  | last => simp only [nextPort_last, Vertex.endpoint.injEq] at he; rcases he with ⟨rfl,rfl⟩; rfl
  | cast t => simp at he

theorem Allowed.from_endpoint {i : Fin k} {b : Bool} {v : Vertex k h c}
    (edge : Allowed occ (.endpoint i b) v) :
    v = endpointBuffer i b ∨ v = .sep (finRotate k i) := by
  generalize hs : Vertex.endpoint i b = u at edge
  cases edge with
  | prevBuffer i' t => exact Or.inl (prevEndpoint_buffer t hs.symm)
  | nextBuffer i' t => exact Or.inl (nextEndpoint_buffer t hs.symm)
  | exitTrack i' b' => cases hs; exact Or.inr rfl
  | _ => cases hs

theorem Allowed.to_endpoint {i : Fin k} {b : Bool} {u : Vertex k h c}
    (edge : Allowed occ u (.endpoint i b)) : u = endpointBuffer i b ∨ u = .sep i := by
  generalize hs : Vertex.endpoint i b = v at edge
  cases edge with
  | bufferPrev i' t => exact Or.inl (prevEndpoint_buffer t hs.symm)
  | bufferNext i' t => exact Or.inl (nextEndpoint_buffer t hs.symm)
  | enterTrack i' b' => cases hs; exact Or.inr rfl
  | _ => cases hs

/-- The left and right neighbor of a buffer are distinct, including an empty track. -/
theorem prev_next_ne (i : Fin k) (t : Fin (h + 1)) :
    prevPort (c := c) i t ≠ nextPort i t := by
  suffices disjoint : ∀ l r : Fin (h + 1), prevPort (c := c) i l ≠ nextPort i r from disjoint t t
  intro l r
  induction l using Fin.cases <;> induction r using Fin.lastCases <;> simp

/-- A spanning permutation cannot contain a 2-cycle: a track has at least four vertices. -/
theorem no_two_cycle (π : Equiv.Perm (Vertex k h c)) (cycle : π.IsCycleOn Set.univ)
    (i : Fin k) (v : Vertex k h c) : π (π v) ≠ v := by
  intro hv
  have hcy : π.IsCycleOn (Finset.univ : Finset (Vertex k h c)) := by simpa using cycle
  have hdiv := (hcy.pow_apply_eq (Finset.mem_univ v) (n := 2)).mp
    (by simpa [pow_two] using hv)
  rw [Finset.card_univ, card_vertex] at hdiv
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  have hi : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hmul := Nat.le_mul_of_pos_left (3*h+4) hi
  omega

/-- A tour passes through each degree-two buffer from one side to the other. -/
theorem buffer_directions (π : Equiv.Perm (Vertex k h c)) (cycle : π.IsCycleOn Set.univ)
    (allowed : ∀ v, Allowed occ v (π v)) (i : Fin k) (t : Fin (h + 1)) :
    (π (.buffer i t) = nextPort i t ∧ π (prevPort i t) = .buffer i t) ∨
    (π (.buffer i t) = prevPort i t ∧ π (nextPort i t) = .buffer i t) := by
  obtain ⟨v, hv⟩ := π.surjective (.buffer i t)
  have he := allowed v
  rw [hv] at he
  have hin := allowed_to_buffer_iff.mp he
  have hout := allowed_from_buffer_iff.mp (allowed (.buffer i t))
  have hne := no_two_cycle π cycle i v
  rw [hv] at hne
  rcases hin with rfl | rfl
  · exact Or.inl ⟨hout.resolve_left hne, hv⟩
  · exact Or.inr ⟨hout.resolve_right hne, hv⟩

end HCGadget

end VPVNP
end Computability
end OAI
