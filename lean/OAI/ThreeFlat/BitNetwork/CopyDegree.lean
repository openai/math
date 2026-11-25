import OAI.ThreeFlat.BitNetwork.CopyGraph

namespace OAI
/-! # The degree and size of the copy chains

At a data cell the three local ports are the three sockets. At a chain node
the ports are the outgoing trunk, incoming trunk, and the spoke at that node.
A pin occupies the third port at the initial node, before the first spoke.
-/

namespace ThreeFlat.BitNetwork

open Computability.BorderVNP.Crossing
open scoped Classical BigOperators

variable {F : Type*} {p : ℕ} (N : BitNetwork F p)

private abbrev End := Fin p ⊕ N.CopyEdge × Bool

private noncomputable def incident : N.End → N.CopySite :=
  Sum.elim N.copyGraph.attach (fun q ↦ if q.2 then N.copyDst q.1 else N.copySrc q.1)

private def localPort : N.End → Fin 3
  | .inl _ => 2
  | .inr (.inl _, false) => 0
  | .inr (.inl _, true) => 1
  | .inr (.inr _, false) => 2
  | .inr (.inr u, true) => u.2

private noncomputable def recover : N.CopySite → Fin 3 → Option N.End
  | .inl i, l => some (.inr (.inr (i,l), true))
  | .inr ⟨s,j⟩, l =>
    if l = 0 then
      if h : j.val < N.arity s + 1 then some (.inr (.inl ⟨s, ⟨j.val,h⟩⟩, false)) else none
    else if l = 1 then
      if h : j.val - 1 < N.arity s + 1 then
        some (.inr (.inl ⟨s, ⟨j.val-1,h⟩⟩, true))
      else none
    else if j.val = 0 then
      match s with
      | .pin i => some (.inl i)
      | _ => none
    else if h : j.val - 1 < N.arity s then
      some (.inr (.inr (((N.socketOrder s).symm ⟨j.val-1,h⟩).val), false))
    else none

private theorem recover_port (e : N.End) :
    N.recover (N.incident e) (N.localPort e) = some e := by
  rcases e with i | ⟨e, b⟩
  · simp [recover, incident, localPort, copyGraph]
  · rcases e with ⟨s,j⟩ | ⟨c,k⟩
    · cases b <;> simp [recover, incident, Sum.elim, localPort, copyDst, copySrc, j.isLt]
    · cases b <;> simp [recover, incident, Sum.elim, localPort, copyDst, copySrc, copyPosition]

/-- Every incidence at a fixed physical vertex occupies its own local port. -/
theorem copyGraph_bitDegree (v : N.CopySite) : N.copyGraph.bitDegree v ≤ 3 := by
  classical
  unfold Network.bitDegree
  rw [← Fintype.card_coe, ← Fintype.card_fin 3]
  apply Fintype.card_le_of_injective (fun e ↦ N.localPort e.val)
  intro ⟨e,he⟩ ⟨f,hf⟩ h
  have he' : N.incident e = v := (Finset.mem_filter.mp he).2
  have hf' : N.incident f = v := (Finset.mem_filter.mp hf).2
  have eqn := congrArg (N.recover v) h
  dsimp only at eqn
  rw [← he'] at eqn
  rw [N.recover_port e, he', ← hf', N.recover_port f] at eqn
  exact Subtype.ext (Option.some.inj eqn)

/-- All cables have width one and every vertex is at most trivalent. -/
theorem copyGraph_trivalent : N.copyGraph.Trivalent :=
  ⟨fun _ ↦ rfl, N.copyGraph_bitDegree⟩

private def sourceEquiv : N.Source ≃ Fin N.internal ⊕ (Fin p ⊕ Bool) where
  toFun
    | .hidden i => .inl i
    | .pin i => .inr (.inl i)
    | .constant b => .inr (.inr b)
  invFun
    | .inl i => .hidden i
    | .inr (.inl i) => .pin i
    | .inr (.inr b) => .constant b
  left_inv := by intro s; cases s <;> rfl
  right_inv := by rintro (i | (i | b)) <;> rfl

/-- The counts include a two-node chain even for a source with no readers. -/
theorem copyGraph_bitVolume : N.copyGraph.bitVolume =
    10 * N.cells + 3 * N.internal + 4 * p + 6 := by
  have total : ∑ s : N.Source, N.arity s = N.cells * 3 := by
    simpa [arity, Fiber, Socket] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv N.address))
  have card : Fintype.card N.Source = N.internal + (p + 2) := by
    simpa using (Fintype.card_congr N.sourceEquiv)
  change Fintype.card N.CopySite + Fintype.card N.CopyEdge + Fintype.card (Fin p) = _
  simp only [CopySite, CopyEdge, Socket, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin, Fintype.card_prod, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [total, card]
  push_cast
  omega

theorem copyGraph_volume_le : N.copyGraph.bitVolume ≤ 10 * (N.cells + N.internal + p + 1) := by
  rw [copyGraph_bitVolume]
  omega

end ThreeFlat.BitNetwork

end OAI
