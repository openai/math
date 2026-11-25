import OAI.Computability.BorderVNP.TeamSiteConsistencyHandoff

/-! # Reading arbitrary proposed register links in physical processor order

Only the public initial frame is known in advance. For a tuple of locally accepted
physical leaves, the first sender checks a canonical output word, and the next
receiver sees exactly that word. Induction gives a decoded frame at every site
without imposing canonicality on the externally supplied assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteTraversal

open TeamTapeHandoff TeamContraction.Wires TeamSiteConsistency

variable {r k w : ℕ} {A : Type*}

/-- The first site uses the public frame, all others see its predecessor's exact bits. -/
def Reads (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (first : Frame w k) (j : Fin r) (f : Frame w k) : Prop :=
  if j.val = 0 then f = first else f.bits = frameInput raw true j

/-- A nonfinal sender checks its outgoing bits; the final site instead checks acceptance. -/
def Writes (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (j : Fin r) (f : Frame w k) : Prop :=
  if j.val+1 < r then f.bits = frameInput raw false j else f.halted = true

private noncomputable def readCanonical (xs : List Bool) : Frame w k := by
  classical
  exact if h : ∃ f : Frame w k, f.bits = xs then h.choose else .accepted 0

private theorem readCanonical_bits (f : Frame w k) : readCanonical f.bits = f := by
  classical
  unfold readCanonical
  have h : ∃ g : Frame w k, g.bits = f.bits := ⟨f,rfl⟩
  rw [dite_eq_left h]
  exact Frame.bits_injective h.choose_spec

private noncomputable def inputFrame (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (first : Frame w k)
    (j : Fin r) : Frame w k := if j.val=0 then first else readCanonical (frameInput raw true j)

private theorem adjacent_bits (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (i j : Fin r) (h : j.val=i.val+1) :
    frameInput raw false i = frameInput raw true j := by
  have hi : i.val+1 < r := h ▸ j.isLt
  have eq : frameIndex false i = frameIndex true j := by
    simp [frameIndex,hi,h]
  simp only [frameInput, eq]

/-- Traversing accepted rows constructs all native chunks and typed outputs in order,
as well as the exact physical frame checks and final accepted status. The row predicate
may also retain its emitted records, local sorting verdict, choice bits and sign. -/
theorem collect (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (first : Frame w k)
    (R : Fin r → Frame w k → A → Frame w k → Prop)
    (row : ∀ j f, Reads raw first j f → ∃ a g, R j f a g ∧ Writes raw j g) :
    ∃ payload : Fin r → A, ∃ input output : Fin r → Frame w k,
      FrameChecks raw first input output ∧
      (∀ j, R j (input j) (payload j) (output j)) ∧ ∀ j, j.val+1=r → (output j).halted=true := by
  let input := inputFrame raw first
  have validN (n : ℕ) : ∀ h : n < r, Reads raw first ⟨n,h⟩ (input ⟨n,h⟩) := by
    induction n with
    | zero => intro h; simp [Reads,input,inputFrame]
    | succ n ih =>
      intro h
      let i : Fin r := ⟨n,by omega⟩
      let j : Fin r := ⟨n+1,h⟩
      obtain ⟨a,g,_,sent⟩ := row i _ (ih i.isLt)
      have hs : g.bits = frameInput raw false i := by simpa only [Writes,show i.val+1<r from h,ite_true] using sent
      have incoming := hs.trans (adjacent_bits raw i j rfl)
      change Reads raw first j (input j)
      simp only [Reads,input,inputFrame,show j.val≠0 from Nat.succ_ne_zero n,ite_false,← incoming,readCanonical_bits]
  choose dat output certified sent using fun j => row j (input j) (validN j.val j.isLt)
  refine ⟨dat,input,output,⟨?_,?_,?_⟩,certified,?_⟩
  · intro j h; simp [input,inputFrame,h]
  · intro j h; simpa [Reads,Nat.ne_of_gt h] using validN j.val j.isLt
  · intro j h; simpa [Writes,h] using sent j
  · intro j h; simpa [Writes,h] using sent j

/-- An already validated array passes the same per-site predecessor and output tests. -/
theorem frame_conditions (raw : Fin (r-1) → Fin (frameWidth k w) → Bool) (first : Frame w k)
    (ins outs : Fin r → Frame w k) (frames : FrameChecks raw first ins outs)
    (final : ∀ j, j.val+1=r → (outs j).halted=true) (j : Fin r) :
    Reads raw first j (ins j) ∧ Writes raw j (outs j) := by
  constructor
  · by_cases hj : j.val=0
    · simpa [Reads,hj] using frames.initial j hj
    · simpa [Reads,hj] using frames.received j (Nat.pos_of_ne_zero hj)
  · by_cases hj : j.val+1<r
    · simpa [Writes,hj] using frames.sent j hj
    · simpa [Writes,hj] using final j (by have := j.isLt; omega)

/-- For one physical assignment the canonical incoming frames agree regardless of the
path witnesses used to reconstruct them. -/
theorem same_inputs {raw : Fin (r-1) → Fin (frameWidth k w) → Bool} {first : Frame w k}
    {i₁ o₁ i₂ o₂ : Fin r → Frame w k} (a : FrameChecks raw first i₁ o₁) (b : FrameChecks raw first i₂ o₂) :
    i₁ = i₂ := by
  funext j
  by_cases h : j.val=0
  · exact (a.initial j h).trans (b.initial j h).symm
  · exact Frame.bits_injective ((a.received j (Nat.pos_of_ne_zero h)).trans (b.received j (Nat.pos_of_ne_zero h)).symm)

end TeamSiteTraversal

end BorderVNP
end Computability
end OAI
