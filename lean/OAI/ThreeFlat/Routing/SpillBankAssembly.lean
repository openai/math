import OAI.ThreeFlat.Routing.SpillBankBoard
import OAI.ThreeFlat.Routing.SpillReserveSelect

namespace OAI
/-! # Combining the primary and reserve output assignments -/

noncomputable section
open scoped Classical

namespace ThreeFlat.Routing.Spill
open Concentrator

variable {C q D R : ℕ} (B : TwoPassBank C q D R)

/-- A matching on the primary board combines with the reserve assignment for
its uncovered active rows. The public edge bits are the graph of the resulting
injection into the complete bank. -/
theorem assemble_bank_injection (A S : Finset (Fin (C*R))) (cap : ℕ)
    (P : Candidate (primaryBoard B) → Bool)
    (selectedActive : ∀ i (r : primaryBoard B i), P ⟨i,r⟩ = true → i ∈ A)
    (sameRow : ∀ i (r s : primaryBoard B i), P ⟨i,r⟩ = true → P ⟨i,s⟩ = true → r = s)
    (sameRegister : Function.Injective (fun e : {e : Candidate (primaryBoard B) // P e = true} =>
      e.val.2.val))
    (missed : ∀ i, i ∈ S ↔ i ∈ A ∧ ∀ r : primaryBoard B i, P ⟨i,r⟩ = false)
    (done : B.G.live B.slots S cap = ∅) :
    ∃ f : A ↪ Fin R, (∀ a, f a ∈ fullBoard B a.val) ∧
      boardPick B P (reservePick B.G (reserveReports B.G B.slots cap S)) = injectionPins A f := by
  let reserve := B.G.assignment S B.slots cap (B.G.departure B.slots S cap)
    (B.G.validLabels_departure B.slots S cap) done
  let Addr := Fin B.primary ⊕ (Fin B.reserveSize × Fin B.slots)
  let chosen (i : Fin (C*R)) : Addr → Prop
    | .inl r => ∃ hr : r ∈ primaryBoard B i, P ⟨i,⟨r,hr⟩⟩ = true
    | .inr p => ∃ hi : i ∈ S, reserve ⟨i,hi⟩ = p
  have active {i v} (h : chosen i v) : i ∈ A := by
    cases v with
    | inl r =>
      obtain ⟨hr,hp⟩ := h
      exact selectedActive i ⟨r,hr⟩ hp
    | inr p =>
      obtain ⟨hi,_⟩ := h
      exact ((missed i).mp hi).1
  have distinct {i} {u v : Addr} (hu : chosen i u) (hv : chosen i v) : u = v := by
    cases u with
    | inl a =>
      obtain ⟨ha,hpa⟩ := hu
      cases v with
      | inl b =>
        obtain ⟨hb,hpb⟩ := hv
        exact congrArg Sum.inl (congrArg Subtype.val (sameRow i ⟨a,ha⟩ ⟨b,hb⟩ hpa hpb))
      | inr p =>
        obtain ⟨hi,_⟩ := hv
        exact False.elim (Bool.noConfusion (hpa.symm.trans (((missed i).mp hi).2 ⟨a,ha⟩)))
    | inr p =>
      obtain ⟨hi,hp⟩ := hu
      cases v with
      | inl a =>
        obtain ⟨ha,hpa⟩ := hv
        exact False.elim (Bool.noConfusion (hpa.symm.trans (((missed i).mp hi).2 ⟨a,ha⟩)))
      | inr t =>
        obtain ⟨_,ht⟩ := hv
        exact congrArg Sum.inr (hp.symm.trans ht)
  have total (i : A) : ∃ v, chosen i.val v := by
    by_cases hi : i.val ∈ S
    · exact ⟨.inr (reserve ⟨_,hi⟩),hi,rfl⟩
    · have hp : ∃ r : primaryBoard B i.val, P ⟨i.val,r⟩ = true := by
        by_contra! hn
        exact hi ((missed i.val).mpr ⟨i.property, fun r => by simpa using hn r⟩)
      obtain ⟨r,hr⟩ := hp
      exact ⟨.inl r.val,r.property,hr⟩
  choose dest hdest using total
  let g : A ↪ Addr := ⟨dest, fun x y h => by
    have hx := hdest x
    have hy := hdest y
    rw [h] at hx
    cases hval : dest y with
    | inl r =>
      rw [hval] at hx hy
      obtain ⟨hr,hp⟩ := hx
      obtain ⟨hr',hp'⟩ := hy
      have eqn := sameRegister (a₁ := ⟨⟨x.val,⟨r,hr⟩⟩,hp⟩)
        (a₂ := ⟨⟨y.val,⟨r,hr'⟩⟩,hp'⟩) rfl
      exact Subtype.ext (congrArg (fun a => a.val.1) eqn)
    | inr p =>
      rw [hval] at hx hy
      obtain ⟨hi,he⟩ := hx
      obtain ⟨hj,hf⟩ := hy
      exact Subtype.ext (congrArg (fun a : S => a.val) (reserve.injective (he.trans hf.symm)))⟩
  let f := g.trans B.address.toEmbedding
  refine ⟨f, ?_, ?_⟩
  · intro x
    apply mem_publicNeighbors_of_adjacent B.address.toEmbedding B.N B.G x.val (g x)
    have hit : chosen x.val (g x) := hdest x
    cases hg : g x with
    | inl r =>
      rw [hg] at hit
      exact List.mem_toFinset.mp hit.choose
    | inr p =>
      rw [hg] at hit
      obtain ⟨hi,rfl⟩ := hit
      change B.G.owner _ x.val = B.G.src x.val ∨ B.G.owner _ x.val = B.G.dst x.val
      unfold ReserveGraph.owner
      split <;> simp
  · funext c
    obtain ⟨i,r,hadj⟩ := c
    obtain ⟨z,rfl⟩ := B.address.surjective r
    have realization : (∃ hi : i ∈ A, f ⟨i,hi⟩ = B.address z) ↔ chosen i z := by
      constructor
      · rintro ⟨hi,hh⟩
        exact B.address.injective hh ▸ hdest ⟨i,hi⟩
      · intro hh
        let x : A := ⟨i,active hh⟩
        exact ⟨x.property, congrArg B.address (distinct (hdest x) hh)⟩
    apply Bool.eq_iff_iff.mpr
    simp only [injectionPins,decide_eq_true_eq,realization]
    have adj := (mem_publicNeighbors_iff B.address.toEmbedding B.N B.G i z).mp hadj
    cases z with
    | inl r =>
      have hr : r ∈ primaryBoard B i := List.mem_toFinset.mpr adj
      have signal : boardSignal B ⟨i,⟨B.address (.inl r),hadj⟩⟩ = .inl ⟨i,⟨r,hr⟩⟩ := by
        unfold boardSignal
        split <;> rename_i he <;> change B.address.symm (B.address (.inl r)) = _ at he
        · rw [Equiv.symm_apply_apply] at he
          cases Sum.inl.inj he
          rfl
        · simp at he
      simp only [boardPick,Function.comp_apply,signal,Sum.elim_inl]
      exact ⟨fun hp => ⟨hr,hp⟩,fun ⟨_,hp⟩ => hp⟩
    | inr p =>
      rcases p with ⟨v,j⟩
      let side := decide (v ≠ B.G.src i)
      have end_eq : reserveEnd B.G (i,side,j) = v := by
        rcases adj with h | h
        · simp [side,h,reserveEnd]
        · by_cases eq : v = B.G.src i <;> simp [side,eq,reserveEnd,h.symm]
      have loop : side = true → B.G.src i ≠ B.G.dst i := by
        intro hs eqn
        rcases adj with h | h <;> simp [side,h,eqn] at hs
      have signal : boardSignal B ⟨i,⟨B.address (.inr (v,j)),hadj⟩⟩ = .inr (i,side,j) := by
        unfold boardSignal
        split <;> rename_i he <;> change B.address.symm (B.address (.inr (v,j))) = _ at he
        · simp at he
        · rw [Equiv.symm_apply_apply] at he
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inr.inj he)
          rfl
      simp only [boardPick,Function.comp_apply,signal,Sum.elim_inr]
      simpa only [end_eq, and_iff_left loop] using
        reservePick_iff_assignment B.G B.slots cap S done i side j

end ThreeFlat.Routing.Spill

end
end OAI
