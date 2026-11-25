import OAI.Computability.BorderVNP.PackedTerminalPhysical
import OAI.Computability.BorderVNP.PackedTerminalArgmin

/-!
# A complete public Boolean pass for the terminal site motion

All motion candidates act on the same stored site and cable rows. A single
minimizer supplies the output motion field, all lower tile addresses, and
the move and charge columns of the site pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Terminal

open Cover Cover.AddressCircuit Shortening Epoch Epoch.Round Catalog PublicRelative PublicSegments
open PublicEndpoints Crossing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q a m : ℕ} (enum : Fin q ≃ Cube D) (S : Finset (HyperbolicHost (Cube D)))
  (L : ℝ) {u : Fin m → Cover.Frame.SL} (hu : ∀ i, Cover.Frame.Clears (u i) a)

include hu in
private theorem uniformSiteFrames :
    ∃ C k : ℕ, ∀ d (σ : Cube D → Fin m), ∃ f, MovesSite (a := a) enum S (g := u ∘ σ) (d+2) f ∧
      f.size ≤ C*(d+3)^k := by
  choose M b h using fun σ : Cube D → Fin m => site_frames enum S (fun i => hu (σ i))
  refine ⟨Finset.univ.sup M,Finset.univ.sup b,?_⟩
  intro d σ
  obtain ⟨f,hf,hs⟩ := h σ d
  exact ⟨f,hf,hs.trans (Nat.mul_le_mul (Finset.le_sup (Finset.mem_univ σ))
    (Nat.pow_le_pow_right (by omega) (Finset.le_sup (Finset.mem_univ σ))))⟩

/-- A terminal pass returns the selected motion's one-hot name and the whole route table. -/
abbrev Selected (D m : ℕ) (Move : Type*) (q l V E w : ℕ) :=
  (Cube D → Fin m) ⊕ RouteRows.Pins Move q l V E w

/-- Explicit gate bound before absorbing the fixed motion and move lists into the constant. -/
def selectionCost (Move : Type*) [Fintype Move] (n q Cs ks Cm km d V E w : ℕ) : ℕ :=
  1 + n * (1+V*Cs*(d+3)^ks + 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+90*q*(d+3)+1)^3 +
    (1+E*Cm*(d+3)^km)) + TerminalArgmin.cost Move n q (d+2) V E w

set_option maxHeartbeats 1800000 in
/-- The terminal pass chooses and executes a common minimizing physical motion
using only the prior public descriptor rows. It also returns a readable one-hot
choice for the geometric history, uniformly over all packs and fields. -/
theorem selected_frames (hn : Nonempty (Cube D → Fin m)) :
    ∃ Cs ks Cm km : ℕ, ∀ {Data : Type} [Fintype Data] (d lev : ℕ) (hl : lev+1=d+2+2*a)
      (field : FieldBit (↥S) (Cube D) (lev+1) → Data) (V E w : ℕ), V ≤ 2^w →
      ∃ f : Frame (Input Data V E w) (Selected D m ↥(allowedMoves (Cube D) L) q (d+2) V E w),
        f.size ≤ selectionCost ↥(allowedMoves (Cube D) L) (Fintype.card (Cube D → Fin m)) q Cs ks Cm km d V E w ∧
        ∀ {P : Type} {R : Type*} {bits : P → ℕ} {p : PlacedPack D P bits R (Cube D) lev}
          (dir : Normalized.Directory p V E) (x : Input Data V E w → Bool), dir.Reads S field x →
        let moved (σ : Cube D → Fin m) (v : p.pack.layout.Site) :=
          productMotion (d+2) (Equiv.refl _) (fun i => hu (σ i)) (levelCast hl (p.site v))
        ∃ σ, (∀ τ, terminalScore p.pack (moved σ) p.active ≤ terminalScore p.pack (moved τ) p.active) ∧
          (∀ τ, f.eval x (.inl τ) = decide (τ=σ)) ∧
          CandidateRows enum hl (fun i => hu (σ i)) dir L (f.eval x ∘ Sum.inr) := by
  let Choice := Cube D → Fin m
  let n := Fintype.card Choice
  let order := Fintype.equivFin Choice
  let Move := ↥(allowedMoves (Cube D) L)
  obtain ⟨Cs,ks,hsite⟩ := uniformSiteFrames enum S hu
  obtain ⟨Cm,km,hmove⟩ := move_frames enum L
  refine ⟨Cs,ks,Cm,km,?_⟩
  intro Data _ d lev hl field V E w fit
  let Y := RouteRows.Pins Move q (d+2) V E w
  choose site hsem hsize using fun i : Fin n => hsite d (order.symm i)
  obtain ⟨move,hm,hms⟩ := hmove (d+1)
  choose lane hs hrow using fun i : Fin n =>
    candidate_frames (E := E) enum S hl field (fun k => hu (order.symm i k)) L fit (site i) (hsem i) move hm
  obtain ⟨bank,hbank,he⟩ := exists_parallelFrames (out := fun _ : Fin n => Y) lane
  let table := bank.select (fun j : Fin n × Y => ⟨j.1,j.2⟩)
  obtain ⟨pick,hpick,hbest⟩ := TerminalArgmin.exists_frame Move n q (d+2) V E w
  let f := (pick.subst table).select (Sum.map order id)
  refine ⟨f,?_,?_⟩
  · let M := 1+V*Cs*(d+3)^ks + 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+90*q*(d+3)+1)^3 +
      (1+E*Cm*(d+3)^km)
    have hc : Fintype.card (ProductSlots q (d+2)) = 90*q*(d+3) := by
      simp [ProductSlots,StackFrame.Slots,width]
      ring
    have hLane (i : Fin n) : (lane i).size ≤ M := by
      apply (hs i).trans
      rw [hc]
      have h₁ := Nat.mul_le_mul_left V (hsize i)
      have h₂ := Nat.mul_le_mul_left E hms
      dsimp only [M]
      rw [Nat.mul_assoc V,Nat.mul_assoc E]
      exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left h₁ 1) _) (Nat.add_le_add_left h₂ 1)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hLane i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hsum
    change (pick.subst table).size ≤ _
    rw [Frame.subst_size,show table.size=bank.size from rfl]
    exact Nat.add_le_add (hbank.trans (Nat.add_le_add_left hsum 1)) hpick
  · intro P R bits p dir x hx moved
    let b := table.eval x
    have hr (i : Fin n) : (fun j => b (i,j)) = (lane i).eval x := by
      funext j; exact (Frame.select_eval _ _ _ _).trans (he _ _ _)
    have hz (i : Fin n) : CandidateRows enum hl (fun j => hu (order.symm i j)) dir L (fun j => b (i,j)) :=
      (hr i).symm ▸ hrow i dir x hx
    have hscore (i : Fin n) : TerminalArgmin.score (fun j => b (i,j)) =
        terminalScore p.pack (moved (order.symm i)) p.active := (hz i).score
    have hN : 0 < n := Fintype.card_pos_iff.mpr hn
    obtain ⟨i,hi,hmin⟩ := TerminalArgmin.exists_minimum hN b
    obtain ⟨hflag,hemit⟩ := hbest b
    have row : f.eval x ∘ Sum.inr = fun j => b (i,j) := by
      funext j
      change f.eval x (.inr j) = _
      rw [show f = (pick.subst table).select (Sum.map order id) from rfl,Frame.select_eval,Sum.map_inr,Frame.subst_eval]
      exact hemit i hi j
    refine ⟨order.symm i,?_,?_,row.symm ▸ hz i⟩
    · intro τ
      have h := hmin (order τ)
      simpa only [hscore,Equiv.symm_apply_apply] using h
    · intro τ
      apply Bool.eq_iff_iff.mpr
      rw [show f = (pick.subst table).select (Sum.map order id) from rfl,Frame.select_eval,Sum.map_inl,Frame.subst_eval]
      change pick.eval b (.inl (order τ)) = true ↔ _
      rw [hflag,hi]
      simp [Equiv.eq_symm_apply,eq_comm]

end PackedHistoryCircuit.Terminal

end BorderVNP
end Computability
end OAI
