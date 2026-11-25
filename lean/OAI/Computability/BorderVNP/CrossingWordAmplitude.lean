import OAI.Computability.BorderVNP.CrossingWordPorts

/-! # Signed binomial-weight lookup for one padded field factor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.WordFrame

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)

private def selectMode {L : ℕ} (m : Fin L) (a : Bool × Fin L) : Expr (Inputs L) :=
  let del := Expr.input (delPort m)
  .and (isMode m a.2) (.and (if a.1 then del else .not del)
    (.input (.inl (.inr (if a.1 then .inr a.2 else .inl a.2)))))

private theorem selectMode_eval {L : ℕ} (m : Fin L) (a : Bool × Fin L)
    (A I J : Finset ℕ) (x : Witnesses L → Bool) :
    (selectMode m a).eval (pack A I J x) = decide ((packet x m).2.1.val = a.2.val ∧
      (packet x m).1 = a.1 ∧ a.2.val ∈ (if a.1 then J else I)) := by
  rcases a with ⟨d,k⟩
  cases d <;> simp only [selectMode, Expr.eval, Bool.false_eq_true, ite_true, ite_false, isMode_eval] <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] <;> simp [pack, delPort, packet]

private theorem entry_zero {σ K : Type*} [Fintype K] (z : K → ℤ) (sel : K → Expr σ)
    (b : ℕ) (g : Fin b → σ) (neg : Bool) (x : σ → Bool) (h : ∀ i, (sel i).eval x = false) :
    (Lookup.entry z sel b g neg).eval x = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  rw [Lookup.entry, Expr.eval_disjoin_true] at ht
  obtain ⟨_, he, hh⟩ := ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  split_ifs at hh <;> simp [Expr.eval, h] at hh

private noncomputable def amplitudeExpr {L : ℕ} (dual : Bool) (m : Fin L) (neg : Bool) : Expr (Inputs L) :=
  let z (a : Bool × Fin L) := Padded.coefficient dual a.1 m a.2
  let pad := .and (.not (.input (delPort m))) (.and (Lookup.less _ (modePort m) 1)
      (Lookup.less _ (weightPort m) 1))
  Expr.mux (.input (.inl (.inl m))) (Lookup.entry z (selectMode m) _ (weightPort m) neg)
    (if neg then .const false else pad)

/-- The scalar of the field factor before the exterior and normal-order signs. -/
def amplitudeValue {L : ℕ} (dual : Bool) (m : Fin L) (A I J : Finset ℕ) (g : Padded.Packet L) : ℤ :=
  if m.val ∈ A then
    if g.2.1.val < L ∧ g.2.1.val ∈ (if g.1 then J else I) then
      signedGuess (Padded.coefficient dual g.1 m g.2.1.val) g.2.2.val else 0
  else if g = Padded.padding L then 1 else 0

private theorem signGuess_flag (z : ℤ) (n : ℕ) (neg : Bool) :
    flag (signedGuess z n) neg = decide ((if neg then z < 0 else 0 < z) ∧ n < z.natAbs) := by
  by_cases hn : n < z.natAbs <;> rcases lt_trichotomy z 0 with hz | rfl | hz <;> cases neg <;>
    simp [flag, signedGuess, *, Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, not_lt_of_gt]

private theorem amplitudeExpr_eval {L : ℕ} (dual : Bool) (m : Fin L) (neg : Bool)
    (A I J : Finset ℕ) (x : Witnesses L → Bool) :
    (amplitudeExpr dual m neg).eval (pack A I J x) = flag (amplitudeValue dual m A I J (packet x m)) neg := by
  let g := packet x m
  rw [amplitudeExpr, Expr.eval_mux]
  change (if decide (m.val ∈ A) then _ else _) = _
  by_cases hm : m.val ∈ A
  · simp only [hm, decide_true, ite_true, amplitudeValue]
    by_cases h : g.2.1.val < L ∧ g.2.1.val ∈ (if g.1 then J else I)
    · let i : Bool × Fin L := (g.1, ⟨g.2.1.val, h.1⟩)
      have hi (a : Bool × Fin L) : (selectMode m a).eval (pack A I J x) = decide (i = a) := by
        rw [selectMode_eval]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        change (g.2.1.val = a.2.val ∧ g.1 = a.1 ∧ _) ↔ _
        constructor
        · rintro ⟨hk,hd,_⟩
          exact Prod.ext hd (Fin.ext hk)
        · rintro rfl
          exact ⟨rfl,rfl,h.2⟩
      rw [ite_eq_left h, signGuess_flag, Lookup.entry_eval _ _ _ _ _ i hi]
      rfl
    · have hn (a : Bool × Fin L) : (selectMode m a).eval (pack A I J x) = false := by
        rw [selectMode_eval, decide_eq_false_iff_not]
        rintro ⟨hk,hd,hs⟩
        exact h ⟨by rw [show g.2.1.val = a.2.val from hk]; exact a.2.isLt,
          by simpa only [g, hk, hd] using hs⟩
      rw [ite_eq_right h, entry_zero _ _ _ _ _ _ hn]
      cases neg <;> rfl
  · simp only [hm, decide_false, Bool.false_eq_true, ite_false, amplitudeValue]
    have hpad : g = Padded.padding L ↔ g.1 = false ∧ g.2.1.val < 1 ∧ g.2.2.val < 1 := by
      rcases g with ⟨v,k,u⟩
      change (v,k,u) = (false,0,0) ↔ _
      constructor
      · rintro h; cases h; simp
      · rintro ⟨hd,hk,hu⟩
        change k.val < 1 at hk
        change u.val < 1 at hu
        exact Prod.ext hd (Prod.ext (Fin.ext (by change k.val = 0; omega))
          (Fin.ext (by change u.val = 0; omega)))
    cases neg <;> simp only [ite_true, Bool.false_eq_true, ite_false, Expr.eval, Lookup.less_eval]
    · change ((!g.1) && (decide (g.2.1.val < 1) && decide (g.2.2.val < 1))) =
        flag (if g = Padded.padding L then 1 else 0) false
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      rw [← hpad]
      split_ifs <;> simp_all [flag]
    · by_cases he : g = Padded.padding L <;> simp [flag, he, g] at *

/-- The pair of acceptance outputs for the signed binomial and the validity of the selected mode. -/
noncomputable def amplitude {L : ℕ} (dual : Bool) (m : Fin L) : Frame (Inputs L) Bool :=
  (Frame.initial id).step (amplitudeExpr dual m)

theorem amplitude_eval {L : ℕ} (dual : Bool) (m : Fin L) (A I J : Finset ℕ) (x : Witnesses L → Bool)
    (neg : Bool) :
    (amplitude dual m).eval (pack A I J x) neg = flag (amplitudeValue dual m A I J (packet x m)) neg := by
  simp only [amplitude, Frame.step_eval]
  rw [show (Frame.initial (id : Inputs L → Inputs L)).eval (pack A I J x) = pack A I J x by ext; simp]
  exact amplitudeExpr_eval dual m neg A I J x

theorem amplitude_size {L : ℕ} (dual : Bool) (m : Fin L) :
    (amplitude dual m).size ≤ 100 * (L+1)^2 := by
  apply (Frame.step_size_le (Frame.initial id) (amplitudeExpr dual m) (50*(L+1)^2) ?_).trans
  · simp; omega
  intro neg
  have hs (a : Bool × Fin L) : (selectMode m a).size ≤ 6 * Padded.width L + 10 := by
    rcases a with ⟨d,k⟩
    have hk := isMode_size m k
    cases d <;> simp only [selectMode, Expr.size, ite_true, Bool.false_eq_true, ite_false] <;> omega
  have he := Lookup.entry_size (fun a : Bool × Fin L => Padded.coefficient dual a.1 m a.2)
    (selectMode m) _ (weightPort m) neg _ hs
  have h₁ := Lookup.less_size _ (modePort m) 1
  have h₂ := Lookup.less_size _ (weightPort m) 1
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at he
  cases neg <;> simp only [amplitudeExpr, Expr.mux, Expr.size, Bool.false_eq_true, ite_true, ite_false] <;>
    unfold Padded.width at * <;> nlinarith

end Crossing.Signed.WordFrame

end BorderVNP
end Computability
end OAI
