import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.PackedChoiceMux

/-! # Selecting a terminal rounding by its actual active cable width

Each candidate has a complete physical route directory. Masking the width of
each cable by its charge bit gives the rounded nonlocal width, even when a
live cable has width zero. The padded binary sum is exact on every input.
One first-minimum selector chooses all fields of the winning directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalArgmin

open RouteRows PackedDeckScore ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {Move : Type*} {q d V E w m : ℕ}

/-- Total width of the cables marked active in a candidate route directory. -/
def score (x : Pins Move q d V E w → Bool) : ℕ :=
  ∑ i : Fin E, if x (.inr (.inl i)) then
    value (fun j => x (.inr (.inr (.inr (i,.inl j))))) else 0

private def masked (ij : Fin E × Fin w) : Expr (Pins Move q d V E w) :=
  .and (.input (.inr (.inl ij.1))) (.input (.inr (.inr (.inr (ij.1,.inl ij.2)))))

/-- Compute the full-width score from the active bit and the width bits of each row. -/
noncomputable def scoreFrame (Move : Type*) [Fintype Move] (q d V E w : ℕ) :
    Frame (Pins Move q d V E w) (Fin (sumBits (Fin E) w)) :=
  (sumFrame (Fin E) w).subst ((Frame.initial id).step masked)

open private zeros from OAI.Computability.BorderVNP.PackedDeckScoreSum

/-- Masking and summation count each active width once, including for an empty directory. -/
theorem scoreFrame_value [Fintype Move] (x : Pins Move q d V E w → Bool) :
    value ((scoreFrame Move q d V E w).eval x) = score x := by
  let mask := (Frame.initial id).step (masked : Fin E × Fin w → Expr (Pins Move q d V E w))
  have he : (scoreFrame Move q d V E w).eval x = (sumFrame (Fin E) w).eval (mask.eval x) :=
    funext fun i => Frame.subst_eval _ _ _ _
  rw [he,sumFrame_value,score]
  apply Finset.sum_congr rfl
  intro i _
  cases h : x (.inr (.inl i)) <;>
    simp [mask,masked,StatementCircuit.Expr.eval,h,zeros]

/-- Per-candidate cost for masking and summing all cable widths. -/
def scoreCost (E w : ℕ) : ℕ :=
  E*w*3 + 300*(E+1)*(2*Nat.clog 2 (E+1)+w+1)^3

theorem scoreFrame_size (Move : Type*) [Fintype Move] (q d V E w : ℕ) :
    (scoreFrame Move q d V E w).size ≤ scoreCost E w := by
  let b := Nat.clog 2 (E+1)
  have mask := Frame.step_size_le (Frame.initial id) (masked : Fin E × Fin w → Expr (Pins Move q d V E w))
    3 (fun _ => le_rfl)
  have pad : 2^b ≤ 2*(E+1) := (TeamSorting.padding_lt_twice (by omega : 0 < E+1)).le
  have hs := (sumFrame_size (Fin E) w).trans (queryCost_le ..)
  simp only [batchBits,sumBits,Fintype.card_fin,Fintype.card_unit,Nat.add_zero] at hs
  change (sumFrame (Fin E) w).size ≤ 2^b * (150*(b+(w+b)+1)^3) at hs
  have hs' : (sumFrame (Fin E) w).size ≤ 300*(E+1)*(2*b+w+1)^3 := by
    apply (hs.trans (Nat.mul_le_mul_right _ pad)).trans_eq
    ring
  simpa only [scoreFrame,Frame.subst_size,scoreCost,Frame.initial_size,zero_add,
    Fintype.card_prod,Fintype.card_fin,b] using Nat.add_le_add mask hs'

/-- All output bits, including vacant rows and stable endpoint pointers, are dispatched. -/
theorem pins_card (Move : Type*) [Fintype Move] (q d V E w : ℕ) :
    Fintype.card (Pins Move q d V E w) =
      E*(1+Fintype.card Move) + E + V*q*(90*(d+1)) + E*(3*w) := by
  simp [RouteRows.Pins,Shortening.PublicSegments.Raw,Shortening.PublicEndpoints.Inputs,
    Cover.AddressCircuit.ProductSlots,Cover.AddressCircuit.width,StackFrame.Slots]
  ring

/-- Selection cost on already generated candidate directories. It is linear
in the site and cable counts up to powers of the address and word widths. -/
def cost (Move : Type*) [Fintype Move] (m q d V E w : ℕ) : ℕ :=
  1 + m*scoreCost E w + m*((15*sumBits (Fin E) w+3)*m+1) +
    (m + Fintype.card (Pins Move q d V E w))*(4*m+1)

/-- The selector flags are exactly the first minimizing ordinal. The returned
directory is that same candidate on every wire. -/
theorem exists_frame (Move : Type*) [Fintype Move] (m q d V E w : ℕ) :
    ∃ f : Frame (Fin m × Pins Move q d V E w) (Fin m ⊕ Pins Move q d V E w),
      f.size ≤ cost Move m q d V E w ∧
      ∀ (x : Fin m × Pins Move q d V E w → Bool),
        let best := (List.finRange m).argmin (fun i => score (fun j => x (i,j)))
        (∀ i, f.eval x (.inl i) = true ↔ best = some i) ∧
        ∀ i, best = some i → ∀ j, f.eval x (.inr j) = x (i,j) := by
  let R := Pins Move q d V E w
  let W := sumBits (Fin E) w
  let lane (i : Fin m) : Frame (Fin m × R) (Fin W) :=
    (scoreFrame Move q d V E w).subst (Frame.initial (fun j => (i,j)))
  obtain ⟨p,hsize,heval⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin m => Fin W) lane
  let scores := p.select (fun ij : Fin m × Fin W => ⟨ij.1,ij.2⟩)
  let chosen := (PackedDeckChoice.firstMin m W).subst scores
  let emit : Fin m ⊕ R → Expr ((Fin m × R) ⊕ Fin m) := Sum.elim
    (fun i => .input (.inr i)) (fun j => PackedChoiceMux.read Sum.inr (fun i => .inl (i,j)))
  refine ⟨chosen.withInput.step emit,?_,?_⟩
  · have hl (i : Fin m) : (lane i).size ≤ scoreCost E w := by
      simpa [lane] using scoreFrame_size Move q d V E w
    have hp : p.size ≤ 1 + m*scoreCost E w := hsize.trans (Nat.add_le_add_left
      (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hl i)) _)
    have hc := Nat.add_le_add hp (PackedDeckChoice.firstMin_size m W)
    have hout := Frame.step_size_le chosen.withInput emit (4*m+1) (fun j => by
      cases j with
      | inl i => simp [emit,StatementCircuit.Expr.size]
      | inr j => exact PackedChoiceMux.read_size ..)
    simp only [Frame.withInput_size,chosen,Frame.subst_size,scores,Frame.select_size,
      Fintype.card_sum,Fintype.card_fin] at hout
    exact hout.trans (Nat.add_le_add_right hc _)
  · intro x best
    have hscore (i : Fin m) : value (fun j => scores.eval x (i,j)) = score (fun j => x (i,j)) := by
      have h := scoreFrame_value (fun j => x (i,j))
      apply Eq.trans _ h
      apply congrArg value
      funext j
      simp only [scores,Frame.select_eval,heval,lane,Frame.subst_eval]
      congr 1
      funext k
      exact Frame.initial_eval _ _ _
    have hchoice (i : Fin m) : chosen.eval x i = true ↔ best = some i := by
      simp only [chosen,Frame.subst_eval,PackedDeckChoice.firstMin_eval,funext hscore,best]
    refine ⟨fun i => by simpa [emit,StatementCircuit.Expr.eval] using hchoice i,?_⟩
    intro i hi j
    have unique (a : Fin m) : chosen.withInput.eval x (.inr a) = true ↔ a=i := by
      simp only [Frame.withInput_eval_inr,hchoice,hi,Option.some.injEq,eq_comm]
    simpa [emit] using PackedChoiceMux.read_eval Sum.inr (fun a : Fin m => Sum.inl (a,j))
      (chosen.withInput.eval x) i unique

/-- A positive candidate count always supplies a minimizing candidate and its
score is bounded by that of each competing directory. -/
theorem exists_minimum (hm : 0 < m) (x : Fin m × Pins Move q d V E w → Bool) :
    ∃ i : Fin m, (List.finRange m).argmin (fun a => score (fun j => x (a,j))) = some i ∧
      ∀ a, score (fun j => x (i,j)) ≤ score (fun j => x (a,j)) := by
  cases h : (List.finRange m).argmin (fun a => score (fun j => x (a,j))) with
  | none =>
    have z := congrArg List.length (List.argmin_eq_none.mp h)
    simp at z
    omega
  | some i =>
    exact ⟨i,rfl,fun a => (List.argmin_eq_some_iff.mp h).2.1 a (List.mem_finRange a)⟩

/-- Including the generation of every candidate's site, endpoint and move
rows, terminal rounding has linear gate count in the physical rows times a
fixed polynomial in the cover level, word width and row address width. -/
theorem whole_cost_le (Move : Type*) [Fintype Move] (N q Cs ks Cm km : ℕ) :
    ∃ G k : ℕ, ∀ d V E w : ℕ,
      1 + N*(1+V*Cs*(d+3)^ks +
        300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+90*q*(d+3)+1)^3 +
        (1+E*Cm*(d+3)^km)) + cost Move N q (d+2) V E w ≤
      (V+E+1)*G*(d+w+Nat.clog 2 (V+2*E+1)+3)^k := by
  let A := 2+Cs+600*(90*q+1)^3+Cm
  let H := 1+N*2403+N*(18*N+1)+(N+(1+Fintype.card Move)+1+90*q+3)*(4*N+1)
  let k := max 3 (max ks km)
  refine ⟨1+N*A+H,k,?_⟩
  intro d V E w
  let S := V+E+1
  let W := d+w+Nat.clog 2 (V+2*E+1)+3
  let B := W^k
  let U := S*B
  have hp : 0 < W := by dsimp [W]; omega
  have hS : 0 < S := by dsimp [S]; omega
  have hB : 0 < B := Nat.pow_pos hp
  have hu : 1 ≤ U := Nat.mul_pos hS hB
  have su : S ≤ U := Nat.le_mul_of_pos_right _ hB
  have bu : B ≤ U := Nat.le_mul_of_pos_left _ hS
  have wb : W ≤ B := Nat.le_self_pow (by dsimp [k]; omega) _
  have leB {a h : ℕ} (ha : a ≤ W) (hh : h ≤ k) : a^h ≤ B :=
    (Nat.pow_le_pow_left ha _).trans (Nat.pow_le_pow_right hp hh)
  have hd : d+3 ≤ W := by dsimp [W]; omega
  have hw : w ≤ W := by dsimp [W]; omega
  have hv : V ≤ S := by dsimp [S]; omega
  have he : E ≤ S := by dsimp [S]; omega
  have he1 : E+1 ≤ S := by dsimp [S]; omega
  have hrect : V+2*E+1 ≤ 2*S := by dsimp [S]; omega
  have logV := Nat.clog_mono_right 2 (show V+2*E ≤ V+2*E+1 by omega)
  have logE := Nat.clog_mono_right 2 (show E+1 ≤ V+2*E+1 by omega)
  have cubic {z c : ℕ} (h : z ≤ c*W) : z^3 ≤ c^3*B :=
    (Nat.pow_le_pow_left h 3).trans (by rw [mul_pow]; exact Nat.mul_le_mul_left _ (leB le_rfl (le_max_left ..)))
  have large : Nat.clog 2 (V+2*E)+w+90*q*(d+3)+1 ≤ (90*q+1)*W := by
    have hz : Nat.clog 2 (V+2*E)+w+1 ≤ W := by dsimp [W]; omega
    have hq := Nat.mul_le_mul_left (90*q) hd
    rw [Nat.add_mul,one_mul]
    omega
  have candidate : 1+V*Cs*(d+3)^ks +
      300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+90*q*(d+3)+1)^3 +
      (1+E*Cm*(d+3)^km) ≤ U*A := by
    have hs := leB hd ((le_max_left ks km).trans (le_max_right ..))
    have hm := leB hd ((le_max_right ks km).trans (le_max_right ..))
    calc
      _ ≤ U+S*Cs*B + 300*(2*S)*((90*q+1)^3*B) + (U+S*Cm*B) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu (Nat.mul_le_mul (Nat.mul_le_mul_right _ hv) hs))
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hrect) (cubic large)))
          (Nat.add_le_add hu (Nat.mul_le_mul (Nat.mul_le_mul_right _ he) hm))
      _ = _ := by dsimp [U,A]; ring
  have small : 2*Nat.clog 2 (E+1)+w+1 ≤ 2*W := by dsimp [W]; omega
  have sc : scoreCost E w ≤ U*2403 := by
    calc
      _ ≤ U*3 + 300*S*(2^3*B) := Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul he (hw.trans wb)))
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ he1) (cubic small))
      _ = _ := by dsimp [U]; ring
  have word : sumBits (Fin E) w ≤ U := by
    apply (le_trans _ (wb.trans bu))
    simp only [sumBits,Fintype.card_fin,W]
    omega
  have pick : N*((15*sumBits (Fin E) w+3)*N+1) ≤ U*(N*(18*N+1)) := by
    calc
      _ ≤ N*((15*U+3*U)*N+U) := Nat.mul_le_mul_left _ (Nat.add_le_add
        (Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul_left _ word) (Nat.le_mul_of_pos_right _ hu))) hu)
      _ = _ := by ring
  have cardBound : N + Fintype.card (Pins Move q (d+2) V E w) ≤
      U*(N+(1+Fintype.card Move)+1+90*q+3) := by
    rw [pins_card]
    have sites : V*q*(90*(d+2+1)) ≤ U*(90*q) := by
      calc
        _ = V*(d+3)*(90*q) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul hv (hd.trans wb))
    have widths : E*(3*w) ≤ U*3 := by
      calc
        _ = E*w*3 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul he (hw.trans wb))
    calc
      _ ≤ N*U + (U*(1+Fintype.card Move)+U+U*(90*q)+U*3) :=
        Nat.add_le_add (Nat.le_mul_of_pos_right _ hu) (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ (he.trans su)) (he.trans su)) sites) widths)
      _ = _ := by ring
  have chosen : cost Move N q (d+2) V E w ≤ U*H := by
    calc
      _ ≤ U + N*(U*2403) + U*(N*(18*N+1)) + (U*(N+(1+Fintype.card Move)+1+90*q+3))*(4*N+1) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hu (Nat.mul_le_mul_left _ sc)) pick)
          (Nat.mul_le_mul_right _ cardBound)
      _ = _ := by dsimp [H]; ring
  calc
    _ ≤ U+N*(U*A)+U*H := Nat.add_le_add (Nat.add_le_add hu (Nat.mul_le_mul_left _ candidate)) chosen
    _ = _ := by change S*B+N*(S*B*A)+S*B*H = S*(1+N*A+H)*B; ring

end PackedHistoryCircuit.TerminalArgmin

end BorderVNP
end Computability
end OAI
