import OAI.ThreeFlat.Diagonal.TraceMemoryControl
import OAI.ThreeFlat.Diagonal.TraceMemoryCircuit

namespace OAI
/-! # A single two-track sort template controlled by public row coordinates -/

namespace ThreeFlat.Diagonal.TraceMemoryCircuit

open Computability.VPVNP BurstRAM RAMSort RAMSerialization
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSortSite TraceSlots TraceWords

variable {d w : ℕ}

abbrev ControlledPort (d w : ℕ) := Port d w ⊕ MemoryControl d w

private def strideControl (s : Stage (1+d)) (i : Fin 2) : MemoryControl d w :=
  .inl (⟨s.stride,by have := s.stride_lt; have := s.phase_le; omega⟩,i)

private def phaseControl (s : Stage (1+d)) (i : Fin 2) : MemoryControl d w :=
  .inl (⟨s.phase,by have := s.phase_le; omega⟩,i)

theorem lowOutput_eq_bits (v : Fin (2^d)) (s : Stage (1+d)) (i : Fin 2) :
    lowOutput s v i = (controlsAt (w := w) v (strideControl (w := w) s i) == controlsAt (w := w) v (phaseControl (w := w) s i)) := by
  simpa [lowOutput,controlsAt,strideControl,phaseControl,Nat.mul_comm] using
    polarity_eq_bits s.phase s.stride (v.val*2+i.val)

private def chooseLow (s : Stage (1+d)) (i : Fin 2) : Expr (ControlledPort d w ⊕ Live w) :=
  same (.input (.inl (.inr (strideControl (w := w) s i)))) (.input (.inl (.inr (phaseControl (w := w) s i))))

def controlVal (x : Port d w → Bool) (v : Fin (2^d)) : ControlledPort d w → Bool :=
  Sum.elim x (controlsAt (w := w) v)

/-- The current register-pair rows always use their relative outgoing and
incoming ports. Their absolute addresses are resolved by the XOR wiring. -/
private def stageSend (s : Stage (1+d)) (h : 1 ≤ s.stride) (own : Bool) (i : Fin 2) :
    SlotAddr w (ControlledPort d w ⊕ Live w) :=
  fun f j => .inl (.inl (exchange (RAMLayout.layerEquiv d ((crossStageEquiv 1 d).symm ⟨s,h⟩)) own i f j))

private def stageOther (s : Stage (1+d)) (i : Fin 2) : SlotAddr w (ControlledPort d w ⊕ Live w) :=
  if h : 1 ≤ s.stride then stageSend s h false i
  else ownAddr ⟨partner s.stride i.val, partner_lt i.isLt (Nat.lt_of_not_ge h)⟩

private def uniformExpr (s : Stage (1+d)) : Live w → Expr (ControlledPort d w ⊕ Live w)
  | .inl (i,f,j) => Expr.mux (chooseLow s i)
      (pick true (ownAddr i) (stageOther s i) f j) (pick false (ownAddr i) (stageOther s i) f j)
  | .inr _ => (Expr.input (.inr (.inr ()))).and
      (if h : 1 ≤ s.stride then allBits fun i => eqPort (ownAddr i) (stageSend s h true i)
       else .const true)

noncomputable def uniformAdvance (frame : Frame (ControlledPort d w) (Live w))
    (s : Stage (1+d)) : Frame (ControlledPort d w) (Live w) :=
  frame.withInput.step (uniformExpr s)

theorem uniformAdvance_eval (u : Frame (ControlledPort d w) (Live w)) (b : Frame (Port d w) (Live w))
    (s : Stage (1+d)) (v : Fin (2^d)) (x : Port d w → Bool)
    (he : u.eval (controlVal x v) = b.eval x) :
    (uniformAdvance u s).eval (controlVal x v) = (advance b (stagePins v) s v).eval x := by
  let a := u.withInput.eval (controlVal x v)
  let z := b.withInput.eval x
  have hx (i f j) : a (ownAddr i f j) = z (ownAddr i f j) := by
    simp [a,z,ownAddr,he]
  have hown (h i f j) : a (stageSend s h true i f j) = z (sendAddr (stagePins v) s h v i f j) := by
    simp [a,z,stageSend,sendAddr,controlVal,stagePins]
  have hother (i f j) : a (stageOther s i f j) =
      z (other s v (sendAddr (stagePins v) s) ownAddr i f j) := by
    by_cases h : 1 ≤ s.stride
    · have hn : sourceSite s h v ≠ v := by rw [sourceSite_eq_physical]; exact RAMLayout.Layer.partner_ne _ _
      simp [stageOther,other,h,stageSend,sendAddr,stagePins,hn,a,z,controlVal]
    · simpa [stageOther,other,h] using hx (⟨_,partner_lt i.isLt (Nat.lt_of_not_ge h)⟩ : Fin 2) f j
  funext q
  rcases q with ⟨i,f,j⟩ | ⟨⟩
  · simp only [uniformAdvance,advance,Frame.step_eval,uniformExpr,stepExpr,Expr.eval_mux]
    change (if (chooseLow s i).eval a then _ else _) = _
    have eq : (chooseLow s i).eval a = lowOutput s v i := by
      rw [lowOutput_eq_bits (w := w) v s i]
      apply Bool.eq_iff_iff.mpr
      simp [chooseLow,same_true,a,controlVal,Expr.eval]
    rw [eq]
    cases h : lowOutput s v i <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true] using pick_congr (hx i) (hother i) _ f j
  · apply Bool.eq_iff_iff.mpr
    simp only [uniformAdvance,advance,Frame.step_eval,uniformExpr,stepExpr,Expr.eval,Bool.and_eq_true,
      Frame.withInput_eval_inr, he]
    by_cases h : 1 ≤ s.stride
    · simp only [dite_eq_left h, allBits_true]
      exact and_congr_right fun _ => forall_congr' fun i =>
        iff_of_eq (congrArg (· = true) (eqPort_congr (hx i) (hown h i)))
    · simp [h,Expr.eval]

noncomputable def uniformRun :
    List (Stage (1+d)) → Frame (ControlledPort d w) (Live w) → Frame (ControlledPort d w) (Live w)
  | [], b => b
  | s :: ss, b => uniformRun ss (uniformAdvance b s)

theorem uniformRun_eval (ss : List (Stage (1+d))) (v : Fin (2^d)) (x : Port d w → Bool)
    (u : Frame (ControlledPort d w) (Live w)) (b : Frame (Port d w) (Live w))
    (he : u.eval (controlVal x v) = b.eval x) :
    (uniformRun ss u).eval (controlVal x v) = (run (stagePins v) v ss b).eval x := by
  induction ss generalizing u b with
  | nil => exact he
  | cons s ss ih => exact ih _ _ (uniformAdvance_eval u b s v x he)

theorem uniformAdvance_size (frame : Frame (ControlledPort d w) (Live w)) (s : Stage (1+d)) :
    (uniformAdvance frame s).size ≤ frame.size + (14*w+1)*(1030*(w+1)) := by
  have hb (i : Live w) : (uniformExpr (w := w) s i).size ≤ 1030*(w+1) := by
    rcases i with ⟨i,f,j⟩ | ⟨⟩
    · have h₁ := pick_size true (ownAddr i) (stageOther (w := w) s i) f j
      have h₂ := pick_size false (ownAddr i) (stageOther (w := w) s i) f j
      simp only [uniformExpr, Expr.mux, Expr.size, chooseLow, same_size]
      omega
    · by_cases h : 1 ≤ s.stride
      · have z := allBits_size_le (fun i : Fin 2 => eqPort (ownAddr i) (stageSend (w := w) s h true i))
          (s := 80*(w+1)) (fun _ => eqPort_size _ _)
        simp only [uniformExpr,dite_eq_left h,Expr.size]
        omega
      · simp only [uniformExpr,dite_eq_right h,Expr.size]
        omega
  have card : Fintype.card (Live w) = 14*w+1 := by
    simp only [Live,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit]
    omega
  have h := frame.withInput.step_size_le (uniformExpr s) _ hb
  rw [card,Frame.withInput_size] at h
  exact h

theorem uniformRun_size (ss : List (Stage (1+d))) (frame : Frame (ControlledPort d w) (Live w)) :
    (uniformRun ss frame).size ≤ frame.size + ss.length*((14*w+1)*(1030*(w+1))) := by
  induction ss generalizing frame with
  | nil => simp [uniformRun]
  | cons s ss ih =>
    have ht := uniformAdvance_size frame s
    have h := ih (uniformAdvance frame s)
    rw [List.length_cons, Nat.succ_mul]
    exact h.trans (by omega)

end ThreeFlat.Diagonal.TraceMemoryCircuit

end OAI
