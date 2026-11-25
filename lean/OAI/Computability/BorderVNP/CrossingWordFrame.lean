import OAI.Computability.BorderVNP.CrossingWordAmplitude
import OAI.Computability.BorderVNP.CrossingWordPhase
import OAI.Computability.BorderVNP.CrossingCoefficientFrame

/-!
# Boolean signed verifier for an entire fermionic word

The verifier receives a mask of derivative orders and two endpoint occupation masks.
Each row has a binary packet. Every unused row requires the canonical zero packet.
All local tests are polynomial-size Boolean circuits. Their products and the transitions
on the occupation masks are composed as shared gate fragments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.WordFrame

open Lemmata.FockCircuits.FiniteIdentity (Index)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open CoefficientFrame (times times_value times_size)

private def mismatch {L : ℕ} (k : Fin L) : Expr (Inputs L) :=
  let i := Expr.input (.inl (.inr (.inl k)))
  let j := Expr.input (.inl (.inr (.inr k)))
  Expr.mux i (.not j) j

private noncomputable def finish (L : ℕ) : Frame (Inputs L) Bool :=
  (Frame.initial id).step fun neg =>
    if neg then .const false else .not (Expr.disjoin (List.ofFn (mismatch (L := L))))

private theorem finish_value {L : ℕ} (A I J : Index L) (x : Witnesses L → Bool) :
    CoefficientFrame.value ((finish L).eval (pack A.val I.val J.val x)) = if J.val = I.val then 1 else 0 := by
  have hinput : (Frame.initial (id : Inputs L → Inputs L)).eval (pack A.val I.val J.val x) =
      pack A.val I.val J.val x := by ext; simp
  have htest (k : Fin L) : (mismatch k).eval (pack A.val I.val J.val x) = decide ((k.val ∈ I.val) ≠ (k.val ∈ J.val)) := by
    by_cases hi : k.val ∈ I.val <;> by_cases hj : k.val ∈ J.val <;> simp [mismatch, Expr.eval, pack, *]
  have hdis : (Expr.disjoin (List.ofFn (mismatch (L := L)))).eval (pack A.val I.val J.val x) = decide (J.val ≠ I.val) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Expr.eval_disjoin_true, List.mem_ofFn, exists_exists_eq_and, htest, decide_eq_true_eq]
    constructor
    · rintro ⟨k,hk⟩ he
      exact hk (by rw [he])
    · intro he
      by_contra! hn
      apply he
      ext j
      by_cases hj : j < L
      · exact iff_of_eq (hn ⟨j,hj⟩).symm
      · have hI : j ∉ I.val := fun h => hj (Finset.mem_range.mp (Finset.mem_powerset.mp I.property h))
        have hJ : j ∉ J.val := fun h => hj (Finset.mem_range.mp (Finset.mem_powerset.mp J.property h))
        simp [hI,hJ]
  simp only [CoefficientFrame.value, finish, Frame.step_eval, hinput, ite_true, Bool.false_eq_true,
    ite_false, Expr.eval, hdis, Bool.toNat_false, Nat.cast_zero, sub_zero]
  by_cases he : J.val = I.val <;> simp [he]

private theorem finish_size (L : ℕ) : (finish L).size ≤ 20 * (L+1) := by
  apply (Frame.step_size_le (Frame.initial id) _ (10*(L+1)) ?_).trans (by simp; omega)
  intro neg
  cases neg with
  | true => change 1 ≤ _; omega
  | false =>
    change (Expr.disjoin (List.ofFn (mismatch (L := L)))).size + 1 ≤ _
    have h := Expr.size_disjoin_le (List.ofFn (mismatch (L := L))) 9 (by
      intro e he
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
      simp [mismatch, Expr.mux, Expr.size])
    rw [List.length_ofFn] at h
    omega

private noncomputable def build (dual : Bool) (L : ℕ) : List ℕ → Frame (Inputs L) Bool
  | [] => finish L
  | m :: ms => if h : m < L then
      times (times (phase ⟨m,h⟩ ms.toFinset) (amplitude dual ⟨m,h⟩))
        ((build dual L ms).subst (after ⟨m,h⟩))
    else build dual L ms

/-- The signed field-word verifier. All available derivative orders are scanned in order. -/
noncomputable def frame (dual : Bool) (L : ℕ) : Frame (Inputs L) Bool :=
  build dual L (List.range L)

private theorem value_flags (z : ℤ) (h : z = -1 ∨ z = 0 ∨ z = 1) :
    CoefficientFrame.value (flag z) = z := by rcases h with rfl | rfl | rfl <;> rfl

private theorem sign_cases (n : ℕ) : (-1 : ℤ)^n = -1 ∨ (-1 : ℤ)^n = 1 := by
  rw [neg_one_pow_eq_ite]; split_ifs <;> simp

private theorem phase_cases {L : ℕ} (m : Fin L) (T A I J : Finset ℕ) (g : Padded.Packet L) :
    phaseValue m T A I J g = -1 ∨ phaseValue m T A I J g = 0 ∨ phaseValue m T A I J g = 1 := by
  unfold phaseValue insertionSign
  split_ifs <;> norm_num
  · rw [← pow_add]; exact sign_cases _
  · exact sign_cases _

private theorem amplitude_cases {L : ℕ} (dual : Bool) (m : Fin L) (A I J : Finset ℕ) (g : Padded.Packet L) :
    amplitudeValue dual m A I J g = -1 ∨ amplitudeValue dual m A I J g = 0 ∨ amplitudeValue dual m A I J g = 1 := by
  unfold amplitudeValue
  split_ifs <;> first | exact signedGuess_values _ _ | norm_num

private theorem local_product {L : ℕ} (dual : Bool) (m : Fin L) (ms : List ℕ) (hn : ms.Nodup)
    (A I J : Finset ℕ) (g : Padded.Packet L) :
    phaseValue m ms.toFinset A I J g * amplitudeValue dual m A I J g =
      Padded.localWeight dual (decide (m.val ∈ A)) m (ms.filter (· ∈ A)).length g I J := by
  have hs : A.filter (· ∈ ms.toFinset) = (ms.filter (· ∈ A)).toFinset := by ext; simp [and_comm]
  have hl : remaining ms.toFinset A = (ms.filter (· ∈ A)).length :=
    (congrArg Finset.card hs).trans (List.toFinset_card_of_nodup (hn.filter _))
  by_cases hm : m.val ∈ A <;> simp [phaseValue, amplitudeValue, Padded.localWeight, hm, hl]

private def indexed {L : ℕ} (ms : List ℕ) (h : ∀ m ∈ ms, m < L) (x : Witnesses L → Bool)
    (i : Fin ms.length) : Padded.Packet L := packet x ⟨ms[i], h _ (List.getElem_mem ..)⟩

private theorem build_eval {L : ℕ} (dual : Bool) (ms : List ℕ) (hn : ms.Nodup)
    (h : ∀ m ∈ ms, m < L) (A I J : Index L) (x : Witnesses L → Bool) :
    CoefficientFrame.value ((build dual L ms).eval (pack A.val I.val J.val x)) =
      Padded.value dual A.val ms (indexed ms h x) I.val J.val := by
  induction ms generalizing I J with
  | nil => exact finish_value A I J x
  | cons m ms ih =>
    let j : Fin L := ⟨m,h m List.mem_cons_self⟩
    let g := packet x j
    let ij := Padded.next (decide (m ∈ A.val)) g I.val J.val
    have hs : ij.1 ⊆ I.val ∧ ij.2 ⊆ J.val := by
      dsimp only [ij, Padded.next]
      split_ifs <;> simp [Finset.erase_subset]
    let i' : Index L := ⟨ij.1, Finset.mem_powerset.mpr (hs.1.trans (Finset.mem_powerset.mp I.property))⟩
    let j' : Index L := ⟨ij.2, Finset.mem_powerset.mpr (hs.2.trans (Finset.mem_powerset.mp J.property))⟩
    have htail (a) (ha : a ∈ ms) := h a (List.mem_cons_of_mem _ ha)
    have hr := ih hn.of_cons htail i' j'
    rw [build, dite_eq_left j.isLt, times_value, times_value]
    have hsub : ((build dual L ms).subst (after j)).eval (pack A.val I.val J.val x) =
        (build dual L ms).eval (pack A.val i'.val j'.val x) := by
      funext b
      rw [Frame.subst_eval, after_eval]
    rw [hsub]
    rw [show (phase j ms.toFinset).eval (pack A.val I.val J.val x) =
        flag (phaseValue j ms.toFinset A.val I.val J.val g) from funext (phase_eval j _ A I J x)]
    rw [show (amplitude dual j).eval (pack A.val I.val J.val x) =
        flag (amplitudeValue dual j A.val I.val J.val g) from funext (amplitude_eval dual j _ _ _ x)]
    rw [value_flags _ (phase_cases ..), value_flags _ (amplitude_cases ..), local_product _ _ _ hn.of_cons]
    change _ * CoefficientFrame.value ((build dual L ms).eval (pack A.val i'.val j'.val x)) = _
    rw [hr]
    rfl

private theorem full_word {L : ℕ} (dual : Bool) (A : Index L) :
    Padded.word (L := L) dual A.val (List.range L) = if dual then dualWord A else derivativeWord A := by
  let row := (List.range L).filter (· ∈ A.val)
  have hs : row.toFinset = A.val := by
    ext i
    have hi (h : i ∈ A.val) := Finset.mem_range.mp (Finset.mem_powerset.mp A.property h)
    simpa [row] using hi
  have hr : row = A.val.sort := by
    rw [← hs]
    symm
    exact (List.toFinset_sort _ (List.nodup_range.filter _)).mpr
      (((List.sortedLT_range L).pairwise.imp (fun h => h.le)).filter _)
  cases dual <;> change row.map _ = _ <;> rw [hr] <;> rfl

/-- The fixed-width Boolean verifier sums to the actual operator entry in either flavor. -/
theorem frame_sum {L : ℕ} (dual : Bool) (A I J : Index L) :
    (∑ x : Witnesses L → Bool, CoefficientFrame.value ((frame dual L).eval (pack A.val I.val J.val x))) =
      let s := if dual then dualWord A else derivativeWord A
      ∑ p : ModePath L s.length, modeWeight s p I.val J.val := by
  let e := (packetEquiv L).trans ((finCongr (List.length_range (n := L)).symm).arrowCongr
    (Equiv.refl (Padded.Packet L)))
  let f (gs : Fin (List.range L).length → Padded.Packet L) := Padded.value dual A.val (List.range L) gs I.val J.val
  calc
    _ = ∑ gs, f gs := by
      apply Fintype.sum_equiv e
      intro x
      rw [frame, build_eval dual (List.range L) List.nodup_range (fun _ hm => List.mem_range.mp hm)]
      apply congrArg (fun p => f p)
      funext i
      simp [indexed, e, packetEquiv, Equiv.arrowCongr, packet]
      exact ⟨rfl,rfl,rfl⟩
    _ = _ := (Padded.value_sum dual A.val (List.range L) (fun _ hm => List.mem_range.mp hm) I.val J.val).trans
      (congrArg (fun s : List ((Fin L → ℤ) × (Fin L → ℤ)) =>
        ∑ p : ModePath L s.length, modeWeight s p I.val J.val) (full_word dual A))

private theorem build_size (dual : Bool) (L : ℕ) (ms : List ℕ) :
    (build dual L ms).size ≤ 20 * (L+1) + ms.length * (450 * (L+1)^3) := by
  induction ms with
  | nil => simpa [build] using finish_size L
  | cons m ms ih =>
    rw [build]
    split_ifs with hm
    · let j : Fin L := ⟨m,hm⟩
      have ho := times_size (times (phase j ms.toFinset) (amplitude dual j)) ((build dual L ms).subst (after j))
      have hp := times_size (phase j ms.toFinset) (amplitude dual j)
      have ha := amplitude_size dual j
      have he := phase_size j ms.toFinset
      have hx := after_size j
      rw [Frame.subst_size] at ho
      simp only [Inputs, Masks, Witnesses, Fields, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_unit, Padded.width] at hx
      simp only [List.length_cons, Nat.add_mul, one_mul]
      nlinarith
    · simp only [List.length_cons, Nat.add_mul, one_mul]
      omega

/-- A single polynomial gate bound for all source and endpoint masks. -/
theorem frame_size (dual : Bool) (L : ℕ) : (frame dual L).size ≤ (L+2)^20 := by
  have h := build_size dual L (List.range L)
  rw [List.length_range] at h
  apply h.trans
  have h₂ : 2^9 ≤ (L+2)^9 := Nat.pow_le_pow_left (by omega) _
  have h₃ : (L+1)^4 ≤ (L+2)^4 := Nat.pow_le_pow_left (by omega) _
  have hd : (L+2)^13 ≤ (L+2)^20 := Nat.pow_le_pow_right (by omega) (by decide)
  apply le_trans _ hd
  calc
    _ ≤ 470 * (L+1)^4 := by nlinarith
    _ ≤ (L+2)^9 * (L+2)^4 := Nat.mul_le_mul (by norm_num at h₂; omega) h₃
    _ = _ := by rw [← pow_add]

end Crossing.Signed.WordFrame

end BorderVNP
end Computability
end OAI
