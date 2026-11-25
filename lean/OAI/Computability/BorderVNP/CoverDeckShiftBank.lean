import OAI.Computability.BorderVNP.CoverDeckDigitFrames
import OAI.Computability.BorderVNP.PackedDeckScoreCost
import OAI.Computability.BorderVNP.PackedLookup

/-!
# Updating the bin counts after choosing a product-deck translation

The address multipliers compute the left-translated tile keys once. Every
relative bin then reads its candidate counts at these keys and adds them to
its previous counts at the original tiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedHistogram ParseBatchSort PackedDeckScore VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

private abbrev Tiles (q l : ℕ) := Fin q → Deck l
private abbrev Raw (B : Type*) (q l w : ℕ) := CountBits B q l w ⊕ Fin (keyWidth q l)
private abbrev Mid (B : Type*) (q l w : ℕ) := CountBits B q l w ⊕ (Tiles q l × Fin (keyWidth q l))

private def candidate {B : Type*} {q l w : ℕ} (b : B) (g : Tiles q l) (j : Fin w) :
    Expr (Mid B q l w) := .input (.inl (true,b,g,j))

private def request {B : Type*} {q l w : ℕ} (g : Tiles q l) (j : Fin (keyWidth q l)) :
    Expr (Mid B q l w) := .input (.inr (g,j))

private noncomputable def reader {B : Type*} [Fintype B] (q l w : ℕ) (b : B) :
    Frame (Mid B q l w) (Tiles q l × Fin w) :=
  PackedLookup.lookup (layout (Tiles q l) (Tiles q l)) (productKey q l) (candidate b) request

private theorem reader_size {B : Type*} [Fintype B] (q l w : ℕ) (b : B) :
    (reader q l w b).size ≤ queryCost (batchBits (Tiles q l) (Tiles q l)) (keyWidth q l) w := by
  apply (queries_size _ _ _ _ 1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)).trans
  simp [queryCost,batchBits]

private theorem add_mod {σ : Type*} {w : ℕ} (x : σ → Bool) (a b : Fin w → Expr σ) :
    wordValue x (addWord a b) = (wordValue x a + wordValue x b) % 2^w := by
  have h := sumWord_value_carry x false a b
  simp only [Bool.toNat_false,Nat.add_zero] at h
  rw [← h,Nat.mul_comm _ (2^w),Nat.mul_add_mod]
  exact (Nat.mod_eq_of_lt (value_lt _)).symm

private noncomputable def rawCost (B : Type*) [Fintype B] (q l w C e : ℕ) :=
  let V := Fintype.card (Tiles q l)
  (1+(V*q)*(3*width l+C*(l+1)^e)) +
    (1+Fintype.card B * queryCost (batchBits (Tiles q l) (Tiles q l)) (keyWidth q l) w) +
    (Fintype.card B*(V*w))*(16*w+22)

private theorem raw_frames :
    ∃ C e : ℕ, ∀ (B : Type*) [Fintype B] (q l w : ℕ),
      ∃ f : Frame (Raw B q l w) (B × Tiles q l × Fin w),
        f.size ≤ rawCost B q l w C e ∧
        ∀ (z : CountBits B q l w → Bool) (h : Tiles q l) (b : B) (g : Tiles q l),
          value (fun j => f.eval (Sum.elim z (keyWord q l h)) (b,g,j)) =
            (physicalCount z false b g + physicalCount z true b (h*g)) % 2^w := by
  obtain ⟨C,e,translate⟩ := translationKeys_frames
  refine ⟨C,e,?_⟩
  intro B inst q l w
  obtain ⟨keys,hkeys,evalKeys⟩ := translate q l 1
  let lift : Frame (Raw B q l w) (Fin 1 × Fin (keyWidth q l)) := Frame.initial (fun p => .inr p.2)
  let shifted := (keys.subst lift).select (fun p : Tiles q l × Fin (keyWidth q l) => (0,p))
  let start : Frame (Raw B q l w) (Mid B q l w) := Crossing.parallelFrame (Frame.initial Sum.inl) shifted
  obtain ⟨reads,hs,he⟩ := Crossing.exists_parallelFrames
    (out := fun _ : B => Tiles q l × Fin w) (reader q l w)
  let bank := reads.withInput.subst start
  let old (b : B) (g : Tiles q l) (j : Fin w) : Expr (Mid B q l w ⊕ (Σ _ : B, Tiles q l × Fin w)) :=
    .input (.inl (.inl (false,b,g,j)))
  let moved (b : B) (g : Tiles q l) (j : Fin w) : Expr (Mid B q l w ⊕ (Σ _ : B, Tiles q l × Fin w)) :=
    .input (.inr ⟨b,(g,j)⟩)
  let sums (p : B × Tiles q l × Fin w) := addWord (old p.1 p.2.1) (moved p.1 p.2.1) p.2.2
  refine ⟨bank.step sums,?_,?_⟩
  · have hstart : start.size ≤ 1+(Fintype.card (Tiles q l)*q)*(3*width l+C*(l+1)^e) := by
      simpa [start,shifted,lift] using hkeys
    have hr := Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun b _ => reader_size q l w b)
    have hreads : reads.size ≤ 1+Fintype.card B * queryCost (batchBits (Tiles q l) (Tiles q l)) (keyWidth q l) w := by
      simpa using hs.trans (Nat.add_le_add_left hr 1)
    have hb := Nat.add_le_add hstart hreads
    rw [show start.size+reads.size = bank.size by simp [bank]] at hb
    have hadd := Frame.step_size_le bank sums (16*w+22) (fun p =>
      sumWord_size_le false (old p.1 p.2.1) (moved p.1 p.2.1) 1 (fun _ => le_rfl) (fun _ => le_rfl) p.2.2)
    simpa [rawCost,Fintype.card_prod] using hadd.trans (Nat.add_le_add_right hb _)
  · intro z h b g
    let x : Raw B q l w → Bool := Sum.elim z (keyWord q l h)
    let y : Mid B q l w → Bool := Sum.elim z (fun p => keyWord q l (h*p.1) p.2)
    have hl : lift.eval x = fun p => keyWord q l h p.2 := by
      funext i; exact Frame.initial_eval _ _ _
    have hstart : start.eval x = y := by
      funext p
      rcases p with a | ⟨v,j⟩
      · simp [start,x,y]
      · simpa only [start,Crossing.parallelFrame_eval_inr,shifted,Frame.select_eval,Frame.subst_eval,hl,y,
          Sum.elim_inr] using evalKeys (fun _ => h) 0 v j
    have hread (v : Tiles q l) (j : Fin w) : (reader q l w b).eval y (v,j) = z (true,b,h*v,j) :=
      PackedLookup.lookup_bits (layout (Tiles q l) (Tiles q l)) (productKey q l) (candidate b)
        request y v (h*v) rfl j
    have ha : wordValue (bank.eval x) (old b g) = physicalCount z false b g := by
      apply congrArg value
      funext j
      simp [bank,old,hstart,y,StatementCircuit.Expr.eval]
    have hb : wordValue (bank.eval x) (moved b g) = physicalCount z true b (h*g) := by
      apply congrArg value
      funext j
      simp only [bank,moved,StatementCircuit.Expr.eval,Frame.subst_eval,hstart,Frame.withInput_eval_inr,
        he,hread]
    change value (fun j => (bank.step sums).eval x (b,g,j)) = _
    simp only [Frame.step_eval]
    exact (add_mod (bank.eval x) (old b g) (moved b g)).trans (by rw [ha,hb])

private theorem rawCost_uniform (B : Type*) [Fintype B] (q C e : ℕ) :
    ∃ D p : ℕ, ∀ l w : ℕ, rawCost B q l w C e ≤ Fintype.card (Tiles q l)*D*(l+w+1)^p := by
  let A := 180*q+2
  let b := Fintype.card B
  let p := e+3
  let D := 2 + q*(90+C) + b*600*A^3 + b*38
  refine ⟨D,p,?_⟩
  intro l w
  let V := Fintype.card (Tiles q l)
  let S := l+w+1
  let k := keyWidth q l
  let T := batchBits (Tiles q l) (Tiles q l)
  let P := S^p
  have hv : 1 ≤ V := Fintype.card_pos
  have hS : 1 ≤ S := Nat.succ_pos _
  have hP (i : ℕ) (hi : i ≤ p) : S^i ≤ P := Nat.pow_le_pow_right hS hi
  have hSP : S ≤ P := by simpa only [pow_one] using hP 1 (by dsimp [p]; omega)
  have hVP : 1 ≤ V*P := Nat.mul_pos hv (hS.trans hSP)
  have hk : k ≤ (90*q)*S := by
    change q*(30*(l+1)*3) ≤ _
    calc
      _ = (90*q)*(l+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by dsimp [S]; omega)
  have hV : V ≤ 2^k := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (productKey q l).injective
  have hT : T ≤ k+1 := by
    apply Nat.clog_le_of_le_pow
    change V+V ≤ _
    rw [pow_succ]; omega
  have hpad : 2^T ≤ 4*V := by
    have h := (layout_size (Tiles q l) (Tiles q l) (Nat.add_pos_left hv _)).le
    change 2^T ≤ 2*(V+V) at h
    omega
  have hW : w+1 ≤ S := by dsimp [S]; omega
  have hwidth : T+k+w+1 ≤ A*S := by
    have he : A*S = 2*((90*q)*S)+2*S := by unfold A; ring
    omega
  have hq : queryCost T k w ≤ (4*V)*(150*(A^3*P)) := by
    apply (queryCost_le ..).trans
    gcongr
    exact (Nat.pow_le_pow_left hwidth 3).trans ((mul_pow ..).trans_le
      (Nat.mul_le_mul_left _ (hP 3 (by dsimp [p]; omega))))
  have hw : width l ≤ 30*P := Nat.mul_le_mul_left _ ((show l+1 ≤ S by dsimp [S]; omega).trans hSP)
  have hc : (l+1)^e ≤ P := (Nat.pow_le_pow_left (show l+1 ≤ S by dsimp [S]; omega) e).trans
    (hP e (by dsimp [p]; omega))
  have ha : w*(16*w+22) ≤ 38*P := by
    calc
      _ ≤ S*(16*S+22*S) := by gcongr <;> omega
      _ = 38*S^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hP 2 (by dsimp [p]; omega))
  unfold rawCost
  change 1+(V*q)*(3*width l+C*(l+1)^e)+(1+b*queryCost T k w)+(b*(V*w))*(16*w+22) ≤ _
  calc
    _ = 1+(V*q)*(3*width l+C*(l+1)^e)+(1+b*queryCost T k w)+(b*V)*(w*(16*w+22)) := by ring
    _ ≤ V*P+(V*q)*(3*(30*P)+C*P)+(V*P+b*((4*V)*(150*(A^3*P))))+(b*V)*(38*P) := by gcongr
    _ = V*D*P := by unfold D; ring

/-- Apply the selected left translation to all candidate bins and add the
previous bin counts at the original tiles. The bit-level update computes the
sum modulo its width for arbitrary inputs, and its gates cost one full-cover
volume times a polynomial in depth and bit width. -/
theorem shiftBank_frames (B : Type*) [Fintype B] (q : ℕ) :
    ∃ D p : ℕ, ∀ l w : ℕ, ∃ f :
      Frame (CountBits B q l w ⊕ Fin (keyWidth q l)) (B × (Fin q → Deck l) × Fin w),
      f.size ≤ Fintype.card (Fin q → Deck l) * D * (l+w+1)^p ∧
      ∀ (z : CountBits B q l w → Bool) (h : Fin q → Deck l) (b : B) (g : Fin q → Deck l),
        value (fun j => f.eval (Sum.elim z (keyWord q l h)) (b,g,j)) =
          (physicalCount z false b g + physicalCount z true b (h*g)) % 2^w := by
  obtain ⟨C,e,make⟩ := raw_frames
  obtain ⟨D,p,bound⟩ := rawCost_uniform B q C e
  refine ⟨D,p,?_⟩
  intro l w
  obtain ⟨f,hf,he⟩ := make B q l w
  exact ⟨f,hf.trans (bound l w),he⟩

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
