import OAI.Computability.NearSquareRoot.FixedCandidateCRTDirectory
import OAI.Computability.NearSquareRoot.FixedCandidateCRTNative

/-! # Coverage, size and effective native-seed bounds for active CRT batches -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTDispatch
open IntegerMultiplication Code Staff Strip Controlled CRTTable

def low (t : Tally) : Tally := tally (t.length/16)

theorem low_poly : Poly low := by
  let r : Regime Tally := ⟨size,send,Dom.base _⟩
  have n : Realizes r List.length := by
    change Poly (fun t : Tally => tally t.length)
    simpa only [recover_tally] using (Code.Poly.identity (X := Tally))
  exact n.dividing (Realizes.fix 16)

theorem range_iff {d : ℕ} (cap β j : ℕ) (w : Fin d → ℕ) (z : Fin d) :
    (∃ i, selectBlock cap β j w i = z) ↔ z.val/cap = β ∧ j < w z := by
  rw [← mem_activeBlocks]
  exact List.mem_iff_get.symm

theorem selected_count {d cap : ℕ} (pos : 0 < cap) (β j : ℕ) (w : Fin d → ℕ) :
    (activeBlocks cap β j w).length ≤ cap := by
  let sel := selectBlock cap β j w
  let slot (q : Fin (activeBlocks cap β j w).length) : Fin cap := ⟨(sel q).val % cap,Nat.mod_lt _ pos⟩
  have same (q : Fin (activeBlocks cap β j w).length) : (sel q).val / cap = β :=
    ((range_iff _ _ _ _ _).mp ⟨q,rfl⟩).1
  have inj : Function.Injective slot := by
    intro q s eq
    apply sel.injective
    apply Fin.ext
    have m : (sel q).val % cap = (sel s).val % cap := congrArg Fin.val eq
    calc
      _ = cap*((sel q).val/cap)+(sel q).val%cap := (Nat.div_add_mod ..).symm
      _ = cap*((sel s).val/cap)+(sel s).val%cap := by rw [same q,same s,m]
      _ = _ := Nat.div_add_mod ..
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective slot inj

noncomputable def which (d depth cap : ℕ) (r : TargetIndex d depth) :=
  ((targetRank d depth).symm r).val/cap

theorem which_lt {d depth k : ℕ} (pos : 0 < Cap k) (r : TargetIndex d depth) :
    which d depth (Cap k) r < batchCount d k 4 (CRTBudget.stride k) := by
  let ord := (targetRank d depth).symm r
  have sz : (targetOrder d depth).length ≤ d := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (fun i => targetAxis d depth (targetRank d depth i))
      ((targetAxis_injective d depth).comp (targetRank d depth).injective)
  exact ((batchAddress (j := 4) (g := CRTBudget.stride k) pos) (⟨ord.val,ord.isLt.trans_le sz⟩ : Fin d)).1.isLt

variable {box : List (ℕ × ℕ)} {k depth j β : ℕ}

noncomputable abbrev selection (box : List (ℕ × ℕ)) (depth k j β : ℕ) :=
  selectBlock (Cap k) β j (targetWidth box depth)

theorem selection_wide (q) : j < axisWidth box (Native.Chosen (selection box depth k j β) q) :=
  ((range_iff (Cap k) β j (targetWidth box depth) _).mp ⟨q,rfl⟩).2

theorem selection_batch (q) : which box.length depth (Cap k)
    (targetRank _ _ (selection box depth k j β q)) = β := by
  simpa [which] using ((range_iff (Cap k) β j (targetWidth box depth) _).mp ⟨q,rfl⟩).1

theorem selection_covers (r : TargetIndex box.length depth) (bin : which box.length depth (Cap k) r = β)
    (wide : j < axisWidth box (targetAxis _ _ r)) :
    ∃ q, targetRank _ _ (selection box depth k j β q) = r := by
  let e := targetRank box.length depth
  have width : j < targetWidth box depth (e.symm r) := by simpa [targetWidth,e] using wide
  obtain ⟨q,hq⟩ := (range_iff _ _ _ _ _).mpr ⟨bin,width⟩
  exact ⟨q,(congrArg e hq).trans (e.apply_symm_apply r)⟩

theorem seed_eq_row {n : ℕ} (inv : Bool) (s : CRTStream.Switch n) :
    CRTStream.seed inv s = row s.2.1 s.2.2 inv s.1.val (FixedCandidate.box n) := by
  unfold CRTStream.seed row
  rw [BoxProgram.encoded,tally_length,box_encoded]

theorem issueAt {n : ℕ} (h : Directory n) (inv : Bool) (s : CRTStream.Switch n) (β : ℕ) :
    issue low (CRTStream.seed inv s,tally β) =
      Native.seed (k := DigitPacking.addressBits n)
        (selection (FixedCandidate.box n) s.1.val (DigitPacking.addressBits n) s.2.2 β) s.2.1 inv s.2.2
        (guardWidth (DigitPacking.addressBits n)) (DigitPacking.addressBits n/16) := by
  rw [seed_eq_row,actual_issue h _ _ _ _ _ s.1.isLt.le]
  simp [low]

theorem countAt {n : ℕ} (h : Directory n) (inv : Bool) (s : CRTStream.Switch n) :
    batchN (CRTStream.seed inv s) = CRTBudget.batches (DigitPacking.addressBits n) := by
  rw [seed_eq_row,batch_count h]
  rfl

private theorem contained {A : Type} [Codec A] (xs : List A) {a : A} (ha : a ∈ xs) : size a ≤ size xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · rw [size_cons]; omega
    · rw [size_cons]; have := ih h; omega

variable {I : Type} (n : I → ℕ) (inv : Bool)

/-- From the physical stage query and a valid serialized batch counter, the complete
native header has a single polynomial bound independent of the original record payload. -/
theorem issueSizeDom :
    let Cases := (e : CRTStream.Input n inv) × Fin (batchN (CRTStream.seed inv e.2.1.val))
    Dom (fun p : Cases => DigitPacking.addressBits (n p.1.1))
      (fun p => size (issue low (CRTStream.seed inv p.1.2.1.val,tally p.2.val))) := by
  dsimp only
  let X := (e : CRTStream.Input n inv) × Fin (batchN (CRTStream.seed inv e.2.1.val))
  let seed (p : X) := CRTStream.seed inv p.1.2.1.val
  have bound := ((directory_poly low low_poly).length.map seed).sub ((CRTStream.seedSizeDom n inv).map Sigma.fst)
  apply bound.mono
  intro p
  apply contained
  rw [directory_eq]
  exact List.mem_ofFn.mpr ⟨p.2,rfl⟩

end FixedCandidate.CRTDispatch

end NearSquareRoot
end Computability
end OAI
