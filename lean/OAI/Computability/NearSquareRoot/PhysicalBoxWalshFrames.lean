import OAI.Computability.NearSquareRoot.PhysicalBoxWalsh

/-! # Fixed ticket and data frames for the selected Walsh command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space Strip FixedPoint FixedCandidate DigitPacking
open ShortFourier.BatchWord PhysicalWalsh PhysicalWalsh.GatherProgram

private abbrev WalshTicket := (Bool × Bool) × Tally × Bool × Tally

private def readMask (t : WalshTicket) := emittedMask ((t.2.2.1,t.2.1),t.2.2.2)

private theorem readMask_poly : Poly readMask :=
  (show Easy (fun t : WalshTicket => ((t.2.2.1,t.2.1),t.2.2.2)) from by fun_prop).poly.compose
    emittedMask_poly

private theorem readMask_eq {k : ℕ} (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (dir : Bool) (j : ℕ) (hj : j < (directedPlan (dir,tally k)).length) :
    readMask (phaseStageTicket k dir j hj) = flags (walshBits h dir j hj) :=
  emittedMask_eq h dir ⟨j,hj⟩

private theorem words_eq_records {n} (x : FixedCandidate.Array n) : Odd.words x = records x := by
  change (List.ofFn x).map Dusk.mark = List.ofFn (Dusk.mark ∘ x)
  exact List.map_ofFn ..

/-- Run the compact mask computation on the ticket while the full operand
frame is parked. Forward the flags and data and retain a single operand ruler. -/
theorem walshMaskPre {I : Type} (n stage : I → ℕ) (dir : I → Bool) (hn : ∀ i, 2 ≤ n i)
    (hb : ∀ i, Directory (n i))
    (inside : ∀ i, stage i < (directedPlan (dir i,tally (addressBits (n i)))).length)
    (x : (i : I) → FixedCandidate.Array (n i)) :
    BoundedTask n n
      (fun i => .fork (send (phaseStageTicket (addressBits (n i)) (dir i) (stage i) (inside i))) (framed (x i)))
      (fun i => .fork (send (flags (walshBits (hb i) (dir i) (stage i) (inside i)),Odd.words (x i)))
        (send (tally (n i)))) := by
  let k i := addressBits (n i)
  let ticket i := phaseStageTicket (k i) (dir i) (stage i) (inside i)
  let mask i := flags (walshBits (hb i) (dir i) (stage i) (inside i))
  have small : Dom k (fun i => size (ticket i)) := ⟨1,10000000000,fun i =>
    by simpa only [pow_one] using phaseStageTicket_size (k i) (dir i) (stage i) (inside i)⟩
  obtain ⟨b,hb',run⟩ := readMask_poly.on small
  obtain ⟨B,cap⟩ := setup_le_array hb'
  have eqMask i : readMask (ticket i) = mask i := readMask_eq (hb i) _ _ _
  simp only [eqMask] at run
  have unit i : k i + 1 ≤ 192*n i :=
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (array_volume (hn i))
  have vol i : 2^(k i) ≤ 192*n i :=
    (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (array_volume (hn i)))
  have price i : b i ≤ (B*192)*(n i+1) := by
    rw [Nat.mul_assoc]
    exact (cap i).trans (Nat.mul_le_mul_left B ((vol i).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))))
  have head := (BoundedTask.of_time run).bound (time' := n) (space' := n)
    (B*192+1) (B*192+1920000000001) (fun i => by have := price i; rw [Nat.add_mul]; omega) (by
      intro i
      have p := price i
      have u := unit i
      have q := phaseStageTicket_size (k i) (dir i) (stage i) (inside i)
      change size (ticket i) + b i + 1 ≤ _
      change size (ticket i) ≤ _ at q
      rw [Nat.add_mul]; omega)
  have parked := (head.left (fun i => framed (x i))).bound (time' := n) (space' := n)
    1 75002 (fun _ => by simp) (fun i => by have := framed_size (hn i) (x i); omega)
  let arrange (p : List Bool × Tally × List Dusk.Pair) := ((p.1,p.2.2),p.2.1)
  have ready := linearTree (t := n) (n := n) arrange (by unfold arrange; fun_prop)
    (fun i => (mask i,tally (n i),records (x i))) 76000 (fun _ => le_rfl) (by
      intro i
      have h := framed_size (hn i) (x i)
      change size (tally (n i),records (x i)) ≤ _ at h
      have u := unit i
      have hm : (mask i).length = k i := flags_length _
      change size (mask i)+size (tally (n i),records (x i))+1 ≤ _
      rw [Bits.size_word, hm]; omega)
  simp only [words_eq_records]
  exact sequence parked ready

/-- Reattach the parked ruler to the resulting record stream. -/
theorem walshMaskPost {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (y : (i : I) → FixedCandidate.Array (n i)) :
    BoundedTask n n
      (fun i => .fork (send (Odd.words (y i))) (send (tally (n i)))) (fun i => framed (y i)) := by
  simp only [words_eq_records]
  exact linearTree Prod.swap Easy.exchange (fun i => (records (y i), tally (n i))) 75000
    (fun _ => le_rfl) (fun i => by
      have h := framed_size (hn i) (y i)
      change size (tally (n i),records (y i)) ≤ _ at h
      rw [size_prod] at h ⊢
      dsimp only at h ⊢
      omega)

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
