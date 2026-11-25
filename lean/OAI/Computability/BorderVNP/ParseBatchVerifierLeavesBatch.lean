import OAI.Computability.BorderVNP.ParseBatchVerifierLeaves
import OAI.Computability.BorderVNP.TeamSorting

/-! # Near-linear leaf checks on a batch of coefficient queries -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLeaves

open VPVNP VPVNP.VerifierNetwork BorderVNP.ParseRecords

variable {m g n r : ℕ}

/-- The one-tree gate bound when the sorting lanes and record words fit the logarithmic
width of the query batch. -/
theorem frame_size_per_query (d : Fin n) (hm : m = d.val + 1) (hr : 0 < r)
    (hwidth : max m (max g n) + 1 ≤ 2*m*r) :
    (frame m g n (2*d.val+1) (Nat.clog 2 (2*d.val+1))).size ≤
      600*m*(Nat.clog 2 (2*m*r)+3)^3 := by
  let rows := 2*d.val+1
  let b := Nat.clog 2 rows
  let L := Nat.clog 2 (2*m*r)
  have hrows : rows ≤ 2*m := by dsimp [rows]; omega
  have hcap : 2^b ≤ 4*m :=
    (TeamSorting.padding_lt_twice (show 0 < rows by dsimp [rows]; omega)).le.trans
      ((Nat.mul_le_mul_left 2 hrows).trans_eq (by ring))
  have hb : b ≤ L := Nat.clog_mono_right 2 (hrows.trans (Nat.le_mul_of_pos_right _ hr))
  have hw : recordWidth m g n ≤ L := Nat.clog_mono_right 2 hwidth
  apply (frame_size m g n rows b).trans
  change 2 * (b^2 * (2^b * (24*(recordWidth m g n + 2)+1))) +
    12*(2^b*(recordWidth m g n + 2))+2 ≤ 600*m*(L+3)^3
  calc
    _ ≤ 2 * (L^2 * (4*m * (24*(L+2)+1))) + 12*(4*m*(L+2))+2 := by gcongr
    _ ≤ 600*m*(L+3)^3 := by ring_nf; omega

/-- A single shared-gate frame checks all r leaf multisets. For logarithmic-width
table fields, it uses at most 1 + 600 m r (⌈log₂(2mr)⌉+3)³ gates. Each query
sees only its own preorder block. -/
theorem exists_batch (d : Fin n) (hm : m = d.val+1) (hr : 0 < r)
    (hwidth : max m (max g n) + 1 ≤ 2*m*r) :
    ∃ f : Frame (Fin r × Inputs m g n (2*d.val+1)) (Fin r),
      f.size ≤ 1 + 600*(m*r)*(Nat.clog 2 (2*m*r)+3)^3 ∧
      ∀ x t (a : Fin (2*d.val+1) → GrammarLabel (Fin m × Bool) (Fin g) n),
        (∀ i, unpack m g n (fieldsOfBits (fun j => x (t,.inr (i,j)))) = some (a i)) →
        (f.eval x t = true ↔ Matches d (fun i => (i,x (t,.inl i))) (List.ofFn a)) := by
  let rows := 2*d.val+1
  let F := frame m g n rows (Nat.clog 2 rows)
  let one (t : Fin r) := F.subst (Frame.initial (fun i => (t,i)))
  obtain ⟨p, hp, he⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin r => Unit) one
  refine ⟨p.select (fun t => ⟨t,()⟩), ?_, ?_⟩
  · rw [Frame.select_size]
    simp only [one, Frame.subst_size, Frame.initial_size, zero_add, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hp
    refine hp.trans (Nat.add_le_add_left ?_ 1)
    exact (Nat.mul_le_mul_left r (frame_size_per_query d hm hr hwidth)).trans_eq (by ring)
  · intro x t a ha
    rw [Frame.select_eval, he]
    let wire : Inputs m g n rows → Fin r × Inputs m g n rows := fun i => (t,i)
    have e : (Frame.initial wire).eval x = fun i => x (t,i) := by
      funext i; simp [wire]
    change (F.subst (Frame.initial wire)).eval x () = true ↔ _
    rw [Frame.subst_eval, e]
    exact frame_eval_of_unpacked (b := Nat.clog 2 rows) d (fun i => x (t,i)) a ha rfl hm
      (Nat.le_pow_clog (by decide) rows)

end ParseBatchLeaves

end BorderVNP
end Computability
end OAI
