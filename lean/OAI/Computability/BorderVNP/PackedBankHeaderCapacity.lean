import OAI.Computability.BorderVNP.PackedBankCharges

/-! # Word magnitudes in a bounded seed-site bank

The per-tile estimate bounds every computed paid-box operand and every
origin/terminal header. Even when there are zero selector lanes, a matched
copy count fits because its seed also has a terminal with positive original
width. This uses the cap common to all physical tiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCharges

open Crossing Crossing.Profile.Cell Shortening Shortening.CombiningStep Shortening.SeedIntervals
  Shortening.StaticRows BankCircuit Finset
open scoped Classical

private theorem slice_le {R : Type*} [Fintype R] (L : BankLayout R) (r : R) (c : SliceColumn) :
    sliceRead L r c ≤ Fintype.card R * L.stride := by
  let d := L.stride
  let rank := (Fintype.equivFin R r).val
  have hr : rank + 1 ≤ Fintype.card R := (Fintype.equivFin R r).isLt
  have hroom := Nat.mul_le_mul_right d hr
  rw [Nat.add_mul,Nat.one_mul] at hroom
  have hbits : active L r ≤ d :=
    single_le_sum (f := fun u => L.copies u * L.lanes u) (fun _ _ => Nat.zero_le _) (mem_univ r)
  cases c with
  | base => change rank*d+0 ≤ Fintype.card R*d; omega
  | padBase => change rank*d+active L r ≤ Fintype.card R*d; omega
  | padWidth => change d-active L r ≤ Fintype.card R*d; omega

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
  {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

/-- The same uniform physical capacity bounds all numerical headers, including
both kinds of profile bank and all paid-site bases and multiplicities. -/
theorem header_le_of_tile_cap {T : Type*} (hm : 0 < m)
    (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : ∀ t, localRecords (output e p bin perm positive first q).layout true
      (Sum.elim prior (fun _ => 0))
      (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
      (fun v => tile v = t) ≤ M)
    (a : A) :
    let j := blocks p.layout bin perm m a
    let h := (q a).val
    (∀ i : Header D e.count, headerWord m (fun k => k.elim j h) i ≤ bound e * M) ∧
      ∀ (i : Fin e.count) (v : (e.net i).Site) (k : PaidBox.Operand (PaidBox.arity e i v)),
        PaidBox.header (PaidBox.widths (e.net i) v) (h i) k ≤ bound e * M := by
  let j := blocks p.layout bin perm m a
  let h := (q a).val
  let B := bound e * M
  have hsite (v : TemplateSite e) : sparse e v + volume e j h v ≤ B :=
    site_le e p bin perm positive first q tile prior payload M cap a v
  have hvol (v : TemplateSite e) : volume e j h v ≤ B := (Nat.le_add_left _ _).trans (hsite v)
  have hsum : ∑ i, h i = j := profileCounts_total e _ q a
  have hterm := hvol (.inr (.inl first))
  change Fintype.card (Unit ⊕ Unit ⊕ Fin e.count) * (terminalLayout j m h).stride ≤ B at hterm
  have hj : j ≤ B := by
    apply le_trans _ hterm
    rw [terminalStride _ _ _ hsum]
    have ha : 0 < Fintype.card (Unit ⊕ Unit ⊕ Fin e.count) := Fintype.card_pos
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_left _ ha)
  refine ⟨?_, ?_⟩
  · intro i
    rcases i with (_ | i) | ⟨(u | r),c⟩
    · exact hj
    · exact ((single_le_sum (f := h) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans_eq hsum).trans hj
    · rw [origin_word]
      exact (slice_le _ _ _).trans (hvol (.inl ()))
    · rw [terminal_word _ _ _ hsum]
      exact (slice_le _ _ _).trans hterm
  · intro i v k
    have h₁ := hsite (.inr (.inr ⟨i,v⟩))
    let d := PaidBox.arity e i v
    let b := Fintype.card (PaidBox.Bundle (e.net i) v)
    change d+1+b + h i * (1+2*d) ≤ B at h₁
    apply (PaidBox.header_le _ _ k).trans
    change h i + h i*d + d ≤ B
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm (h i) 2] at h₁
    omega

end Packing.BankCharges

end BorderVNP
end Computability
end OAI
