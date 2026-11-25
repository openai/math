import OAI.Hierarchy.TaggedAlignWord
import OAI.Hierarchy.TaggedAlign

namespace OAI
/-! # The adjacent real-row check for packed routing

The input address is split at the pack boundary. A same-key step increments
the whole address. A larger-key step increments the high field and clears all
low result bits. The two branches are disjoint on the exposed keys.
-/

namespace Hierarchy.Tagged.AlignTransition
open ThreeFlat Routing
open AlignWord ExactQuantumFactoring
open scoped Classical
noncomputable section

abbrev Ports (d j t : ℕ) := Pin d ⊕ (Pin j ⊕ Pin t)

def pull {F A B : Type*} [Fintype A] [Fintype B] (N : BitNetwork F (Fintype.card A))
    (wire : A → B ⊕ Bool) : BitNetwork F (Fintype.card B) :=
  Guard.rename N (fun i => Sum.map (Fintype.equivFin B) id (wire ((Fintype.equivFin A).symm i)))

theorem pull_eval {F A B : Type*} [CommSemiring F] [Fintype A] [Fintype B]
    (N : BitNetwork F (Fintype.card A)) (wire : A → B ⊕ Bool) (x : B → Bool) :
    TypedWiring.value (pull N wire) x = TypedWiring.value N (Sum.elim x id ∘ wire) := by
  unfold TypedWiring.value pull
  rw [Guard.rename_value]
  congr 1
  funext i
  cases s : wire ((Fintype.equivFin A).symm i) <;> simp [s]

private def key {d j t : ℕ} (p : Pin d) : Ports d j t ⊕ Bool := .inl (.inl p)
private def high {d j t : ℕ} (p : Pin t) : Ports d j t ⊕ Bool := .inl (.inr (.inr p))
private def full {d j t : ℕ} (p : Pin (j+t)) : Ports d j t ⊕ Bool :=
  .inl (Fin.addCases (fun i => .inr (.inl (p.1,i))) (fun i => .inr (.inr (p.1,i))) p.2)
private def zeroLow {d j t : ℕ} (p : Pin j) : Ports d j t ⊕ Bool :=
  if p.1 then .inl (.inr (.inl (true,p.2))) else .inr false

def network (F : Type*) [Zero F] [One F] (d j t : ℕ) : BitNetwork F (Fintype.card (Ports d j t)) :=
  Guard.either (Guard.both (pull (equal F d) key) (pull (increment F (j+t)) full))
    (Guard.both (pull (less F d) key)
      (Guard.both (pull (increment F t) high) (pull (equal F j) zeroLow)))

def cat {j t : ℕ} (lo : BitVec j) (hi : BitVec t) : BitVec (j+t) :=
  bitsValue (Fin.append (fun i => lo.getLsbD i.val) (fun i => hi.getLsbD i.val))

private theorem cat_nat {j t : ℕ} (lo : BitVec j) (hi : BitVec t) :
    (cat lo hi).toNat = lo.toNat + 2^j*hi.toNat := by
  have eq := wordValue_append (fun i : Fin j => lo.getLsbD i.val) (fun i : Fin t => hi.getLsbD i.val)
  simp only [wordValue_addressEquiv] at eq
  change (cat lo hi).toNat = (bitsValue (fun i : Fin j => lo.getLsbD i.val)).toNat +
    2^j*(bitsValue (fun i : Fin t => hi.getLsbD i.val)).toNat at eq
  simpa only [bitsValue_bits] using eq

def pins {d j t : ℕ} (a b : BitVec d) (x y : BitVec j) (u v : BitVec t) : Ports d j t → Bool :=
  Sum.elim (bits a b) (Sum.elim (bits x y) (bits u v))

private theorem cat_low {j t : ℕ} (x : BitVec j) (y : BitVec t) (k : Fin j) :
    (cat x y).getLsbD (Fin.castAdd t k).val=x.getLsbD k.val :=
  (bitsValue_bit _ (Fin.castAdd t k)).trans (Fin.append_left _ _ k)

private theorem cat_high {j t : ℕ} (x : BitVec j) (y : BitVec t) (k : Fin t) :
    (cat x y).getLsbD (Fin.natAdd j k).val=y.getLsbD k.val :=
  (bitsValue_bit _ (Fin.natAdd j k)).trans (Fin.append_right _ _ k)

private theorem full_pins {d j t : ℕ} (a b : BitVec d) (x y : BitVec j) (u v : BitVec t) :
    Sum.elim (pins a b x y u v) id ∘ full = bits (cat x u) (cat y v) := by
  funext p
  rcases p with ⟨flag,i⟩
  cases flag <;> refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
    simp only [Function.comp_apply,full,Fin.addCases_left,Fin.addCases_right,Sum.elim_inl,Sum.elim_inr,
      pins,bits,Bool.false_eq_true,ite_false,ite_true] <;>
    first | exact (cat_low ..).symm | exact (cat_high ..).symm

private theorem zero_pins {d j t : ℕ} (a b : BitVec d) (x y : BitVec j) (u v : BitVec t) :
    Sum.elim (pins a b x y u v) id ∘ zeroLow = bits 0 y := by
  funext p
  rcases p with ⟨flag,i⟩
  cases flag <;> simp [bits, pins, zeroLow]

private theorem value_either {F P : Type*} [CommSemiring F] [Fintype P]
    (A B : BitNetwork F (Fintype.card P)) (x : P → Bool) :
    TypedWiring.value (Guard.either A B) x = TypedWiring.value A x + TypedWiring.value B x :=
  Guard.either_eval A B _
private theorem value_both {F P : Type*} [CommSemiring F] [Fintype P]
    (A B : BitNetwork F (Fintype.card P)) (x : P → Bool) :
    TypedWiring.value (Guard.both A B) x = TypedWiring.value A x * TypedWiring.value B x :=
  Guard.both_eval A B _

/-- The numeric successor relation on adjacent sorted real slots. -/
theorem eval (F : Type*) [CommSemiring F] {d j t : ℕ} (a b : BitVec d)
    (x y : BitVec j) (u v : BitVec t) (sorted : a.toNat ≤ b.toNat) :
    TypedWiring.value (network F d j t) (pins a b x y u v) =
      if (cat y v).toNat = Align.advance (2^j) (cat x u).toNat (decide (a ≠ b)) then 1 else 0 := by
  have k : Sum.elim (pins a b x y u v) id ∘ key = bits a b := rfl
  have h : Sum.elim (pins a b x y u v) id ∘ high = bits u v := rfl
  simp only [network, value_either, value_both, pull_eval, k, h, full_pins, zero_pins, equal_eval,
    less_eval, increment_eval]
  by_cases same : a = b
  · subst b
    simp [Align.advance]
  · have lt : a.toNat < b.toNat := sorted.lt_of_ne (fun e => same (BitVec.toNat_inj.mp e))
    have pos := Nat.two_pow_pos j
    have div : (cat x u).toNat / 2^j = u.toNat := by
      rw [cat_nat, Nat.add_mul_div_left _ _ pos, Nat.div_eq_of_lt x.isLt, Nat.zero_add]
    have boundary : (cat y v).toNat = (u.toNat+1)*2^j ↔ v.toNat = u.toNat+1 ∧ 0 = y := by
      rw [cat_nat]
      constructor
      · intro eq
        have hi := congrArg (fun n => n/2^j) eq
        simp only [Nat.add_mul_div_left _ _ pos, Nat.div_eq_of_lt y.isLt, Nat.zero_add,
          Nat.mul_div_cancel _ pos] at hi
        have zero : y.toNat = 0 := by rw [hi, Nat.mul_comm] at eq; omega
        exact ⟨hi, BitVec.toNat_inj.mp (by simp [zero])⟩
      · rintro ⟨hi,rfl⟩
        simp [hi, Nat.mul_comm]
    simp only [same, ite_false, zero_mul, lt, ite_true, one_mul, zero_add, ne_eq, not_false_eq_true,
      decide_true, Align.advance, div, boundary]
    by_cases highOk : v.toNat = u.toNat + 1 <;> by_cases lowOk : (0 : BitVec j) = y <;> simp [highOk, lowOk]

/-- The hidden branch and all word comparisons have total size linear in word width. -/
theorem size (F : Type*) [Zero F] [One F] (d j t : ℕ) :
    (network F d j t).cells+(network F d j t).internal ≤ 200000*(d+j+t+3) := by
  unfold network
  apply (Guard.either_size _ _).trans
  have a := Guard.both_size (pull (equal F d) (@key d j t)) (pull (increment F (j+t)) full)
  have b := Guard.both_size (pull (increment F t) (@high d j t)) (pull (equal F j) zeroLow)
  have c := Guard.both_size (pull (less F d) (@key d j t))
    (Guard.both (pull (increment F t) high) (pull (equal F j) zeroLow))
  have incW := increment_size F (j+t)
  have incH := increment_size F t
  have cmp := less_size F d
  dsimp only [pull, Guard.rename, equal] at a b c ⊢
  omega

end
end Hierarchy.Tagged.AlignTransition

end OAI
