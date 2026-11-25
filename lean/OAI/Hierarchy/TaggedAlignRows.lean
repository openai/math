import OAI.Hierarchy.TaggedAlignmentData
import OAI.Hierarchy.TaggedAlignShell
import OAI.Hierarchy.TaggedAlignTransition
import OAI.Hierarchy.TaggedPinGuard

namespace OAI
/-! # The physical row checks used in a block alignment -/

namespace Hierarchy.Tagged.AlignRows
open ThreeFlat Routing SortNetwork
open ExactQuantumFactoring AlignShell AlignWord AlignTransition
open scoped BigOperators Classical
noncomputable section

private abbrev C (j t w : ℕ) := CheckPins (j+t) w

private def atPair {m : ℕ} (e : Edge m) : Bool → Row m
  | false => e.val
  | true => next e

private def hop {d j t w : ℕ} (digit : Fin d → Fin w) (e : Edge (j+t)) :
    Ports d j t → C j t w ⊕ Bool
  | .inl (b,i) => .inl (.inl (atPair e b,digit i))
  | .inr (.inl (b,i)) => .inl (.inr (atPair e b,i.castAdd t))
  | .inr (.inr (b,i)) => .inl (.inr (atPair e b,Fin.natAdd j i))

private def address {j t w : ℕ} (e : Edge (j+t)) (p : Pin (j+t)) : C j t w ⊕ Bool :=
  .inl (.inr (atPair e p.1,p.2))
private def initial {j t w : ℕ} (p : Pin (j+t)) : C j t w ⊕ Bool :=
  if p.1 then .inl (.inr (0,p.2)) else .inr false

def first (F : Type*) [Zero F] [One F] {j t w : ℕ} (real : Fin w) :
    BitNetwork F (Fintype.card (C j t w)) :=
  Guard.onPin (.inl (0,real) : C j t w) true (pull (equal F (j+t)) initial)

def adjacent (F : Type*) [Zero F] [One F] {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w)
    (e : Edge (j+t)) : BitNetwork F (Fintype.card (C j t w)) :=
  let gate (b : Bool) (N : BitNetwork F (Fintype.card (C j t w))) :=
    Guard.onPin (.inl (e.val,real) : C j t w) b (Guard.onPin (.inl (next e,real) : C j t w) b N)
  Guard.both (gate true (pull (AlignTransition.network F d j t) (hop digit e)))
    (gate false (pull (less F (j+t)) (address e)))

private def component (F : Type*) [Zero F] [One F] {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) :
    Option (Edge (j+t)) → BitNetwork F (Fintype.card (C j t w))
  | none => first F real
  | some e => adjacent F real digit e

def network (F : Type*) [Zero F] [One F] {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) :
    BitNetwork F (Fintype.card (C j t w)) :=
  BitNetwork.glue (component F real digit) fun _ i => (BitSource.pin i : BitSource 0 _)

def checkerPins {h w : ℕ} (input : Records h w) (g : Row h → Row h) : CheckPins h w → Bool :=
  Sum.elim (Function.uncurry input) (fun (i,j) => (addressEquiv h).symm (g i) j)

private def low {j t : ℕ} (a : Row (j+t)) := bitsValue (fun i : Fin j => (addressEquiv _).symm a (i.castAdd t))
private def hi {j t : ℕ} (a : Row (j+t)) := bitsValue (fun i : Fin t => (addressEquiv _).symm a (Fin.natAdd j i))
private def code {h : ℕ} (a : Row h) := bitsValue ((addressEquiv _).symm a)
private theorem code_nat {h : ℕ} (a : Row h) : (code a).toNat = a.val :=
  congrArg Fin.val ((addressEquiv h).apply_symm_apply a)
private theorem joined {j t : ℕ} (a : Row (j+t)) : cat (low a) (hi a) = code a := by
  unfold cat code
  apply congrArg bitsValue
  funext i
  refine Fin.addCases (fun l => ?_) (fun u => ?_) i
  · rw [Fin.append_left]
    exact bitsValue_bit _ l
  · rw [Fin.append_right]
    exact bitsValue_bit _ u

private theorem hop_read {d j t w : ℕ} (digit : Fin d → Fin w) (e : Edge (j+t))
    (input : Records (j+t) w) (g : Row (j+t) → Row (j+t)) :
    Sum.elim (checkerPins input g) id ∘ hop digit e =
      AlignTransition.pins (digitValue digit input e.1) (digitValue digit input (next e))
        (low (g e.1)) (low (g (next e))) (hi (g e.1)) (hi (g (next e))) := by
  funext p
  rcases p with ⟨b,i⟩ | (⟨b,i⟩ | ⟨b,i⟩) <;> cases b <;>
    simp only [Function.comp_apply,hop,checkerPins,atPair,Sum.elim_inl,Sum.elim_inr,
      AlignTransition.pins,bits,digitValue,low,hi,Bool.false_eq_true,ite_false,ite_true,
      Function.uncurry_apply_pair,bitsValue_bit]

private theorem addr_read {j t w : ℕ} (e : Edge (j+t)) (input : Records (j+t) w)
    (g : Row (j+t) → Row (j+t)) : Sum.elim (checkerPins input g) id ∘ address e =
      bits (code (g e.1)) (code (g (next e))) := by
  funext p
  rcases p with ⟨b,i⟩
  cases b <;> simp only [Function.comp_apply,address,atPair,checkerPins,Sum.elim_inl,Sum.elim_inr,
    bits,code,Bool.false_eq_true,ite_false,ite_true,bitsValue_bit]

private theorem initial_read {j t w : ℕ} (input : Records (j+t) w) (g : Row (j+t) → Row (j+t)) :
    Sum.elim (checkerPins input g) id ∘ initial = bits 0 (code (g 0)) := by
  funext p
  rcases p with ⟨b,i⟩
  cases b with
  | false => simp [initial,bits]
  | true => simp only [Function.comp_apply,initial,ite_true,Sum.elim_inl,Sum.elim_inr,checkerPins,
      bits,code,bitsValue_bit]

def GoodEdge {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) (input : Records (j+t) w)
    (g : Row (j+t) → Row (j+t)) (e : Edge (j+t)) : Prop :=
  (input e.1 real = true → input (next e) real = true → (g (next e)).val =
    Align.advance (2^j) (g e.1).val (decide (digitValue digit input e.1 ≠ digitValue digit input (next e)))) ∧
  (input e.1 real = false → input (next e) real = false → g e.1 < g (next e))

private theorem adjacent_eval {F : Type*} [CommSemiring F] {d j t w : ℕ} (real : Fin w)
    (digit : Fin d → Fin w) (input : Records (j+t) w) (ordered : Ordered real digit input)
    (g : Row (j+t) → Row (j+t)) (e : Edge (j+t)) :
    TypedWiring.value (adjacent F real digit e) (checkerPins input g) =
      if GoodEdge real digit input g e then 1 else 0 := by
  unfold adjacent
  rw [show ∀ A B, TypedWiring.value (Guard.both A B) (checkerPins input g) =
    TypedWiring.value A (checkerPins input g)*TypedWiring.value B (checkerPins input g)
    from fun A B => Guard.both_eval A B _]
  simp only [Guard.onPin_eval, pull_eval, hop_read, addr_read, less_eval, code_nat]
  cases l : input e.1 real <;> cases r : input (next e) real
  all_goals try rw [AlignTransition.eval F _ _ _ _ _ _ (ordered e l r), joined, joined, code_nat, code_nat]
  all_goals simp [checkerPins, l, r, GoodEdge, Fin.lt_def, -Fin.val_fin_lt]

/-- Contracting the entire row verifier checks precisely these adjacent address
rules, including the first real slot. -/
theorem eval {F : Type*} [CommSemiring F] {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w)
    (input : Records (j+t) w) (ordered : Ordered real digit input) (g : Row (j+t) → Row (j+t)) :
    TypedWiring.value (network F real digit) (checkerPins input g) =
      if (input 0 real = true → (g 0).val = 0) ∧ (∀ e, GoodEdge real digit input g e) then 1 else 0 := by
  let pin := checkerPins input g
  change (network F real digit).eval (pin ∘ (Fintype.equivFin _).symm) = _
  rw [network, BitNetwork.glue_eval]
  simp only [Fintype.sum_unique, Fintype.prod_option, component, BitSource.read]
  change TypedWiring.value (first F real) pin * (∏ e, TypedWiring.value (adjacent F real digit e) pin) = _
  simp only [pin, adjacent_eval real digit input ordered, Fintype.prod_boole,
    first, Guard.onPin_eval, pull_eval, initial_read, equal_eval, ← BitVec.toNat_inj, code_nat]
  change (if input 0 real = true then (if 0 = (g 0).val then 1 else 0) else 1) * _ = _
  by_cases tag : (g 0).val=0
  · simp only [ite_eq_left tag.symm]
    by_cases start : input 0 real=true <;> by_cases steps : ∀ e, GoodEdge real digit input g e <;>
      simp [start,tag,steps]
  · simp only [ite_eq_right (Ne.symm tag)]
    by_cases start : input 0 real=true <;> by_cases steps : ∀ e, GoodEdge real digit input g e <;>
      simp [start,tag,steps]

private theorem first_size (F : Type*) [Zero F] [One F] {j t w : ℕ} (real : Fin w) :
    (first (j := j) (t := t) F real).cells + (first (j := j) (t := t) F real).internal ≤ 177*(j+t) := by
  unfold first
  exact (Guard.onPin_size _ _ _).trans (by simp [pull, Guard.rename, equal])

private theorem pull_bill {F A B : Type*} [Fintype A] [Fintype B]
    (N : BitNetwork F (Fintype.card A)) (wire : A → B ⊕ Bool) :
    (pull N wire).cells + (pull N wire).internal = N.cells + N.internal := rfl

private theorem edge_size (F : Type*) [Zero F] [One F] {d j t w : ℕ} (real : Fin w)
    (digit : Fin d → Fin w) (e : Edge (j+t)) :
    (adjacent F real digit e).cells+(adjacent F real digit e).internal ≤ 7000000000*(d+j+t+3) := by
  let left : C j t w := .inl (e.val,real)
  let right : C j t w := .inl (next e,real)
  have guard (b : Bool) (N : BitNetwork F (Fintype.card (C j t w))) :
      (Guard.onPin left b (Guard.onPin right b N)).cells +
      (Guard.onPin left b (Guard.onPin right b N)).internal ≤ 177*177*(N.cells+N.internal) := by
    have a := Guard.onPin_size left b (Guard.onPin right b N)
    have c := Guard.onPin_size right b N
    exact a.trans ((Nat.mul_le_mul_left 177 c).trans_eq (Nat.mul_assoc ..).symm)
  unfold adjacent
  rw [Guard.both_size]
  have pa := guard true (pull (AlignTransition.network F d j t) (hop digit e))
  have pb := guard false (pull (less F (j+t)) (address e))
  dsimp only [left,right] at pa pb
  have ra := AlignTransition.size F d j t
  have rb := less_size F (j+t)
  rw [pull_bill] at pa pb
  apply (Nat.add_le_add pa pb).trans
  omega

/-- A fixed number of word tests per row, including guard circuitry. -/
theorem size (F : Type*) [Zero F] [One F] {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) :
    (network (j := j) (t := t) F real digit).cells+(network (j := j) (t := t) F real digit).internal ≤
      14000000000*2^(j+t)*(d+j+t+3) := by
  let cap := 7000000000*(d+j+t+3)
  have site (g : Option (Edge (j+t))) :
      (component F real digit g).cells + (component F real digit g).internal ≤ cap := by
    cases g with
    | none => exact (first_size F real).trans (by dsimp [cap]; omega)
    | some e => exact edge_size F real digit e
  have count : Fintype.card (Edge (j+t)) ≤ 2^(j+t) := by
    simpa using Fintype.card_subtype_le (fun i : Row (j+t) => i.val+1 < 2^(j+t))
  have npos := Nat.two_pow_pos (j+t)
  have many : Fintype.card (Option (Edge (j+t))) ≤ 2*2^(j+t) := by simpa using (show
      Fintype.card (Edge (j+t))+1 ≤ 2*2^(j+t) by omega)
  simp only [network, BitNetwork.glue_cells, BitNetwork.glue_internal, Nat.zero_add, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _g : Option (Edge (j+t)), cap := Finset.sum_le_sum fun g _ => site g
    _ = Fintype.card (Option (Edge (j+t)))*cap := by simp
    _ ≤ (2*2^(j+t))*cap := Nat.mul_le_mul_right _ many
    _ = _ := by dsimp [cap]; ring

end
end Hierarchy.Tagged.AlignRows

end OAI
