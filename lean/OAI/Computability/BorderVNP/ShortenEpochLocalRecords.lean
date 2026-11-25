import OAI.Computability.BorderVNP.ShortenSeedIntervalsNetwork
import OAI.Computability.BorderVNP.ShortenEpochProfileWidth

/-!
# Local descriptor and expanded counts

Each local box, cable end, and external interval occupies a public record.
The expanded count adds the widths read there, private payloads and individual
uses of term tables. Additional prior records and their associated payloads
can be charged to their retained sites. Counting the ends separately is
essential: a long uncharged wire need not have its other end nearby.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Finset
open scoped Classical

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {T : Type*}

/-- Charge of a descriptor carrying the given number of extra words or bits.
The public mode ignores all payloads. -/
def recordCost (expanded : Bool) (width : ℕ) := 1 + if expanded then width else 0

/-- A box contains any previous local histories and data attributed to this
site, in addition to its own mandatory public descriptor. -/
def boxCost (expanded : Bool) (prior payload : ℕ) := prior + recordCost expanded payload

/-- Total cost of all the physical records whose incident site passes the
tile test. Separate tests on the two ends support nonlocal uncharged wires. -/
noncomputable def localRecords (N : Network D P bits) (expanded : Bool)
    (prior payload : N.Site → ℕ) (test : N.Site → Prop) : ℕ :=
  testedWidth (fun v => boxCost expanded (prior v) (payload v)) test +
  testedWidth (fun e => recordCost expanded (N.width e)) (fun e => test (N.src e)) +
  testedWidth (fun e => recordCost expanded (N.width e)) (fun e => test (N.dst e)) +
  testedWidth (fun i => recordCost expanded (bits i)) (fun i => test (N.attach i))

private theorem aggregate_testedWidth {E : Type*} [Fintype E] (weight : E → ℕ) (addr : E → T) (near : Finset T) :
      testedWidth weight (fun x => addr x ∈ near) = ∑ o ∈ near, testedWidth weight (fun x => addr x = o) := by
  classical
  unfold testedWidth
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

/-- Cost on any set of input tiles is the sum of the separate tile costs,
including all retained boxes and both physical cable ends. -/
theorem localRecords_near (N : Network D P bits) (expanded : Bool) (prior payload : N.Site → ℕ)
    (tile : N.Site → T) (near : Finset T) :
    localRecords N expanded prior payload (fun v => tile v ∈ near) =
      ∑ o ∈ near, localRecords N expanded prior payload (fun v => tile v = o) := by
  classical
  simp only [localRecords, sum_add_distrib]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (aggregate_testedWidth _ tile near) (aggregate_testedWidth _ (fun e => tile (N.src e)) near))
    (aggregate_testedWidth _ (fun e => tile (N.dst e)) near))
    (aggregate_testedWidth _ (fun i => tile (N.attach i)) near)

/-- Passing from a parent cable to its `J` ordered bands charges its widths
exactly once, even when the table materializes records for empty bands. -/
theorem bands_localRecords {J : Type} [Fintype J] [Nonempty J] (N : Network D P bits)
    (label : ∀ e : N.Edge, Fin (N.width e) → J) (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : N.Site → Prop) :
    localRecords (N.bands label) expanded prior payload test ≤
      Fintype.card J * localRecords N expanded prior payload test := by
  classical
  let C := Fintype.card J
  have hC : 1 ≤ C := Fintype.card_pos
  have he (get : N.Edge → N.Site) :
      (∑ eb : N.Edge × J, if test (get eb.1) then recordCost expanded ((N.bands label).width eb) else 0) ≤
        C * testedWidth (fun e => recordCost expanded (N.width e)) (fun e => test (get e)) := by
    rw [Fintype.sum_prod_type, testedWidth, mul_sum]
    apply sum_le_sum
    intro e _
    by_cases ht : test (get e)
    · simp only [ht,ite_true]
      cases expanded with
      | false => simp [recordCost,C]
      | true =>
        simp only [recordCost, ite_true, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
          mul_one, N.sum_bands_width label e, mul_add]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hC) C
    · simp [ht]
  let boxes := testedWidth (fun v => boxCost expanded (prior v) (payload v)) test
  let ports := testedWidth (fun i => recordCost expanded (bits i)) (fun i => test (N.attach i))
  have hbox := Nat.le_mul_of_pos_left boxes hC
  have hport := Nat.le_mul_of_pos_left ports hC
  have hs := he N.src
  have hd := he N.dst
  change boxes + _ + _ + ports ≤ C * (boxes + _ + _ + ports)
  simp only [mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hbox hs) hd) hport

/-- All public box and cable-end records introduced by one fixed profile. -/
noncomputable def profileDescriptorBound {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m) :=
  Fintype.card ((e.profile 0 (fun _ => 0)).Site) +
    2 * Fintype.card ((e.profile 0 (fun _ => 0)).Edge)

/-- Local factor uses implicit at the banks. The same profile table is used
once per occurrence in its term subsequence. -/
def bankUses {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m) (j : ℕ) (p : Fin e.count → ℕ) :
    (e.profile j p).Site → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr ⟨i,_⟩) => p i

/-- Uniform bound on expanded individual bank uses at one seed. -/
theorem sum_bankUses_le {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m)
    (j : ℕ) (q : Fin e.count → ℕ) (hq : ∑ i, q i = j) :
    ∑ v, bankUses e j q v ≤ j * ∑ i, Fintype.card (e.net i).Site := by
  change (∑ v : Unit ⊕ ((Fin D × Bool) ⊕ (Σ i, (e.net i).Site)), bankUses e j q v) ≤ _
  rw [Fintype.sum_sum_type (fun v : Unit ⊕ ((Fin D × Bool) ⊕ (Σ i, (e.net i).Site)) => bankUses e j q v),
    Fintype.sum_sum_type (fun v : (Fin D × Bool) ⊕ (Σ i, (e.net i).Site) =>
    bankUses e j q (.inr v)), Fintype.sum_sigma]
  simp only [bankUses, sum_const_zero, zero_add, sum_const, card_univ, nsmul_eq_mul, mul_sum]
  exact sum_le_sum fun i _ => (Nat.mul_le_mul_left _ ((single_le_sum (f := q) (fun _ _ => Nat.zero_le _)
    (mem_univ i)).trans_eq hq)).trans_eq (Nat.mul_comm _ _)

end Shortening

end BorderVNP
end Computability
end OAI
