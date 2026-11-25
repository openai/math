import OAI.Hierarchy.TaggedBarrelTurns
import OAI.Hierarchy.TaggedPrefixMask
import OAI.Hierarchy.CatalystSubstitutionNetwork

namespace OAI
/-! # A binary-length equality test between two variable packed ranges -/

noncomputable section
namespace Hierarchy.Tagged.BinaryBarrelTurns
open ThreeFlat Routing CatalystSubstitution
open scoped Classical BigOperators

abbrev Pin (d e w : ℕ) := Fin d ⊕ (Bool × (Fin e ⊕ Fin w))

def pins {d e w : ℕ} (live : Bits d) (off : Bool → Bits e) (word : Bool → Bits w) :
    Pin d e w → Bool := Sum.elim live (fun bi => Sum.elim (off bi.1) (word bi.1) bi.2)

private def maskWire {d e w : ℕ} : PrefixMask.Pin d w → Pin d e w ⊕ Fin w
  | .inl i => .inl (.inl i)
  | .inr j => .inr j

private def turnWire {d e w : ℕ} : BarrelTurns.Pin e w → Pin d e w ⊕ Fin w
  | .inl j => .inr j
  | .inr a => .inl (.inr a)

/-- The prefix flags are private. All bit inputs for the two offsets, the
live length, and both packed words remain exposed. -/
def network (F : Type*) [Field F] (e : ℕ) {d w : ℕ} (room : w ≤ 2^d) :
    BitNetwork F (Fintype.card (Pin d e w)) :=
  plugPair (PrefixMask.network F room) (BarrelTurns.network F e w) maskWire turnWire

theorem value {F : Type*} [Field F] {d e w : ℕ} (room : w ≤ 2^d)
    (live : Bits d) (off : Bool → Bits e) (word : Bool → Bits w) :
    TypedWiring.value (network F e room) (pins live off word) =
      if ∀ j : Fin w, j.val < wordValue live →
        Barrel.shift (word false) (wordValue (off false)) j =
          Barrel.shift (word true) (wordValue (off true)) j then 1 else 0 := by
  have a (z : Fin w → Bool) : Sum.elim (pins live off word) z ∘ maskWire = Sum.elim live z := by
    funext i
    cases i <;> rfl
  have b (z : Fin w → Bool) : Sum.elim (pins live off word) z ∘ turnWire = BarrelTurns.pins z off word := by
    funext i
    cases i <;> rfl
  rw [network,plugPair_value]
  simp only [a,b,PrefixMask.value,BarrelTurns.value,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,PrefixMask.mask,decide_eq_true_eq]

/-- The interface also reads ordinary finite addresses in little-endian
order. Width capacity allows choosing a length word which includes the full
packed width. -/
theorem value_natural {F : Type*} [Field F] {d e w : ℕ} (room : w ≤ 2^d)
    (live : Row d) (off : Bool → Row e) (word : Bool → Bits w) :
    TypedWiring.value (network F e room)
      (pins ((addressEquiv d).symm live) (fun b => (addressEquiv e).symm (off b)) word) =
      if ∀ j : Fin w, j.val < live.val → Barrel.shift (word false) (off false).val j =
          Barrel.shift (word true) (off true).val j then 1 else 0 := by
  simpa only [wordValue_addressEquiv,Equiv.apply_symm_apply] using
    (value (F:=F) room ((addressEquiv d).symm live)
      (fun b => (addressEquiv e).symm (off b)) word)

theorem size (F : Type*) [Field F] (e : ℕ) {d w : ℕ} (room : w ≤ 2^d) :
    (network F e room).cells+(network F e room).internal ≤ 2308*w*(max e d+1) := by
  rw [network,plugPair_cells,plugPair_internal,Fintype.card_fin]
  have cmp := BarrelTurns.size F e w
  have mask := PrefixMask.size F room
  have lhs := Nat.mul_le_mul_left (2051*w) (Nat.add_le_add_right (le_max_left e d) 1)
  have rhs := Nat.mul_le_mul_left (256*w) (Nat.add_le_add_right (le_max_right e d) 1)
  nlinarith [Nat.zero_le (w*max e d)]

/-- One common public word length represents every offset and live length
through the entire packed width, including both endpoints. -/
abbrev digits (w : ℕ) := w.log2 + 1

def address {w : ℕ} (i : Fin (w+1)) : Row (digits w) :=
  ⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt Nat.lt_log2_self⟩

def fixed (F : Type*) [Field F] (w : ℕ) :=
  network F (digits w) (d:=digits w) (w:=w) Nat.lt_log2_self.le

theorem fixed_value {F : Type*} [Field F] {w : ℕ} (live : Fin (w+1))
    (off : Bool → Fin (w+1)) (word : Bool → Bits w) :
    TypedWiring.value (fixed F w)
      (pins ((addressEquiv _).symm (address live))
        (fun b => (addressEquiv _).symm (address (off b))) word) =
      if ∀ j : Fin w, j.val < live.val → Barrel.shift (word false) (off false).val j =
          Barrel.shift (word true) (off true).val j then 1 else 0 :=
  value_natural (F:=F) (w:=w) (d:=digits w) Nat.lt_log2_self.le (address live)
    (fun b => address (off b)) word

theorem fixed_size (F : Type*) [Field F] (w : ℕ) :
    (fixed F w).cells+(fixed F w).internal ≤ 2308*w*(w.log2+2) := by
  simpa only [fixed,max_self,digits,Nat.add_assoc] using
    (size F (digits w) (w:=w) (d:=digits w) Nat.lt_log2_self.le)

end Hierarchy.Tagged.BinaryBarrelTurns

end
end OAI
