import OAI.Hierarchy.TaggedShorterBarrel
import OAI.Hierarchy.TaggedWireEquality

namespace OAI
/-! # Matching a masked range after two independent barrel shifts -/

noncomputable section
namespace Hierarchy.Tagged.BarrelTurns
open ThreeFlat Routing
open WireTelescope
open scoped Classical BigOperators

abbrev Pin (e w : ℕ) := Fin w ⊕ (Bool × (Fin e ⊕ Fin w))
private abbrev Shifted (w : ℕ) := Bool × Fin w

def pins {e w : ℕ} (mask : Bits w) (offset : Bool → Bits e) (word : Bool → Bits w) : Pin e w → Bool :=
  Sum.elim mask (fun bi => Sum.elim (offset bi.1) (word bi.1) bi.2)

private def gate (e w : ℕ) : Option Bool → Type
  | none => Equality.Pins w
  | some _ => Barrel.Pin e w

private instance (e w : ℕ) (i : Option Bool) : Fintype (gate e w i) :=
  match i with
  | none => inferInstanceAs (Fintype (Equality.Pins w))
  | some _ => inferInstanceAs (Fintype (Barrel.Pin e w))

private def part (F : Type*) [Zero F] [One F] (e w : ℕ) :
    (i : Option Bool) → BitNetwork F (Fintype.card (gate e w i))
  | none => Equality.network F w
  | some _ => Barrel.network F e w

private def wire {e w : ℕ} : (i : Option Bool) → gate e w i → Pin e w ⊕ Shifted w
  | none, (j,t) => if t=0 then .inl (.inl j) else .inr (decide (t=2),j)
  | some b, .inl j => .inl (.inr (b,.inl j))
  | some b, .inr (.inl j) => .inl (.inr (b,.inr j))
  | some b, .inr (.inr j) => .inr (b,j)

def network (F : Type*) [Zero F] [One F] (e w : ℕ) : BitNetwork F (Fintype.card (Pin e w)) :=
  TypedWiring.glue (part F e w) wire

private theorem barrel_read {e w : ℕ} (mask : Bits w) (off : Bool → Bits e) (word : Bool → Bits w)
    (z : Shifted w → Bool) (b : Bool) :
    (fun j => Sum.elim (pins mask off word) z (wire (some b) j)) =
      Barrel.pins (off b) (word b) (fun j => z (b,j)) := by
  funext j
  rcases j with k | (k | k) <;> rfl

private theorem mask_read {F : Type*} [CommSemiring F] {e w : ℕ} (mask : Bits w)
    (off : Bool → Bits e) (word : Bool → Bits w) (z : Shifted w → Bool) :
    TypedWiring.value (part F e w none) (fun j => Sum.elim (pins mask off word) z (wire none j)) =
      if ∀ j, mask j=true → z (false,j)=z (true,j) then 1 else 0 := by
  let q : Equality.Pins w→Bool := fun j=>Sum.elim (pins mask off word) z (wire none j)
  have z₀ (j : Fin w) : q (j,0)=mask j := by simp [q,wire,pins]
  have z₁ (j : Fin w) : q (j,1)=z (false,j) := by
    simp [q,wire,show (1 : Fin 3)≠0 by decide,show (1 : Fin 3)≠2 by decide]
  have z₂ (j : Fin w) : q (j,2)=z (true,j) := by
    simp [q,wire,show (2 : Fin 3)≠0 by decide]
  calc
    _ = (if ∀j,q (j,0)=true → q (j,1)=q (j,2) then 1 else 0) := Equality.eval F q
    _ = _ := by simp only [z₀,z₁,z₂]

/-- Every fixed setting of the two offsets determines the two hidden shifted
words uniquely, including at the zero-padded ends. -/
theorem value {F : Type*} [CommSemiring F] {e w : ℕ} (mask : Bits w)
    (off : Bool → Bits e) (word : Bool → Bits w) :
    TypedWiring.value (network F e w) (pins mask off word) =
      if ∀ j, mask j=true → Barrel.shift (word false) (wordValue (off false)) j =
        Barrel.shift (word true) (wordValue (off true)) j then 1 else 0 := by
  let want : Shifted w → Bool := fun z => Barrel.shift (word z.1) (wordValue (off z.1)) z.2
  have bank (z : Shifted w → Bool) : (∏ b : Bool, TypedWiring.value (part F e w (some b))
      (fun j => Sum.elim (pins mask off word) z (wire (some b) j))) =
      if z=want then (1:F) else 0 := by
    have atBit (b : Bool) : TypedWiring.value (part F e w (some b))
        (fun j=>Sum.elim (pins mask off word) z (wire (some b) j)) =
        if (fun j=>z (b,j))=Barrel.shift (word b) (wordValue (off b)) then 1 else 0 := by
      rw [barrel_read]
      exact Barrel.value (off b) (word b) (fun j=>z (b,j))
    simp only [atBit,Fintype.prod_boole]
    have e : (∀ b, (fun j => z (b,j)) = Barrel.shift (word b) (wordValue (off b))) ↔ z=want := by
      constructor
      · intro q; funext ⟨b,j⟩; exact congrFun (q b) j
      · rintro rfl b; rfl
    exact ite_cond_congr (propext e)
  rw [network,TypedWiring.glue_value]
  simp only [Fintype.prod_option,mask_read,bank,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]; rfl

/-- The contribution factors as one indicator for each live column. -/
theorem product_offset {F : Type*} [CommSemiring F] {e w : ℕ} (live : ℕ)
    (off : Bool → Row e) (word : Bool → Bits w) :
    TypedWiring.value (network F e w)
      (pins (fun j => decide (j.val < live)) (fun b => (addressEquiv e).symm (off b)) word) =
      ∏ j : Fin w, if j.val < live → Barrel.shift (word false) (off false).val j =
        Barrel.shift (word true) (off true).val j then 1 else 0 := by
  simp only [value,wordValue_addressEquiv,Equiv.apply_symm_apply,decide_eq_true_eq,Fintype.prod_boole]
 ; split_ifs <;> rfl

/-- The entire masked comparison uses two barrel networks, two hidden words,
and one trivalent equality cell per column. -/
theorem size (F : Type*) [Zero F] [One F] (e w : ℕ) :
    (network F e w).cells + (network F e w).internal ≤ 2051*w*(e+1) := by
  simp only [network,TypedWiring.glue_cells,TypedWiring.glue_internal,Fintype.sum_option,
    Fintype.sum_bool,part, Equality.network, Shifted, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]
  have cost := Barrel.size F e w
  nlinarith

end Hierarchy.Tagged.BarrelTurns

end
end OAI
