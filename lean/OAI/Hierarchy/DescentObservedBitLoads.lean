import OAI.Hierarchy.DescentObservedHardware
import OAI.Hierarchy.DescentResetTraffic

namespace OAI
/-! # Convert the account of an actual marked bit into unit-width physical wiring -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile DescentSixParty DescentBaseVariance
open scoped Classical BigOperators
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {k Y : ℕ} {D : Dyadic V I k}
variable {B factor unit : ℝ}

/-- Change units from normalized load quanta to actual original physical
bits. The real width of a port is now one. The prices are divided by the
same positive conversion factor at every occupied base. -/
def Loads.per_bit (L : D.Loads Y B (factor*B) unit) (positive : 0<unit) :
    D.Loads Y (B/unit) (factor*(B/unit)) 1 where
  weight s o := L.weight s o/unit
  cap a := L.cap a/unit
  atom s o := ⟨div_nonneg (L.atom s o).1 positive.le,div_le_div_of_nonneg_right (L.atom s o).2 positive.le⟩
  full s g := by
    rw [←Finset.sum_div]
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (L.full s g) positive.le
  carried s g o := by simpa using (le_div_iff₀ positive).mpr (L.carried s g o)
  amount a := by simpa using (le_div_iff₀ positive).mpr (L.amount a)
  budget s g := by
    rw [←Finset.sum_div]
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (L.budget s g) positive.le
  degree := L.degree

/-- A semantic group of `grain` bits costs `price*grain` normalized units.
Only the pricing conversion is removed. The installed physical cable still
contains its full group of bits. -/
def Loads.per_grain {grain price : ℕ} (L : D.Loads Y B (factor*B) ((price*grain:ℕ):ℝ))
    (positive : 0<price) : D.Loads Y (B/price) (factor*(B/price)) grain where
  weight s o := L.weight s o/price
  cap a := L.cap a/price
  atom s o := ⟨div_nonneg (L.atom s o).1 (Nat.cast_nonneg _),
    div_le_div_of_nonneg_right (L.atom s o).2 (Nat.cast_nonneg _)⟩
  full s g := by
    rw [←Finset.sum_div]
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (L.full s g) (Nat.cast_nonneg price)
  carried s g o := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr positive)).mpr
    simpa only [Nat.cast_mul,mul_assoc,mul_comm (grain:ℝ) (price:ℝ)] using L.carried s g o
  amount a := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr positive)).mpr
    simpa only [Nat.cast_mul,mul_assoc,mul_comm (grain:ℝ) (price:ℝ)] using L.amount a
  budget s g := by
    rw [←Finset.sum_div]
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right (L.budget s g) (Nat.cast_nonneg price)
  degree := L.degree

/-- When the allowance is measured in normalized units, its cost in physical
bits is the fixed allowance divided by the cost of one old bit. -/
theorem restored_price (positive : 0<unit) : unit * (factor*(B/unit))=factor*B := by
  field_simp [positive.ne']

variable {F H P : Type} [Field F] {d : ℕ} {bits : P→ℕ} (W : MarkedWorld F d P bits)
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k) (hub : W.graph.Site→Bool)
variable (atoms : W.graph.Site→List H) (wire β hist : ℕ) (hβ : 1≤β)
abbrev BitsOf := Σe : W.graph.Edge,Fin (W.graph.width e)
def physicalOld (s : Bool) (i : BitsOf W) :=
  let v := if s then W.graph.dst i.1 else W.graph.src i.1
  (pos v,ix v)
variable (D : Dyadic V (BitsOf W) k)
variable (trace : ∀s i,D.old s i=physicalOld W pos ix s i)

include trace in
omit [Field F] in
/-- Projecting actual occupied cells into the original graph-bit stream is
injective. Every atom in the projected fiber retains its original endpoint. -/
private theorem counted (s : Bool) (g : D.G) (o : D.OldAt g) :
    (Finset.univ.filter (fun p : D.AtBase s g=>D.whole s g p=o)).card≤
    (Finset.univ.filter (fun i : BitsOf W=>physicalOld W pos ix s i=o.val)).card := by
  apply Finset.card_le_card_of_injOn (fun p : D.AtBase s g=>p.val.val)
  · intro a ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(trace s a.val.val).symm.trans
      (congrArg Subtype.val (Finset.mem_filter.mp ha).2)⟩
  · intro a _ b _ eq
    exact Subtype.ext (Subtype.ext eq)

include hβ in
omit [Fintype V] [Field F] in
private theorem singles (s : Bool) (o : V×Block k) :
    (Finset.univ.filter fun i : BitsOf W=>physicalOld W pos ix s i=o).card*wire ≤
      StarKeys.blockMass W.graph pos ix (W.siteUnits hub atoms wire β hist) o.1 o.2 := by
  let endpt (e : W.graph.Edge) := if s then W.graph.dst e else W.graph.src e
  let atSite (v : W.graph.Site) := (∑e,if v=endpt e then wire*W.graph.width e else 0)
  have full (v : W.graph.Site) : atSite v≤MarkedWorld.siteUnits W hub atoms wire β hist v := by
    have weighted : atSite v ≤
        ∑e,if v=endpt e then wire*W.graph.width e*(if hub (endpt e) then β else 1) else 0 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases eq : v=endpt e
      · simp only [ite_eq_left eq]
        exact Nat.le_mul_of_pos_right _ (by split <;> omega)
      · simp only [ite_eq_right eq,le_refl]
    apply weighted.trans
    cases s with
    | false => exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    | true => exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have count :
      (Finset.univ.filter fun i : BitsOf W=>physicalOld W pos ix s i=o).card*wire =
      ∑v,if pos v=o.1 ∧ ix v=o.2 then atSite v else 0 := by
    let selected (v : W.graph.Site) := pos v=o.1 ∧ ix v=o.2
    trans ∑e : W.graph.Edge, if selected (endpt e) then wire*W.graph.width e else 0
    · rw [Finset.card_filter,Finset.sum_mul,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      change (∑ _ : Fin (W.graph.width e), (if (pos (endpt e),ix (endpt e))=o then 1 else 0)*wire)=_
      have same : (pos (endpt e),ix (endpt e))=o ↔ selected (endpt e) := Prod.ext_iff
      by_cases counted : selected (endpt e) <;> simp [same,counted,Nat.mul_comm]
    · symm
      simp only [atSite,Finset.ite_sum_zero]
      rw [Finset.sum_comm (s:=(Finset.univ : Finset W.graph.Site)) (t:=(Finset.univ : Finset W.graph.Edge))]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single_of_mem (endpt e) (Finset.mem_univ _)]
      · simp [selected]
      · intro v _ ne
        simp [ne]
  rw [count]
  unfold StarKeys.blockMass
  apply Finset.sum_le_sum
  intro v _
  split
  · exact full v
  · rfl

include hβ trace in
omit [Field F] in
theorem physical_carried (s : Bool) (g : D.G) (o : D.OldAt g) :
    ((Finset.univ.filter (fun p : D.AtBase s g=>D.whole s g p=o)).card:ℝ)*wire≤
      (StarKeys.blockMass W.graph pos ix (W.siteUnits hub atoms wire β hist) o.val.1 o.val.2 : ℝ) := by
  exact_mod_cast (Nat.mul_le_mul_right wire (counted W pos ix D trace s g o)).trans
    (singles W pos ix hub atoms wire β hist hβ s o.val)

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
