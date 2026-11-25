import OAI.ThreeFlat.Diagonal.CompressorRegularize
import OAI.ThreeFlat.Diagonal.CompressorMotifLanes
import OAI.ThreeFlat.Diagonal.CompressorDistinctBases
import OAI.ThreeFlat.Diagonal.CompressorDRoles

namespace OAI
/-! # A regular lifted graph on the surviving six-party wires -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

variable {c d : ℕ} {V H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

inductive Role | a | b | d deriving DecidableEq

/-- The old packed bundle endpoints and the destination of the old D map. -/
def siteOf (layout : Bool) : Role → P.Motif → Site V Tag L
  | .a => P.roleA
  | .b => P.roleB
  | .d => P.roleD layout

/-- The retained supplies in the common order of their masses. -/
def supplyRoles : Bool → Fin 4 → Role × Role
  | false => ![(.b,.a),(.b,.d),(.a,.d),(.d,.a)]
  | true => ![(.a,.b),(.a,.d),(.b,.d),(.d,.b)]

theorem supplyRoles_ne (layout : Bool) (e : Fin 4) : (supplyRoles layout e).1 ≠ (supplyRoles layout e).2 := by
  cases layout <;> fin_cases e <;> decide

theorem moves_of_role (layout : Bool) (role : Role) (g : L) (m : P.Motif) :
    siteOf P layout role (moveMotif P g m) = moveSite g (siteOf P layout role m) := by
  cases role with
  | a => exact roleA_move P g m
  | b => exact roleB_move P g m
  | d => exact roleD_move P g layout m

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]

private theorem role_count_eq (hc : 2 ≤ c) :
    3*d^2*2^(c-2) = d*(3*(2^c*d)/4) := by
  have h : 2^c = 2^(c-2)*2^2 := by rw [← Nat.pow_add]; congr 1; omega
  rw [h, show 3*(2^(c-2)*2^2*d) = (3*2^(c-2)*d)*4 by ring, Nat.mul_div_cancel _ (by decide : 0 < 4)]
  ring

/-- Each role has `dQ` rooted incidences at every base vertex. Normalizing
the old lane produces exactly the role incidences at lane zero. -/
theorem rooted_role_count (layout : Bool) (role : Role) (b : V × Tag) (hc : 2 ≤ c) :
    Fintype.card {m : Rooted P // base (siteOf P layout role m.val) = b} = d*(3*(2^c*d)/4) := by
  rw [Fintype.card_congr (roleAtZero P (siteOf P layout role) (moves_of_role P layout role) b)]
  cases role with
  | a => exact roleA_count P _ hc
  | b => exact roleB_count P _ hc
  | d => exact (roleD_count P layout _).trans (role_count_eq hc)

/-- One old motif occurrence per parallel slot, labelled also by its supply edge. -/
abbrev ShrinkEdge (count : Fin 4 → ℕ) := Σ e : Fin 4, Rooted P × Fin (count e)

def slotSite (layout : Bool) (role : Fin 4 → Role) {count : Fin 4 → ℕ}
    (e : ShrinkEdge P count) : Site V Tag L := siteOf P layout (role e.1) e.2.1.val

private def incidenceEquiv (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ) (b : V × Tag) :
    {e : ShrinkEdge P count // base (slotSite P layout role e) = b} ≃
      Σ t : Fin 4, {m : Rooted P // base (siteOf P layout (role t) m.val) = b} × Fin (count t) where
  toFun e := ⟨e.val.1, ⟨e.val.2.1,e.property⟩,e.val.2.2⟩
  invFun e := ⟨⟨e.1,e.2.1.val,e.2.2⟩,e.2.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incident_count (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (b : V × Tag) (hc : 2 ≤ c) :
    (CompressorRegularize.incident (fun e : ShrinkEdge P count => base (slotSite P layout role e)) b).card =
      d*(3*(2^c*d)/4)*(∑ e, count e) := by
  let f := fun e : ShrinkEdge P count => base (slotSite P layout role e)
  have eqv : ↥(CompressorRegularize.incident f b) ≃ {e // f e = b} :=
    Equiv.subtypeEquivRight (fun _ => by simp [CompressorRegularize.incident])
  rw [← Fintype.card_coe, Fintype.card_congr eqv, Fintype.card_congr (incidenceEquiv P layout role count b)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, rooted_role_count P layout _ b hc,
    Finset.mul_sum]

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem ends_ne (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (layout : Bool) (count : Fin 4 → ℕ) (e : ShrinkEdge P count) :
    base (slotSite P layout (fun t => (supplyRoles layout t).2) e) ≠
      base (slotSite P layout (fun t => (supplyRoles layout t).1) e) := by
  have hd := distinct_bases P hn good layout e.2.1.val
  rcases e with ⟨t,m,i⟩
  cases layout <;> fin_cases t <;>
    simp only [slotSite, siteOf, supplyRoles] at * <;>
      tauto

/-- The regular surviving graph. An ordinal for each label fixes the
source and target slot order independently at every vertex. The remaining
lane displacement is the actual difference of the motif role lanes. -/
def shrinkingGraph (layout : Bool) (count : Fin 4 → ℕ) (order : ShrinkEdge P count ↪ ℕ)
    (hc : 2 ≤ c) (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset) :
    LiftedSlots (V × Tag) (d*(3*(2^c*d)/4)*(∑ e, count e)) L := by
  letI : LinearOrder (ShrinkEdge P count) := LinearOrder.lift' _ order.injective
  let srcRole := fun t => (supplyRoles layout t).1
  let dstRole := fun t => (supplyRoles layout t).2
  exact CompressorRegularize.graph (fun e => base (slotSite P layout srcRole e))
    (fun e => base (slotSite P layout dstRole e))
    (fun e => (slotSite P layout dstRole e).2.2 - (slotSite P layout srcRole e).2.2)
    (fun b => incident_count P layout srcRole count b hc)
    (fun b => incident_count P layout dstRole count b hc) (ends_ne P hn good layout count)

/-- Zero-width padding uses one fixed nonzero translation of the tag,
leaving the old vertex and the remaining lane unchanged. -/
def tagPadding (t : Tag) (ht : t ≠ 0) (n : ℕ) : LiftedSlots (V × Tag) n L where
  base := {
    target := ((Equiv.refl V).prodCongr (Equiv.addRight t)).prodCongr (Equiv.refl _)
    ends_ne := by
      rintro ⟨⟨v,a⟩,i⟩ h
      have he : a + t = a := congrArg Prod.snd h
      exact ht (add_left_cancel (show a + t = a + 0 by simpa only [add_zero] using he))
  }
  displacement _ := 0

/-- The requested larger degree is obtained from the actual parallel
slots and the common zero-width deficit, with no loops in either part. -/
def regularizedShrinkingGraph (layout : Bool) (count : Fin 4 → ℕ) (order : ShrinkEdge P count ↪ ℕ)
    (hc : 2 ≤ c) (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (t : Tag) (ht : t ≠ 0) (D : ℕ) (fits : d*(3*(2^c*d)/4)*(∑ e, count e) ≤ D) :
    LiftedSlots (V × Tag) D L :=
  let used := d*(3*(2^c*d)/4)*(∑ e, count e)
  (show used + (D-used) = D by omega) ▸
    CompressorRefresh.union (shrinkingGraph P layout count order hc hn good) (tagPadding t ht (D-used))

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
