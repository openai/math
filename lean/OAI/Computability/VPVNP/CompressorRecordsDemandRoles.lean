import OAI.Computability.VPVNP.CompressorRecordsDemandRAM
import OAI.Computability.VPVNP.CompressorRecordsBundleInputs
import OAI.Computability.VPVNP.CompressorRecordsBundleRoleIndex

/-!
# Absolute shrinking arc records and the selected role sites

The native demand pass reads a site-major old arc and writes in the
lane-minor old arc order of the surviving-slot compiler. The two orders are
permutations of all directed old slots, including parallel and zero-width slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DemandRAM

open Compression BurstRAM VPVNP.CompressorRecords.Shrink
open scoped Fin.CommRing

variable {w a g : ℕ}

private theorem of_val {x : Word w} {n : ℕ} (h : x.val = n) : x = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

private theorem div_val (x y : Word w) : (ShrinkRAM.div x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem old_low {V : Type} {N : ℕ} (order : V ≃ Fin N) (s : Old V a g) :
    oldNumber order s % 2^g = (bitWordFinEquiv g s.1.2.2).val := by
  let b := join a (join (colors a) (order s.1.1).val (bitWordFinEquiv (colors a) s.2.1).val)
    (bitWordFinEquiv a s.2.2).val
  have h : oldNumber order s = (b*2^(J a)+(bitWordFinEquiv (J a) s.1.2.1).val)*2^g +
      (bitWordFinEquiv g s.1.2.2).val := by
    change b*2^(J a+g)+((bitWordFinEquiv (J a) s.1.2.1).val*2^g+(bitWordFinEquiv g s.1.2.2).val) = _
    rw [pow_add]; ring
  rw [h, Nat.mul_add_mod_of_lt (Fin.isLt _)]

theorem address_exact {V : Type} {n : ℕ} (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) {p : Fin 11 → Word w} {B : ℕ}
    (hp : BundleRAM.Params p a (colors a) (J a) g B) (e : BundleKeys.OldArc V a g)
    {i : Word w} (hi : i.val = (BundleKeys.oldArcOrder order e).val) :
    address p i = p 10 + 4 * ((Slots.oldArcIndex (orderedDyadicPacking G order) order
      (bitWordFinEquiv (J a)) (bitWordFinEquiv g) e).val : Word w) := by
  have ho := BundleKeys.oldArcOrder_val order e
  have hq : i.val/2^a = oldNumber order (sourcePosition e) := by
    rw [hi,ho, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt e.1.2.isLt, Nat.add_zero]
  have hs : i.val%2^a = e.1.2.val := by rw [hi,ho, Nat.mul_add_mod_of_lt e.1.2.isLt]
  have hl : ShrinkRAM.mod (BundleRAM.sourceSite p i) (p 1) = ((bitWordFinEquiv g e.1.1.2.2).val : Word w) := by
    change (((ShrinkRAM.div i (p 0)).val % (p 1).val : ℕ) : Word w) = _
    rw [div_val, hp.degree,hp.residual,hq,old_low]
    rfl
  unfold address
  rw [BundleRAM.decode_exact hp, hq, hs, hl, BundleKeys.oldArcIndex_eq_key_lane G order]
  simp only [BundleKeys.keyAt, BundleKeys.numericKey, Bool.false_eq_true, ite_false,
    of_val hp.degree, of_val hp.mask, of_val hp.tag, of_val hp.residual, Nat.cast_add, Nat.cast_mul]

/-- Physical source and destination site numbers in the preceding placement directory. -/
theorem site_inputs (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
    {p : Fin 11 → Word w} {m : Memory w} (inc : T.ActualColumns X m) (hd : (p 0).val = 2^a)
    (hOut : p 5 = T.actualOut) (fit : Fintype.card X.Base*2^(packingLaneBits a g)*2^a ≤ 2^w)
    (e : BundleKeys.OldArc X.Base a g) {i : Word w} (hi : i.val = (BundleKeys.oldArcOrder X.baseIndex e).val) :
    BundleRAM.sourceSite p i = ShrinkRAM.word w (oldNumber X.baseIndex (sourcePosition e)) ∧
    BundleRAM.targetSite p m i = ShrinkRAM.word w (oldNumber X.baseIndex (sourcePosition (X.packingData.actual e))) := by
  have num (u : BundleKeys.OldArc X.Base a g) :
      IncidenceDirectory.actualPort (w := w) X (packingInputEdges X.Base a g u) =
        ShrinkRAM.word w (BundleKeys.oldArcOrder X.baseIndex u).val := by
    rw [BundleKeys.oldArcOrder_val, Shrink.oldNumber_original]; rfl
  have src : i = IncidenceDirectory.actualPort X (packingInputEdges X.Base a g e) := by
    rw [num]; exact of_val hi
  constructor
  · exact BundleRAM.site_quotient X _ hd e _ hi
  · apply BundleRAM.site_quotient X _ hd (X.packingData.actual e)
    rw [hOut, src, inc.actualOut, ← BundleRAM.input_target, num]
    exact Nat.mod_eq_of_lt ((BundleKeys.oldArcOrder X.baseIndex (X.packingData.actual e)).isLt.trans_le fit)

/-- The demand worker's public inputs point to the old outgoing incidence and the shrink pass's
thickness, owner, assigned-bundle and target columns. -/
structure Inputs (p : Fin 11 → Word w) (shr : Fin 14 → Word w) (T : IncidenceDirectory w) : Prop where
  incidence : p 5 = T.actualOut
  thick : p 6 = shr 11
  owner : p 7 = shr 10
  assigned : p 8 = shr 12
  target : p 9 = shr 13

/-- All four values of the selected demand role record. The CD flag is defined
on every old arc; the other three outputs agree with A, B, D on every actual motif. -/
theorem roles_exact (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w)
    {p : Fin 11 → Word w} {shr : Fin 14 → Word w} {m : Memory w} {layout : Bool}
    (h : Inputs p shr T) (inc : T.ActualColumns X m)
    (place : ShrinkRAM.PlacementColumns X.slots X.baseIndex shr layout m) (hd : (p 0).val = 2^a)
    (fit : Fintype.card X.Base * 2^(packingLaneBits a g) * 2^a ≤ 2^w)
    (e : BundleKeys.OldArc X.Base a g) {i : Word w} (hi : i.val = (BundleKeys.oldArcOrder X.baseIndex e).val) :
    let P := X.packingData
    let z := roles p m i
    z.cd = (if Slots.isCD P e then 1 else 0) ∧
      ∀ hm : Slots.isCD P e, z.A = (packedNumber X.baseIndex (P.roleA ⟨e,hm⟩) : Word w) ∧
        z.B = (packedNumber X.baseIndex (P.roleB ⟨e,hm⟩) : Word w) ∧
        z.D = (packedNumber X.baseIndex (P.roleD layout ⟨e,hm⟩) : Word w) := by
  let P := X.packingData
  let s := sourcePosition e
  let t := sourcePosition (P.actual e)
  let code (x : Old X.Base a g) := ShrinkRAM.word w (oldNumber X.baseIndex x)
  obtain ⟨hs,ht⟩ := site_inputs X T inc hd h.incidence fit e hi
  have reads (x : Old X.Base a g) :
      m (p 6+code x).val = ((decide (P.thick x)).toNat : Word w) ∧
      ShrinkRAM.div (m (p 8+code x).val) (p 0) = (packedNumber X.baseIndex (P.assignedBundle x).1 : Word w) ∧
      m (p 9+code x).val = (packedNumber X.baseIndex (P.siteGraph.target (P.assignedBundle x)).1 : Word w) ∧
      m (p 7+code x).val = (packedNumber X.baseIndex (P.placement layout x) : Word w) := by
    have ⟨ho,hth,ha,hb⟩ := Prod.mk.inj (place.atSite x) |>.imp_right Prod.mk.inj |>.imp_right (And.imp_right Prod.mk.inj)
    change (m (shr 10+code x).val).val = _ at ho
    change (m (shr 11+code x).val).val = _ at hth
    change (m (shr 12+code x).val).val = _ at ha
    change (m (shr 13+code x).val).val = _ at hb
    rw [h.thick,h.owner,h.assigned,h.target]
    refine ⟨of_val hth, ?_, of_val hb, of_val ho⟩
    apply of_val
    rw [div_val, ha, hd, Shrink.join, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (P.assignedBundle x).2.isLt, Nat.add_zero]
  let cPos := if P.thick s then t else s
  let dPos := if P.thick s then s else t
  have ends : endpoints p m i = (code cPos, code dPos) := by
    unfold endpoints
    rw [hs,ht]
    change (code s + m (p 6+code s).val*(code t-code s),code t-m (p 6+code s).val*(code t-code s)) = _
    rw [(reads s).1]
    by_cases hts : P.thick s <;> simp [hts,cPos,dPos]
  dsimp only
  constructor
  · change 1 - m (p 6+BundleRAM.sourceSite p i).val*m (p 6+BundleRAM.targetSite p m i).val =
      if ¬(P.thick s ∧ P.thick t) then 1 else 0
    rw [hs,ht,(reads s).1,(reads t).1]
    by_cases h₁ : P.thick s <;> by_cases h₂ : P.thick t <;> simp [h₁,h₂]
  · intro hm
    change ShrinkRAM.div (m (p 8+(endpoints p m i).1).val) (p 0) = _ ∧
      m (p 9+(endpoints p m i).1).val = _ ∧ m (p 7+(endpoints p m i).2).val = _
    rw [ends]
    exact ⟨(reads cPos).2.1,(reads cPos).2.2.1,(reads dPos).2.2.2⟩

end CompressorRecords.DemandRAM

end VPVNP
end Computability
end OAI
