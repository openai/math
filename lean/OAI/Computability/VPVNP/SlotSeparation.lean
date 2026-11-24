import OAI.Computability.VPVNP.SlotPacking
import OAI.Computability.VPVNP.SlotTags

/-!
# Separation of the three bases in each shrinking motif

Appendix C of *VP and VNP differ over every field* assigns one base and
tag to each packed position. Both layouts keep the three roles of a motif
at distinct such pairs. The binary tag group makes an arc displacement
the same in both directions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

variable {V H Tag L : Type*} {d c : ℕ}

/-- The base after packing consists of the old base and the packed tag. -/
def packedBase (s : Site V Tag L) : V × Tag := (s.1, s.2.1)

namespace PackingData

variable [AddCommGroup H] [AddCommGroup Tag] [Module (ZMod 2) Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- The tag component of the old arc displacement. -/
def tagShift (e : V × Fin d) : Tag := (P.siteShift e).1

private theorem motifTagConditions (m : P.Motif)
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset) :
    ∃ t, (P.D m).1.2.1 = (P.C m).1.2.1 + t ∧
      (∀ a, P.offset (P.C m).1.1 ≠ t + tagIncrement P.tagShift (P.C m).1.1 a) ∧
      ∀ a b, P.offset (P.C m).1.1 + P.offset (P.D m).1.1 ≠ t +
        tagIncrement P.tagShift (P.C m).1.1 a + tagIncrement P.tagShift (P.D m).1.1 b := by
  let e := (m.val.1.1.1, m.val.1.2)
  obtain ⟨hout, hin, hpair⟩ := hφ e
  refine ⟨P.tagShift e, ?_⟩
  by_cases hs : P.thick (sourcePosition m.val)
  · simp only [D, C, ite_eq_left hs]
    refine ⟨?_, hin, ?_⟩
    · change m.val.1.1.2.1 = m.val.1.1.2.1 + P.tagShift e + P.tagShift e
      rw [add_assoc, ZModModule.add_self, add_zero]
    · intro a b
      change P.offset (P.slots.target e).1 + P.offset e.1 ≠ P.tagShift e +
        tagIncrement P.tagShift (P.slots.target e).1 a + tagIncrement P.tagShift e.1 b
      simpa only [add_comm, add_left_comm, add_assoc] using hpair b a
  · simp only [D, C, ite_eq_right hs]
    exact ⟨rfl, hout, hpair⟩

/-- Excluding the unary and binary shifts keeps either bundle tag distinct
from the placed tag of the other endpoint, for each choice of layout. -/
private theorem tag_ne_placed (m : P.Motif) (layout : Bool)
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset) (a : Option (Fin d)) :
    (P.C m).1.2.1 + (P.offset (P.C m).1.1 + tagIncrement P.tagShift (P.C m).1.1 a) ≠
      (P.roleD layout m).2.1 := by
  obtain ⟨t, htag, hsingle, hpair⟩ := P.motifTagConditions m hφ
  by_cases hd : P.thick (P.D m)
  · rw [roleD, placement, ite_eq_left hd, htag]
    intro he
    exact hsingle a ((eq_sub_iff_add_eq.mpr (add_left_cancel he)).trans (ZModModule.sub_eq_add ..))
  · have placed : ∃ b, (P.roleD layout m).2.1 = (P.D m).1.2.1 +
          (P.offset (P.D m).1.1 + tagIncrement P.tagShift (P.D m).1.1 b) := by
      cases layout with
      | false =>
        refine ⟨none, ?_⟩
        rw [roleD, placement, ite_eq_right hd]
        change _ = _ + (_ + 0)
        rw [add_zero]
        rfl
      | true =>
        refine ⟨some (P.slotLabel (P.D m).2.2), ?_⟩
        rw [roleD, placement, ite_eq_right hd]
        exact add_assoc ..
    obtain ⟨b, hb⟩ := placed
    rw [hb, htag, add_assoc (P.C m).1.2.1 t]
    intro he
    have h := add_left_cancel he
    let u := P.offset (P.C m).1.1
    let v := P.offset (P.D m).1.1
    let s := tagIncrement P.tagShift (P.C m).1.1 a
    let r := tagIncrement P.tagShift (P.D m).1.1 b
    change u + s = t + (v + r) at h
    apply hpair a b
    change u + v = t + s + r
    calc
      u + v = (u + v) + (s + s) := by rw [ZModModule.add_self, add_zero]
      _ = (u + s) + (v + s) := by ac_rfl
      _ = (t + (v + r)) + (v + s) := by rw [h]
      _ = (t + s + r) + (v + v) := by ac_rfl
      _ = t + s + r := by rw [ZModModule.add_self, add_zero]

/-- The packed bases of the three roles are pairwise distinct in every
motif, simultaneously for the source and target layouts. -/
theorem distinct_roleBases (hφ : P.slots.ValidTagOffsets P.tagShift P.offset)
    (layout : Bool) (m : P.Motif) :
    packedBase (P.roleA m) ≠ packedBase (P.roleB m) ∧
    packedBase (P.roleA m) ≠ packedBase (P.roleD layout m) ∧
    packedBase (P.roleB m) ≠ packedBase (P.roleD layout m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact P.slots.ends_ne ((P.C m).1.1, P.slotLabel (P.C m).2.2) (congrArg Prod.fst h).symm
  · intro h
    apply P.tag_ne_placed m layout hφ none
    change _ + (_ + 0) = _
    rw [add_zero]
    exact congrArg Prod.snd h
  · intro h
    apply P.tag_ne_placed m layout hφ (some (P.slotLabel (P.C m).2.2))
    rw [← add_assoc]
    exact congrArg Prod.snd h

end PackingData

end Compression

end VPVNP
end Computability
end OAI
