import OAI.Computability.VPVNP.CompressionHistory

/-!
# Field records for the actual slots of a compression pass

At each output site, keep the local motif records, both half-fields of every
placed old vertex in every slot, and the new site's incoming and outgoing fields.
Outgoing fields in these records cover the entire output width profile.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

open NetworkKernel
open scoped Classical

variable {a b g n : ℕ}

/-- An outgoing slot reads its own arc and an incoming slot recovers its
source by the inverse of the actual slot permutation. -/
def State.halfWidth (X : State a g) (v : X.network.Site) (direction : Bool) (j : Fin (2 ^ a)) : ℕ :=
  let e := ((v.1, j), v.2)
  X.width (if direction then X.slots.actualTarget.symm e else e)

theorem State.halfWidth_le_max (X : State a g) (v : X.network.Site) (dir : Bool) (j : Fin (2 ^ a)) :
    X.halfWidth v dir j ≤ X.maxWireWidth := X.width_le_maxWireWidth _

variable {R : Type*} [CommSemiring R] {X : State a g}

namespace StatePass

/-- Identify the term's output site with its site in the new lifted state. -/
def outputSite (p : StatePass R X b n) (i : p.step.Choice) :
    (p.step.term i).output.Site ≃ (p.next i).network.Site :=
  Equiv.cast (congrArg Network.Site (p.output_eq i))

/-- Include all old and new slot fields alongside the motif's local entries. -/
noncomputable def slotRecords (p : StatePass R X b n) (extra : p.Records) : p.Records := fun i v =>
  { Field := (extra i v).Field ⊕ (((p.step.term i).Preimage v × (Bool × Fin (2 ^ a))) ⊕
        (Bool × Fin (2 ^ b)))
    fieldFintype := inferInstance
    width := Sum.elim (extra i v).width (Sum.elim
      (fun x => X.halfWidth x.1.val x.2.1 x.2.2)
      (fun x => (p.next i).halfWidth (p.outputSite i v) x.1 x.2))
    Map := (extra i v).Map
    mapFintype := inferInstance
    degree := (extra i v).degree }

set_option backward.isDefEq.respectTransparency false in
theorem slotRecords_count (p : StatePass R X b n) (extra : p.Records) (i : p.step.Choice)
    (v : (p.step.term i).output.Site) :
    (p.slotRecords extra i v).count = (extra i v).count +
      Fintype.card ((p.step.term i).Preimage v) * (2 * 2 ^ a) + 2 * 2 ^ b := by
  simp [SiteRecords.count, slotRecords, Fintype.card_sum, Fintype.card_prod, Nat.add_assoc]

/-- One constant bounds the substep even when the old graph, widths, placements,
and selected terms vary. The extra records describe the local motif computations. -/
theorem slotRecords_bounded (p : StatePass R X b n) (extra : p.Records) (A D E : ℕ) (hE : 1 ≤ E)
    (hpre : ∀ i v, Fintype.card ((p.step.term i).Preimage v) ≤ A)
    (hcount : ∀ i v, (extra i v).count ≤ D)
    (hextra : ∀ i v, (extra i v).largest ≤ E * (X.maxWireWidth + 1))
    (hnext : ∀ i e, (p.next i).width e ≤ E * (X.maxWireWidth + 1)) :
    p.Bounded (p.slotRecords extra) (max (D + A * (2 * 2 ^ a) + 2 * 2 ^ b + A) (E + 1)) := by
  intro i
  refine ⟨fun v => ?_, ?_, ?_⟩
  · rw [slotRecords_count]
    apply le_trans _ (le_max_left _ _)
    gcongr <;> first | exact hpre i v | exact hcount i v
  · have hb : TermChain.largest (p.slotRecords extra i) ≤ E * (X.maxWireWidth + 1) := by
      apply Finset.sup_le
      intro v _
      apply max_le
      · apply Finset.sup_le
        rintro (e | (e | e)) _
        · exact ((extra i v).width_le_largest e).trans (hextra i v)
        · exact (X.halfWidth_le_max _ _ _).trans (by nlinarith [Nat.zero_le X.maxWireWidth])
        · exact hnext i _
      · apply Finset.sup_le
        intro j _
        exact ((extra i v).degree_le_largest j).trans (hextra i v)
    calc
      _ ≤ E * (X.maxWireWidth + 1) + 1 := Nat.succ_le_succ hb
      _ ≤ (E + 1) * (X.maxWireWidth + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_right _ _)
  · apply Finset.sup_le
    rintro ⟨⟨x,j⟩, lane⟩ _
    let v := (p.outputSite i).symm (x, lane)
    have h := (p.slotRecords extra i v).width_le_largest (.inr (.inr (false,j)))
    change (p.next i).halfWidth (p.outputSite i v) false j ≤ _ at h
    rw [show p.outputSite i v = (x,lane) from (p.outputSite i).apply_symm_apply _] at h
    exact h.trans (Finset.le_sup (f := fun u => (p.slotRecords extra i u).largest) (Finset.mem_univ v))

end StatePass
end Compression

end VPVNP
end Computability
end OAI
