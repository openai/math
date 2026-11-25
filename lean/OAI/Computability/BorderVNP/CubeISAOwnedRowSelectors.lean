import OAI.Computability.BorderVNP.CubeISAOwnedScatterRow
import OAI.Computability.BorderVNP.CubeISAOwnedScatterSingleRow

/-! # Reading packet selectors after the packet and singleton scatters

Distinct packets occupy disjoint consecutive banks at their global indices.
The singleton array is a separate reservation. Thus the vertex-directory
pass can validate the actual stored selectors after all three scatter passes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM Tally
open RoutingISA.OwnedVertex (bankAt)

namespace PacketRowData

variable {n d blocks b h K s w : ℕ} (D : PacketRowData n d blocks b h K s)

private theorem visit_other (p q : Packet n d blocks) (different : p ≠ q) (z : State w)
    (stride : bankWidth n b h K s ≤ D.stride) (j : Fin (selectorWidth n K h)) :
    (D.visit q z).mem (bankAt D.base D.stride p+j.val) = z.mem (bankAt D.base D.stride p+j.val) := by
  let addr := bankAt D.base D.stride p+j.val
  let dst := bankAt D.base D.stride q
  have len : (D.body q).length = bodyWidth n b h s := List.length_ofFn
  have span : selectorWidth n K h+bodyWidth n b h s ≤ D.stride := by
    simpa [bankWidth,supplyBase,bodyWidth,Nat.add_assoc] using stride
  have out : addr < dst ∨ dst+selectorWidth n K h+bodyWidth n b h s ≤ addr := by
    have ne : packetIndex p ≠ packetIndex q := fun e => different (packetIndex_injective e)
    rcases lt_or_gt_of_ne ne with low | high
    · have step := Nat.mul_le_mul_right D.stride low
      change (packetIndex p+1)*D.stride ≤ _ at step
      rw [Nat.add_mul,one_mul] at step
      dsimp only [addr,dst,bankAt]
      exact Or.inl (by have := j.isLt; omega)
    · have step := Nat.mul_le_mul_right D.stride high
      change (packetIndex q+1)*D.stride ≤ _ at step
      rw [Nat.add_mul,one_mul] at step
      dsimp only [addr,dst,bankAt]
      exact Or.inr (by omega)
  change image (D.body q) (dst+selectorWidth n K h) (image (selectorPositions (D.select q)) dst z.mem)
    addr = z.mem addr
  rw [image_outside _ _ _ (by rw [len]; omega)]
  apply image_outside
  have length : (selectorPositions (D.select q)).length = selectorWidth n K h := List.length_ofFn
  rw [length]; omega

/-- The final packet-bank prefix holds each physical selector after all other
packets have written their (disjoint) data rectangles. -/
theorem final_stored (m : Memory w) (positive : 1 < 2^w) (stride : bankWidth n b h K s ≤ D.stride)
    (p : Packet n d blocks) (row : p.1.1 D.axis = D.pair) :
    SelectorRead.Stored (readings (D.before m (packetTrials n d blocks)).mem)
      (bankAt D.base D.stride p) (D.select p) := by
  let t := (packetRowEquiv D.axis D.pair).symm ⟨p,row⟩
  have he : D.packet t.val t.property = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
  let base := bankAt D.base D.stride p
  have initial : SelectorRead.Stored (readings (D.before m (t.val.val+1)).mem) base (D.select p) := by
    rw [D.before_visit m t.val t.property,he]
    intro j
    have original := selectorImage_stored (D.before m t.val.val).mem base (D.select p) positive j
    have lower : base+j.val < base+selectorWidth n K h := Nat.add_lt_add_left j.isLt _
    change (image (D.body p) (base+selectorWidth n K h)
      (image (selectorPositions (D.select p)) base (D.before m t.val.val).mem) (base+j.val)).val = _
    rw [image_outside _ _ _ (.inl lower)]
    exact original
  have keep {k : ℕ} (lo : t.val.val+1 ≤ k) (hi : k ≤ packetTrials n d blocks) :
      SelectorRead.Stored (readings (D.before m k).mem) base (D.select p) := by
    induction lo with
    | refl => exact initial
    | @step l prev ih =>
      let u : Fin (packetTrials n d blocks) := ⟨l,hi⟩
      by_cases ok : packetTrialValid u
      · rw [D.before_visit m u ok]
        have diff : p ≠ D.packet u ok := by
          intro eqn
          have er : packetRowEquiv D.axis D.pair t = packetRowEquiv D.axis D.pair ⟨u,ok⟩ :=
            Subtype.ext (he.trans eqn)
          have ev := congrArg (fun x : {t : Fin (packetTrials n d blocks) // packetTrialValid t} => x.val.val)
            ((packetRowEquiv D.axis D.pair).injective er)
          change t.val.val = l at ev
          exact Nat.not_succ_le_self l (ev ▸ prev)
        intro j
        exact (congrArg Fin.val (D.visit_other p _ diff _ stride j)).trans (ih (by omega) j)
      · rw [D.before_skip m u ok]
        exact ih (by omega)
  exact keep t.val.isLt le_rfl

end PacketRowData

namespace SingleRowData

variable {n d len w : ℕ} (D : SingleRowData n d len)

/-- Singleton writes leave every earlier-addressed packet word unchanged, at
every intermediate trial as well as at the end of the oriented row. -/
theorem before_below_bank (m : Memory w) (k addr : ℕ) (below : addr < D.bank) :
    (D.before m k).2 addr = m addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < singlePairTrials n d
    · let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
      by_cases yes : D.selected t
      · rw [D.before_visit m t yes]
        exact (image_outside _ _ _ (.inl (below.trans_le (Nat.le_add_right _ _)))).trans ih
      · rw [D.before_skip m t yes]
        exact ih
    · simpa only [before,hk,dite_false] using ih

end SingleRowData

end Cube.Scatter

end BorderVNP
end Computability
end OAI
