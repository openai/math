import OAI.Computability.BorderVNP.CubePairDirectoryModel
import OAI.Computability.BorderVNP.CubeISAOwnedPacketRank
import OAI.Computability.BorderVNP.CubeISAOwnedVertexModel
import OAI.Computability.BorderVNP.DiagonalTallyPacketBank

/-! # The native ordered label-pair address recovers the actual packet end

The kind bit distinguishes singletons. For a full pair, dividing the cable
ordinal by the block width selects the packet's block, and the remaining
ordinal selects its demand bit. The first label comparison gives the orientation
and the remaining comparisons give the actual antipodal vertex.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostAddress

open PairDirectory Physical Tally VPVNP.MotifBase

variable {n d blocks width : ℕ}

/-- Little-endian code of a product-alphabet label. -/
def code {a : ℕ} (x : Label a d) : ℕ := (finFunctionFinEquiv x).val

/-- The native digit used at each coordinate is the corresponding label symbol. -/
theorem code_digit {a : ℕ} (x : Label a d) (j : Fin a) : digit d (code x) j.val = (x j).val :=
  VertexIndex.digit_number x j

/-- The kind flag of the native pair directory detects exactly the physical full pairs. -/
theorem code_kind (u v : Label (n+1) d) : kind d (code u) (code v) (n+1) = 1 ↔ ∀ j, u j ≠ v j := by
  rw [kind_one_iff]
  constructor
  · intro h j he
    exact h j j.isLt (by rw [code_digit,code_digit,he])
  · intro h j hj he
    let k : Fin (n+1) := ⟨j,hj⟩
    exact h k (Fin.ext ((code_digit u k).symm.trans (he.trans (code_digit v k))))

private theorem flip_code (u v : Label (n+1) d) (j : Fin (n+1)) :
    flip d (code u) (code v) j.val = (decide (v j < u j)).toNat := by
  rw [PairDirectory.flip,code_digit,code_digit]
  rfl

private theorem boxDigit (u v : Label (n+1) d) (full : ∀ j, u j ≠ v j) (j : Fin (n+1)) :
    (finProdFinEquiv (((fullPairEquiv _ _) ⟨(u,v),full⟩).1 j).val).val =
      pairDigit d (code u) (code v) j.val := by
  rw [pairDigit,code_digit,code_digit]
  rcases lt_or_gt_of_ne (full j) with lt | gt
  · change ((if h : u j < v j then _ else _) : Symbols d).val.2.val +
        d*((if h : u j < v j then _ else _) : Symbols d).val.1.val = _
    rw [dite_eq_left lt,min_eq_left (show (u j).val ≤ (v j).val from lt.le),max_eq_right (show (u j).val ≤ (v j).val from lt.le)]
    ring
  · change ((if h : u j < v j then _ else _) : Symbols d).val.2.val +
        d*((if h : u j < v j then _ else _) : Symbols d).val.1.val = _
    rw [dite_eq_right gt.not_gt,min_eq_right (show (v j).val ≤ (u j).val from gt.le),max_eq_left (show (v j).val ≤ (u j).val from gt.le)]
    ring

/-- The block-zero field of a directory row plus the block number is the
stable global packet ordinal used by the team ownership scan. -/
theorem packet_rank (u v : Label (n+1) d) (full : ∀ j, u j ≠ v j) (block : Fin blocks) :
    let parts := fullPairEquiv _ _ ⟨(u,v),full⟩
    Physical.Owned.packetIndex ((parts.1,parts.2 0),block) =
      firstPacketIndex d (code u) (code v) (n+1) blocks + block.val := by
  intro parts
  unfold Physical.Owned.packetIndex firstPacketIndex
  have rank : (finFunctionFinEquiv (fun j => finProdFinEquiv (parts.1 j).val)).val =
      cubeRank d (code u) (code v) (n+1) := by
    rw [finFunctionFinEquiv_apply,cubeRank,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (· * (d*d)^j.val) (boxDigit u v full j)
  have orient : (parts.2 0).toNat = orientation d (code u) (code v) (n+1) := by
    simp only [orientation,Nat.succ_ne_zero,ite_false]
    exact (flip_code u v 0).symm
  change (_*2 + (parts.2 0).toNat)*blocks+block.val = _
  rw [rank,orient]

/-- The numeric vertex field is the corner supplied to the concrete antipodal table. -/
theorem vertex_rank (u v : Label (n+1) d) :
    (vertexOrder n (fun j => finTwoEquiv.symm (decide (v j.succ < u j.succ)))).val =
      vertexNo d (code u) (code v) (n+1) := by
  change (finFunctionFinEquiv (fun j : Fin n => finTwoEquiv.symm (decide (v j.succ < u j.succ)))).val = _
  rw [finFunctionFinEquiv_apply,vertexNo,← Fin.sum_univ_eq_sum_range,Fin.sum_univ_succ]
  simp only [Fin.val_zero,ite_eq_left,zero_add,Fin.val_succ,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Fin.val_succ,flip_code]
  have hb (b : Bool) : (finTwoEquiv.symm b).val = b.toNat := by cases b <;> rfl
  rw [hb]

/-- Exact split at a full pair, including source orientation, the ordinal quotient,
the corner, and the within-block bit. -/
theorem split_full (u v : Label (n+1) d) (j : Fin (blocks*width)) (full : ∀ k, u k ≠ v k) :
    let parts := fullPairEquiv _ _ ⟨(u,v),full⟩
    splitSlot n d blocks width ((u,v),j) =
      .inl (((parts.1,parts.2 0),(finProdFinEquiv.symm j).1),
        (fun i => finTwoEquiv.symm (parts.2 i.succ)),(finProdFinEquiv.symm j).2) := by
  intro parts
  simp only [splitSlot,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,
    Equiv.sumCompl_symm_apply_of_pos (a := (u,v)) (p := fun q : Label (n+1) d × Label (n+1) d => ∀ k, q.1 k ≠ q.2 k) full]
  rfl

/-- At a repeated symbol the native slot is the same singleton bit at both ends. -/
theorem split_single (u v : Label (n+1) d) (j : Fin (blocks*width)) (single : ¬∀ k, u k ≠ v k) :
    splitSlot n d blocks width ((u,v),j) = .inr (⟨(u,v),single⟩,j) := by
  simp only [splitSlot,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map,
    Equiv.sumCompl_symm_apply_of_neg (a := (u,v)) (p := fun q : Label (n+1) d × Label (n+1) d => ∀ k, q.1 k ≠ q.2 k) single]
  rfl

/-- Address read by a native cell-copy instruction or a padding-bit guard. -/
def address (d axes blocks width packetBank bankWidth selectors singleBank u v ordinal : ℕ) (dst : Bool) : ℕ :=
  if kind d u v axes = 1 then
    packetBank+(firstPacketIndex d u v axes blocks + ordinal/width)*bankWidth+
      (selectors+(2*vertexNo d u v axes + dst.toNat)*width+ordinal%width)
  else singleBank+(u*d^axes+v)*(blocks*width)+ordinal

/-- The emitted arithmetic address equals the reservation of the genuine singleton or packet demand end. -/
theorem address_eq_split {h b K s : ℕ} (packetBank singleBank : ℕ) (dst : Bool)
    (u v : Label (n+1) d) (j : Fin (blocks*(h*b))) :
    address d (n+1) blocks (h*b) packetBank (bankWidth n b h K s) (selectorWidth n K h)
      singleBank (code u) (code v) j.val dst =
      match splitSlot n d blocks (h*b) ((u,v),j) with
      | .inl (p,a,k) => packetBank+Physical.Owned.packetIndex p*bankWidth n b h K s+
          demandOffset n b h K (a,dst) k
      | .inr single => singleBank+(code single.1.val.1*d^(n+1)+code single.1.val.2)*(blocks*(h*b))+single.2.val := by
  by_cases full : ∀ k, u k ≠ v k
  · rw [split_full u v j full,address,ite_eq_left ((code_kind u v).mpr full)]
    simp only [packet_rank,demandOffset,endOrder_val]
    change _ = packetBank+(firstPacketIndex d (code u) (code v) (n+1) blocks+j.val/(h*b))*_+
      (selectorWidth n K h+(dst.toNat+2*(vertexOrder n (fun i => finTwoEquiv.symm (decide (v i.succ < u i.succ)))).val)*(h*b)+j.val%(h*b))
    rw [vertex_rank]
    ring
  · rw [split_single u v j full,address,ite_eq_right (fun e => full ((code_kind u v).mp e))]

end Cube.HostAddress

end BorderVNP
end Computability
end OAI
