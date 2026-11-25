import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyNodup
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyImage

/-! # Physical ordinal of every native rectangle register -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization
open IntegerMultiplication.Strip

variable {g : Frame} (r : Realization g)

/-- Exact register coverage at every boundary of the eleven-instruction stage. -/
theorem code_codec (n : ℕ) : Codec (bank g n) (r.code n) := by
  have lb := label_codec (g:=g)
  have base := lb.append (box_codec (g:=g)) (bank_nodup g 3)
  have spec := lb.append (query_codec (g:=g)) (List.Nodup.of_append_left (bank_nodup g 7))
  match n with
  | 0 => exact lb
  | 1 => exact lb.append (r.endpoint_codec false) (bank_nodup g 1)
  | 2 => exact lb.append (r.queryEndpoint_codec false) (bank_nodup g 2)
  | 3 => exact base
  | 4 => exact base.append (r.term_codec true) (bank_nodup g 4)
  | 5 => exact base.append r.rank_codec (bank_nodup g 5)
  | 6 => exact base.append (r.term_codec false) (bank_nodup g 6)
  | 7 => exact spec.append box_codec (bank_nodup g 7)
  | 8 => exact spec.append (r.queryEndpoint_codec true) (bank_nodup g 8)
  | 9 => exact lb.append (r.endpoint_codec true) (bank_nodup g 9)
  | 10 => exact lb.append (r.endpoint_codec true) (bank_nodup g 10)
  | _+11 => exact lb

theorem code_mem (n : ℕ) (a : r.Boundary n) : r.code n a ∈ bank g n :=
  (r.code_codec n).mem a

theorem code_injective (n : ℕ) : Function.Injective (r.code n) := (r.code_codec n).injective

theorem physRank_lt (n : ℕ) (a : r.Boundary n) : (bank g n).idxOf (r.code n a) < (bank g n).length :=
  List.idxOf_lt_length_of_mem (r.code_mem n a)

def physRank (n : ℕ) (a : r.Boundary n) : Fin (bank g n).length :=
  ⟨(bank g n).idxOf (r.code n a),r.physRank_lt n a⟩

theorem physRank_get (n : ℕ) (a : r.Boundary n) :
    (bank g n).get (r.physRank n a) = r.code n a :=
  List.getElem_idxOf (r.physRank_lt n a)

theorem physRank_bijective (n : ℕ) : Function.Bijective (r.physRank n) := by
  constructor
  · intro a b e
    exact r.code_injective n ((r.physRank_get n a).symm.trans
      ((congrArg (bank g n).get e).trans (r.physRank_get n b)))
  · intro i
    obtain ⟨a,ha⟩ := ((r.code_codec n).image _).mp (List.mem_of_getElem (l:=bank g n) (i:=i.val) rfl)
    refine ⟨a,Fin.ext ?_⟩
    change (bank g n).idxOf (r.code n a) = i.val
    rw [ha]
    exact (bank_nodup g n).idxOf_getElem i.val i.isLt

noncomputable def indexEquiv (n : ℕ) : r.Boundary n ≃ Fin (bank g n).length :=
  Equiv.ofBijective (r.physRank n) (r.physRank_bijective n)

@[simp] theorem indexEquiv_val (n : ℕ) (a : r.Boundary n) :
    ((r.indexEquiv n) a).val = (bank g n).idxOf (r.code n a) := rfl

/-- The actual typed traversal has precisely the compiled physical order. -/
noncomputable def order (n : ℕ) : Series (r.Boundary n) where
  explore := (List.finRange (bank g n).length).map (r.indexEquiv n).symm
  nodup := (List.nodup_finRange _).map (r.indexEquiv n).symm.injective
  complete a := List.mem_map.mpr ⟨(r.indexEquiv n) a,List.mem_finRange _,(r.indexEquiv n).symm_apply_apply a⟩

theorem order_tab (n : ℕ) : (r.order n).tab (r.code n) = bank g n := by
  have h (i : Fin (bank g n).length) :
      r.code n ((r.indexEquiv n).symm i) = (bank g n).get i := by
    have eq := r.physRank_get n ((r.indexEquiv n).symm i)
    change (bank g n).get (r.indexEquiv n ((r.indexEquiv n).symm i)) = _ at eq
    rw [Equiv.apply_symm_apply] at eq
    exact eq.symm
  change ((List.finRange _).map (r.indexEquiv n).symm).map (r.code n) = _
  rw [List.map_map]
  exact (List.map_congr_left (fun i _ => h i)).trans (List.map_get_finRange _)

/-- This is the reindexing used for the route ledger; no zero-cost or unused slot
is introduced by the translation to ordinal row numbers. -/
theorem sum_bank {A : Type*} [AddCommMonoid A] (n : ℕ) [Fintype (r.Boundary n)] (price : Role → A) :
    ((bank g n).map price).sum = ∑ i, price (r.code n i) := by
  rw [← Fin.sum_univ_fun_getElem]
  symm
  apply Fintype.sum_equiv (r.indexEquiv n)
  intro i
  exact congrArg price (r.physRank_get n i).symm

end InterchangeROMStage.Frame.Realization

end NearSquareRoot
end Computability
end OAI
