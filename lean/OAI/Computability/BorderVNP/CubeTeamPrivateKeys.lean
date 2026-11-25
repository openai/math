import OAI.Computability.BorderVNP.CubeTeamPrivateKeysRows
import OAI.Computability.BorderVNP.CubeScatterGlobalCrossKeys
import OAI.Computability.BorderVNP.CubeTeamRowDispatch

/-! # Bijection from physical private bits to the actual ordered team words

The team visits each directed symbol pair in ascending square-array order
and enters the local row program exactly when it owns the first symbol.
Two groups on the same team contribute their separate endpoint views.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical

variable {n d blocks h K : ℕ} {Team : Type*} [DecidableEq Team]
variable (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1))
variable (owner : Fin d → Team) (team : Team)

/-- Actual finite row block read by the selected team at the given square ordinal. -/
def teamBlock (q : Fin (d*d)) : List (Assignment.BitIndex b s select) :=
  let v := finProdFinEquiv.symm q
  if owner v.1 = team then rowPrivateKeys select i b s v else []

/-- Chronological private-key list of one team's outer symbol scan. -/
def teamPrivateKeys : List (Assignment.BitIndex b s select) :=
  (List.finRange (d*d)).flatMap (teamBlock b s select i owner team)

private theorem teamBlock_mem (q : Fin (d*d)) (k : Assignment.BitIndex b s select) :
    k ∈ teamBlock b s select i owner team q ↔
      privateView i k = some (finProdFinEquiv.symm q) ∧ owner (finProdFinEquiv.symm q).1 = team := by
  simp [teamBlock,rowPrivateKeys_mem,and_comm]

/-- The team's list is exhaustive exactly on its physical private routing fiber. -/
theorem teamPrivateKeys_mem (k : Assignment.BitIndex b s select) :
    k ∈ teamPrivateKeys b s select i owner team ↔ Assignment.route i owner k = .inr team := by
  simp only [teamPrivateKeys,List.mem_flatMap,List.mem_finRange,true_and,teamBlock_mem,route_private_iff_view]
  constructor
  · rintro ⟨q,hq⟩; exact ⟨_,hq⟩
  · rintro ⟨v,hv⟩; exact ⟨finProdFinEquiv v,by simpa only [Equiv.symm_apply_apply] using hv⟩

/-- Distinct directed endpoint views have disjoint private keys, including
when the same physical team enters both endpoint programs. -/
theorem teamPrivateKeys_nodup : (teamPrivateKeys b s select i owner team).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun q _ => ?_,(List.nodup_finRange (d*d)).imp ?_⟩
  · dsimp only [teamBlock]
    split <;> first | exact rowPrivateKeys_nodup .. | exact List.nodup_nil
  · intro q r ne
    exact List.disjoint_left.mpr fun k hq hr => ne (finProdFinEquiv.symm.injective (Option.some.inj
      (((teamBlock_mem ..).mp hq).1.symm.trans ((teamBlock_mem ..).mp hr).1)))

/-- Fixed-length arbitrary private tapes at every physical team. Lengths are
those of the actual local loops after the packet selectors are fixed. -/
abbrev TeamPrivateWords :=
  (t : Team) → {xs : List Bool // xs.length = (teamPrivateKeys b s select i owner t).length}

private def fiberKeys := (teamPrivateKeys b s select i owner team).attachWith
  (fun k => Assignment.route i owner k = .inr team) (fun _ hk => (teamPrivateKeys_mem ..).mp hk)

/-- A fixed private team word has exactly one labeling of its entire routed
fiber. The inverse reads the chronological index of each physical bit. -/
noncomputable def teamPrivateEquiv :
    ({k : Assignment.BitIndex b s select // Assignment.route i owner k = .inr team} → Bool) ≃
      {xs : List Bool // xs.length = (teamPrivateKeys b s select i owner team).length} := by
  classical
  let ks := fiberKeys b s select i owner team
  have cover (x : {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inr team}) : x ∈ ks :=
    (List.mem_attachWith _ x).mpr ((teamPrivateKeys_mem ..).mpr x.property)
  have nd : ks.Nodup := List.Nodup.of_map Subtype.val
    (by simpa only [ks,fiberKeys,List.attachWith_map_subtype_val] using teamPrivateKeys_nodup b s select i owner team)
  let ord := List.Nodup.getEquivOfForallMemList ks nd cover
  have len : ks.length = (teamPrivateKeys b s select i owner team).length := List.length_attachWith ..
  refine ⟨fun f => ⟨ks.map f,by simp only [List.length_map,len]⟩,
    fun xs k => xs.val[(ord.symm k).val]'(by rw [xs.property,← len]; exact (ord.symm k).isLt),?_,?_⟩
  · intro f
    funext k
    simp only [List.getElem_map]
    exact congrArg f (ord.apply_symm_apply k)
  · intro xs
    apply Subtype.ext
    apply List.ext_getElem (by simpa only [List.length_map] using len.trans xs.property.symm)
    intro j hj _
    have hj' : j < ks.length := by simpa using hj
    have eq : ord.symm (ks[j]) = ⟨j,hj'⟩ := ord.symm_apply_apply ⟨j,hj'⟩
    simp [eq]

/-- One independent native team tape per private physical routing fiber. -/
noncomputable def privateWordsEquiv :
    PrivateBitChoices b s select i owner ≃ TeamPrivateWords b s select i owner :=
  Equiv.piCongrRight (fun t => teamPrivateEquiv b s select i owner t)

/-- Shared suffixes and actual private team words together represent every
physical choice, with a unique inverse even when strict rows are co-owned. -/
noncomputable def nativeWordsEquiv :
    Assignment.Choices b s select i owner ≃ StrictCrossWords b s select i × TeamPrivateWords b s select i owner :=
  (choiceWordsEquiv b s select i owner).trans ((Equiv.refl _).prodCongr (privateWordsEquiv b s select i owner))

/-- Reading the encoded team's private word amounts to looking up its ordered
list in the original distributed assignment. -/
theorem nativeWordsEquiv_private (f : Assignment.Choices b s select i owner) :
    (((nativeWordsEquiv b s select i owner) f).2 team).val =
      (teamPrivateKeys b s select i owner team).map (Assignment.lookup f) := by
  change (fiberKeys b s select i owner team).map (f (.inr team)) = _
  rw [← List.attachWith_map_subtype_val (fun k hk => (teamPrivateKeys_mem b s select i owner team k).mp hk),
    List.map_map]
  apply List.map_congr_left
  rintro ⟨k,hk⟩ _
  change f (.inr team) ⟨k,hk⟩ = Assignment.lookup f k
  have read (r : Assignment.Region d Team) (h : Assignment.route i owner k = r) :
      f r ⟨k,h⟩ = Assignment.lookup f k := by subst r; rfl
  exact read _ hk

end Cube.Scatter

end BorderVNP
end Computability
end OAI
