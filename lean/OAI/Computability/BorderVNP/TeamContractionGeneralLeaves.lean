import OAI.Computability.BorderVNP.TeamContractionPhysical

/-! # Signed contraction from a physical row dictionary with arbitrary finite leaf sets

The first public frame initiates traversal. A successful row provides the next frame on
the true shared links. This reconstructs the incoming frames even though arbitrary link
assignments, viewed independently of a successful leaf, need not encode valid frames.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape TeamSiteConsistency Wires TeamSite TeamSiteEvents TeamTapeHandoff TeamSiteTraversal
open scoped BigOperators Classical
open private elapsed from OAI.Computability.BorderVNP.TeamContractionPhysical

variable {teams w p regs k a e m g : ℕ} {Q Γ : Type}

/-- Finite physical leaf sets indexed by the actual interior bits and the real processor. -/
abbrev SiteLeaves (teams regs w e : ℕ) :=
  (Edge teams regs w e (w+1) → Bool) → Fin teams → Finset (List Bool × Bool)

/-- Row recognition on a supplied decoded predecessor, with all register, sort and sign checks. -/
def LeafDictionary (M : Setup teams w p regs k a e) (leaves : SiteLeaves teams regs w e) : Prop :=
  ∀ links j incoming, Reads (edgeEquiv links).1 M.first j incoming → ∀ bits neg,
    (bits,neg) ∈ leaves links j ↔
      ∃ es out, EndpointRow M.program M.pub M.lib M.block M.limit M.cap incoming es out ∧
        Writes (edgeEquiv links).1 j out ∧ sorted M.width M.sorter M.input links j incoming es ∧
        bits = chunkBits es ∧ chunkSign (some false) es = some neg

private abbrev LeafTuple (leaves : SiteLeaves teams regs w e) :=
  Σ links, (j : Fin teams) → ↥(leaves links j)

variable (M : Setup teams w p regs k a e) (leaves : SiteLeaves teams regs w e)
variable (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (hlib : M.lib = macros lib fuel)
variable (bound : max 1 (fuel-1) ≤ M.privateClock) (law : LeafDictionary M leaves)

private theorem sign_get (z : M.NonzeroHistories) (j : Fin teams) :
    chunkSign (some false) (z.val.val.blocks j) = some ((chunkSign (some false) (z.val.val.blocks j)).getD false) := by
  have h := (rawWeight_ne_zero_iff z.val.val).mp z.property j
  cases eq : chunkSign (some false) (z.val.val.blocks j) with
  | none => simp [eq] at h
  | some b => rfl

/-- The unique script tuple of a nonzero history, reading its own register wires and signs. -/
private def spell (z : M.NonzeroHistories) : LeafTuple leaves :=
  ⟨z.val.val.links, fun j => ⟨(chunkBits (z.val.val.blocks j),(chunkSign (some false) (z.val.val.blocks j)).getD false),by
    obtain ⟨rows,last,frames,owners⟩ := (M.endpointChecks_iff_fuel z.val.val lib fuel hlib bound).mpr z.val.property
    let f := predecessor M.first z.val.val.frames j
    have both := frame_conditions (edgeEquiv z.val.val.links).1 M.first _ _ frames last j
    exact (law _ j f both.1 ..).mpr ⟨_,_,rows j,both.2,
      (sorted_iff_global M.width M.sorter M.input _ _ j f (elapsed M rows j)).mpr (owners j),rfl,sign_get M z j⟩⟩⟩

private theorem spell_injective : Function.Injective (spell M leaves lib fuel hlib bound law) := by
  intro x y eq
  apply Subtype.ext
  apply histories_unique_fuel M lib fuel hlib bound x.val y.val
  · exact congrArg Sigma.fst eq
  · intro j
    exact congrArg (fun z : LeafTuple leaves => (z.2 j).val.1) eq

private theorem spell_surjective : Function.Surjective (spell M leaves lib fuel hlib bound law) := by
  rintro ⟨links,tuple⟩
  let row (j : Fin teams) (f : Frame w regs) (es : List (TeamRAM.Event w)) (out : Frame w regs) :=
    EndpointRow M.program M.pub M.lib M.block M.limit M.cap f es out ∧
      sorted M.width M.sorter M.input links j f es ∧ chunkBits es = (tuple j).val.1 ∧
      chunkSign (some false) es = some (tuple j).val.2
  have find (j : Fin teams) (f : Frame w regs) (read : Reads (edgeEquiv links).1 M.first j f) :
      ∃ es out, row j f es out ∧ Writes (edgeEquiv links).1 j out := by
    obtain ⟨es,out,check,write,sort,bits,sign⟩ := (law links j f read ..).mp (tuple j).property
    exact ⟨es,out,⟨check,sort,bits.symm,sign⟩,write⟩
  obtain ⟨blocks,input,outs,frames,rows,last⟩ := collect (edgeEquiv links).1 M.first row find
  obtain rfl : input = predecessor M.first outs := (frameChecks_iff.mp frames).2
  let z : RawHistory teams regs w e := ⟨blocks,outs,links⟩
  have checks : M.EndpointChecks z := by
    refine ⟨fun j => (rows j).1,last,frames,fun j => ?_⟩
    exact (sorted_iff_global M.width M.sorter M.input links blocks j (predecessor M.first outs j)
      (elapsed M (fun j => (rows j).1) j)).mp (rows j).2.1
  have nz : z.weight ≠ 0 := (rawWeight_ne_zero_iff z).mpr (fun j => (rows j).2.2.2 ▸ rfl)
  let hist : M.NonzeroHistories := ⟨⟨z,(M.endpointChecks_iff_fuel z lib fuel hlib bound).mp checks⟩,nz⟩
  refine ⟨hist,congrArg (Sigma.mk links) (funext fun j => Subtype.ext (Prod.ext (rows j).2.2.1 ?_))⟩
  change (chunkSign (some false) (blocks j)).getD false = _
  rw [(rows j).2.2.2]
  rfl

include hlib bound law in
/-- The entire finite signed leaf contraction equals the native value on the true shared
memory. Only the row dictionary for a decoded predecessor is required of the physical leaves. -/
theorem nativeValue_of_leaf_dictionary :
    (∑ links, ∏ j, ∑ z : ↥(leaves links j), TeamTape.haltWeight true z.val.2) =
      nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  let weight (s : LeafTuple leaves) : ℤ := ∏ j, TeamTape.haltWeight true (s.2 j).val.2
  let bij : M.NonzeroHistories ≃ LeafTuple leaves := Equiv.ofBijective _
    ⟨spell_injective M leaves lib fuel hlib bound law,spell_surjective M leaves lib fuel hlib bound law⟩
  have wgt (z : M.NonzeroHistories) : weight (bij z) = z.val.val.weight := by
    rw [rawWeight_prod]
    apply Finset.prod_congr rfl
    intro j _
    change TeamTape.haltWeight true ((chunkSign (some false) (z.val.val.blocks j)).getD false) = _
    have h := sign_get M z j
    generalize eq : chunkSign (some false) (z.val.val.blocks j) = b at h ⊢
    rcases b with _ | (_ | _) <;> first | contradiction | rfl
  let := Fintype.ofFinite (NativePath M.machine M.limit.val M.cap.val M.privateClock)
  rw [nativeValue_nonzero]
  calc
    _ = ∑ s : LeafTuple leaves, weight s := by
      refine Eq.trans ?_ (Fintype.sum_sigma' (fun links tuple => weight ⟨links,tuple⟩)).symm
      exact Finset.sum_congr rfl fun links _ => Fintype.prod_sum (fun j (z : ↥(leaves links j)) =>
        TeamTape.haltWeight true z.val.2)
    _ = _ := by
      apply Fintype.sum_equiv (bij.symm.trans M.nonzeroEquiv)
      intro s
      exact ((congrArg weight (bij.apply_symm_apply s)).symm.trans (wgt (bij.symm s))).trans
        (M.rawEquivNative_weight (bij.symm s).val)

end TeamContraction

end BorderVNP
end Computability
end OAI
