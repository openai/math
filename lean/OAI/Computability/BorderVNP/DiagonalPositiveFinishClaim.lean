import OAI.Computability.BorderVNP.DiagonalPositiveFinishInput

/-! # Eliminating exactly one shared claim from all true native finishing runs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM DiagonalTallyRAM
open scoped BigOperators Classical

variable {reserve axes groups cap T dim width w : ℕ}
local notation "Finish" => finishExpansion signedOccurrences

/-- Fix all source profile and cube bits, varying only the proposed shared
subtotal bank as the true native contraction does. -/
def withSubtotals (p : (PositiveFields reserve axes groups cap T dim width)) (raw : (Fin (T*dim*width) → Bool)) : (PositiveFields reserve axes groups cap T dim width) := {p with subtotals := raw}

theorem canonical_tallyWords (p : (PositiveFields reserve axes groups cap T dim width)) (rows : Fin T → Fin dim → ℕ) :
    (p.withSubtotals (canonicalSubtotals width rows)).tallyWords = DiagonalTallyRAM.broadcast width rows := by
  unfold tallyWords withSubtotals
  rw [ofFn_canonicalSubtotals,splitFields_broadcast]

/-- At one genuine collection of post-cell states, the all-team condition is
equivalent to equality of the complete raw common claim with its true bit vector. -/
theorem finishes_iff (p : (PositiveFields reserve axes groups cap T dim width)) (rows : Fin T → Fin dim → ℕ) (pub : Fin T → Arg → Word w)
    (mac : Fin T → TeamOpcode.Macros w 8) (state : Fin T → Bank w) (mem : Fin T → Memory w)
    (input : ∀ u, FinishInput u rows width (pub u) (mac u) (state u) (mem u) p.tallyWords)
    (wordFit : width ≤ w) (bounded : ∀ u c, rows u c < 2^width) (sumFit : ∀ c, ∑ u,rows u c < 2^w) :
    (∀ u, Nonempty (Returns Finish (pub u) (mac u) (state u) (mem u))) ↔ p.subtotals = canonicalSubtotals width rows := by
  constructor
  · intro returns
    have unique := JointHeader.unique_claim_bits rows wordFit bounded
    have canonical := ofFn_canonicalSubtotals width rows
    apply List.ofFn_inj.mp
    apply Eq.trans _ canonical.symm
    exact unique.unique (y₁:=List.ofFn p.subtotals) (y₂:=(DiagonalTallyRAM.broadcast width rows).flatten)
      ⟨List.length_ofFn,fun u c => (input u).sound (returns u).some c⟩
      ⟨flat_length rows width,fun u c => by rw [splitFields_broadcast,fieldWord_broadcast rows bounded]⟩
  · intro eq u
    have xs : p.tallyWords = DiagonalTallyRAM.broadcast width rows := by
      unfold tallyWords
      rw [eq,ofFn_canonicalSubtotals,splitFields_broadcast]
    exact ⟨((input u).complete xs bounded sumFit).choose⟩

variable (p : (PositiveFields reserve axes groups cap T dim width)) (rows : Fin T → Fin dim → ℕ)
variable (pub : (Fin (T*dim*width) → Bool) → Fin T → Arg → Word w) (mac : (Fin (T*dim*width) → Bool) → Fin T → TeamOpcode.Macros w 8)
variable (state : (Fin (T*dim*width) → Bool) → Fin T → Bank w) (mem : (Fin (T*dim*width) → Bool) → Fin T → Memory w)
variable (input : ∀ raw u, FinishInput u rows width (pub raw u) (mac raw u) (state raw u) (mem raw u)
    (p.withSubtotals raw).tallyWords)
variable (wordFit : width ≤ w) (bounded : ∀ u c, rows u c < 2^width) (sumFit : ∀ c, ∑ u,rows u c < 2^w)

/-- The genuinely dependent claim and all actual native finishing histories have
multiplicity exactly one. Even their starting memories may depend on the raw claim. -/
noncomputable def finishClaimEquiv : (Σ raw : (Fin (T*dim*width) → Bool), (u : Fin T) →
    Returns Finish (pub raw u) (mac raw u) (state raw u) (mem raw u)) ≃ Unit := by
  let canonical := canonicalSubtotals width rows
  let result := fun u : Fin T => ((input canonical u).complete (canonical_tallyWords p rows) bounded sumFit).choose
  refine { toFun := fun _ => ()
           invFun := fun _ => ⟨canonical,result⟩
           left_inv := ?_
           right_inv := fun _ => rfl }
  rintro ⟨raw,path⟩
  have eq : raw=canonical := (finishes_iff (p.withSubtotals raw) rows (pub raw) (mac raw) (state raw)
    (mem raw) (input raw) wordFit bounded sumFit).mp (fun u => ⟨path u⟩)
  subst raw
  exact congrArg (Sigma.mk canonical) (funext fun u => finish_eq (result u) (path u))

/-- The inverse puts the canonical digits on the wire. -/
theorem finishClaimEquiv_raw :
    ((finishClaimEquiv p rows pub mac state mem input wordFit bounded sumFit).symm ()).1 = canonicalSubtotals width rows := rfl

/-- The inverse retains the actual final memory. Its serialized total cells are
at the physical address needed by the entry reader, even when the reader returns zero. -/
theorem finishClaimEquiv_output (u : Fin T) (c : Fin dim) (j : ℕ) (hj : j<w) :
    let final := (finishClaimEquiv p rows pub mac state mem input wordFit bounded sumFit).symm ()
    let h := input final.1 u
    (final.2 u).val.2.2 (h.post.localBase+dim+T*dim+dim+dim+1+(c.val*w+j)) =
      word w (((∑ v,rows v c).testBit j).toNat) := by
  exact ((input (canonicalSubtotals width rows) u).complete (canonical_tallyWords p rows) bounded sumFit).choose_spec.2.2 c j hj

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
