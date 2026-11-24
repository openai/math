import OAI.Computability.VPVNP.CompressorShrinkTermPhases

/-!
# Allocation of the shrinking term phase

Following the sorted width and field-start tables, reserve a pair of
words per motif for the inputs and a strided row for each selected term.
One bound on the end of this last region certifies both native segments
and preservation of the six earlier columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermSelection

open BurstRAM Compression.PackingData

variable {w : ℕ}

theorem packed_arena (s : Fin 5 → BurstRAM.Word w) (B d c prefixHead termStride : ℕ)
    (live : pieceCount d c ≤ (s 3).val)
    (afterWidths : (s 4).val+2*(B*(s 3).val) ≤ prefixHead)
    (fits : prefixHead+2*(B*(s 3).val)+2*B+4*(B*pieceCount d c)+(B*pieceCount d c)*termStride < 2^w) :
    let Q := pieceCount d c
    let N := B*Q
    let t := BundlePrefixGraph.prefixPublic s B d c prefixHead false
    let u := BundlePrefixGraph.prefixPublic s B d c prefixHead true
    let abStart := prefixHead+2*(B*(s 3).val)+2*B
    let p := DemandWidths.packedPublic (t 4) B Q abStart
    let dense := Fin.ofNat (2^w) (abStart+2*N)
    let term := Fin.ofNat (2^w) (abStart+2*N+2*N)
    ShrinkDemandGather.Layout B Q (ShrinkTermInputs.operands u p dense) ∧
      ShrinkDemandFrame.Before B (2^c*d/4) Q t u p dense.val ∧
      dense.val+N*2 ≤ term.val ∧ term.val+N*termStride < 2^w := by
  intro Q N t u abStart p dense term
  let extent := B*(s 3).val
  change (s 4).val+2*extent ≤ prefixHead at afterWidths
  change abStart+4*N+N*termStride < 2^w at fits
  have ha : abStart = prefixHead+2*extent+2*B := rfl
  have hq : Q < 2^w := live.trans_lt (s 3).isLt
  have h₁ : (p 0).val = Q := Nat.mod_eq_of_lt hq
  have h₂ : (p 1).val = Q := Nat.mod_eq_of_lt hq
  have h₃ : (p 3).val = abStart := Nat.mod_eq_of_lt (by omega)
  have h₄ : (p 4).val = abStart+N := Nat.mod_eq_of_lt (by omega)
  have hd : dense.val = abStart+2*N := Nat.mod_eq_of_lt (by omega)
  have he : term.val = abStart+2*N+2*N := Nat.mod_eq_of_lt (by omega)
  have ht₁ : (t 1).val = (s 3).val := rfl
  have ht₂ : (t 2).val = (s 4).val := Nat.mod_eq_of_lt (s 4).isLt
  have ht₃ : (t 3).val = prefixHead := Nat.mod_eq_of_lt (show prefixHead < 2^w by omega)
  have hu₁ : (u 1).val = (s 3).val := rfl
  have hu₂ : (u 2).val = (s 4).val+extent := Nat.mod_eq_of_lt (show (s 4).val+extent < 2^w by omega)
  have hu₃ : (u 3).val = prefixHead+extent := Nat.mod_eq_of_lt (show prefixHead+extent < 2^w by omega)
  have hthick : 2^c*d/4 ≤ Q := by change _ ≤ 3*(2^c*d)/4; omega
  have oldFit : prefixHead+2*extent ≤ dense.val := by omega
  have hg₁ : (p 3).val+B*(p 1).val ≤ dense.val := by rw [h₂,h₃,hd]; change abStart+N ≤ _; omega
  have hg₂ : (u 2).val+B*(u 1).val ≤ dense.val := by rw [hu₂,hu₁]; change _ + extent ≤ _; omega
  have hdt : dense.val+2*N ≤ term.val := by omega
  have htf : term.val+N*termStride < 2^w := by omega
  refine ⟨⟨h₁,h₂.ge,hu₁ ▸ live,hg₁.trans dense.isLt.le,hg₂.trans dense.isLt.le,hdt.trans term.isLt.le,
    .inl hg₁,.inl hg₂⟩,⟨ht₁ ▸ hthick.trans live,hu₁ ▸ live,h₂.ge,?_,?_,hg₂,?_,hg₁,?_⟩,?_,htf⟩
  · rw [ht₂,ht₁]; change _+extent ≤ _; omega
  · rw [ht₃,ht₁]; change _+extent ≤ _; omega
  · rw [hu₃,hu₁]; change _+extent ≤ _; omega
  · rw [h₄,h₂,hd]; change abStart+N+N ≤ abStart+2*N; omega
  · simpa only [Nat.mul_comm N 2] using hdt

end CompressorRecords.ShrinkTermSelection

end VPVNP
end Computability
end OAI
