import OAI.Computability.VPVNP.LiveVirtualPairContinuation

/-! # The canonical virtual pair's reset memory in the live shadow array -/

namespace OAI
namespace Computability
namespace VPVNP

namespace FixedProgramDiagonal.Program

open BurstRAM Compression CursorNetwork LiveProgram PairStages PairStages.Group PrimedInputRAM
open ExponentTrace CutSchedule

private theorem lengths_cast {h h' Δ Δ' a a' : ℕ} (hh : h=h') (hd : Δ=Δ') (ha : a=a') (i : Fin (2^h)) :
    PairedChain.lengths h' Δ' a' (i.cast (congrArg (2^·) hh)) = PairedChain.lengths h Δ a i := by
  subst h'; subst Δ'; subst a'
  rfl

variable {D : FixedProgramDiagonal.Program} {n C : ℕ}
    {ht : 21 ≤ 2^(D.geometry n).w} {hf : 44 ≤ n^10000}

/-- Transport a fixed-program pair index to the actual execution group's auxiliary index type
using equality of the two chain heights. -/
noncomputable abbrev physicalPairIndex (i : D.groupIndices n) : Fin (2^(Auxiliary.sizes (D.executionGroup n ht hf)).h) :=
  i.cast (congrArg (2^·) heights)

theorem physicalPairLengths (i : D.groupIndices n) :
    Auxiliary.pairLengths (D.executionGroup n ht hf) (physicalPairIndex i) = D.pairLengths i :=
  lengths_cast heights deltas adviceSizes i

private theorem shadow_cast (G : Group) {i : Fin (2^(Auxiliary.sizes G).h)}
    {L : PrimedInputRAM.Lengths} (hL : Auxiliary.pairLengths G i = L) (Q : Layout L G.g.n G.g.d G.g.H G.w)
    (degree : Fin G.g.n) (root : Fin (Auxiliary.states G)) (hdr : Header L → Bool) (μ : Nominations.Nom G)
    {m : Memory G.w} {N : Indexed G Stage.nominations m (Nominations.Nom G)}
    (P : Auxiliary.PreparedBranch G m i (hL.symm ▸ hdr) N μ) (a : ℕ) :
    P.copy.memory () ((Auxiliary.shadow G).val+a) =
      (PrimedCounter.Data.ofNomination Q degree root hdr (Auxiliary.nominationEquiv G μ)).initial a := by
  subst L
  exact Auxiliary.shadow_initial Q degree root hdr μ P a

universe v
variable {K : Type v} [Field K] {S : BlockSchedule K} {B : S.Templates} {hn : 2 ≤ n}
    {u : PairExponents B.growthConstant} (V : D.VirtualPairs B u hn C)
    (hC : D.constants.circuitExponent = C) (adv : Bits (n^D.constants.advicePower))
    (ξ : Exterior (D.chainHeight n) (n^D.constants.deltaPower)) (i : D.groupIndices n)
    (μ : Nominations.Nom (D.executionGroup n ht hf))

set_option maxHeartbeats 900000 in
/-- The sparse-copy entry of the actual live machine agrees at every
address with the reset memory of the canonical auxiliary pair. This
includes the seven input arrays, unoccupied sparse slots and unused RAM. -/
theorem VirtualPairs.shadow_initial {m : Memory (D.executionGroup n ht hf).w}
    {N : Indexed (D.executionGroup n ht hf) Stage.nominations m (Nominations.Nom (D.executionGroup n ht hf))}
    (P : Auxiliary.PreparedBranch (D.executionGroup n ht hf) m (physicalPairIndex i)
      ((physicalPairLengths (ht := ht) (hf := hf) i).symm ▸ PairedChain.headers adv ξ i) N μ) (a : ℕ) :
    P.copy.memory () ((Auxiliary.shadow (D.executionGroup n ht hf)).val+a) =
      (V.data adv ξ i (physicalNomination hC μ)).initial a := by
  subst C
  exact shadow_cast (D.executionGroup n ht hf) (physicalPairLengths i) (V.layout i)
    ⟨n-1,by change n-1<n; omega⟩ ⟨0,Nat.pow_pos (by omega : 0<n)⟩ (PairedChain.headers adv ξ i) μ P a

end FixedProgramDiagonal.Program

end VPVNP
end Computability
end OAI
