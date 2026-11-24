import OAI.Computability.VPVNP.LiveProgramPairPreparation
import OAI.Computability.VPVNP.PrimedCounterTranscriptCountLabels

/-! # The live nomination order and the auxiliary machine's initial memory -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM PrimedInputRAM PrimedCounter PrimedStackRAM

variable (G : Group)

/-- Concrete grammar state count used when interpreting the live histogram, `n^(circuitExponent
+ 5)`. -/
abbrev states := G.g.n^(G.constants.circuitExponent+5)
/-- Formal nomination assigning a count of width twice the site-address width to each grammar
production over the group’s state set. -/
abbrev FormalNom := GrammarDiagonal.Nomination G.g.n G.g.n (2*G.g.d) (Fin (states G))

/-- Lexicographic production positions in the grammar are exactly the
positions of the dense array guessed by the live nomination stage. -/
noncomputable def order : GrammarLabel (Fin G.g.n × Bool) (Fin (states G)) G.g.n ≃ Fin (histLength G) :=
  (labelIndex G.g.n G.g.n (states G)).trans
    (finCongr (G.constants.grammarLabels_eq G.g).symm)

/-- Relabel the dense live nomination array by the grammar’s lexicographic production order,
preserving every count word. -/
noncomputable def nominationEquiv : Nominations.Nom G ≃ FormalNom G :=
  Equiv.arrowCongr (order G).symm (Equiv.refl _)

variable {G} {i : Fin (2^(sizes G).h)} (Q : PrimedInputRAM.Layout (pairLengths G i) G.g.n G.g.d G.g.H G.w)
  (degree : Fin G.g.n) (root : Fin (states G)) (hdr : Header (pairLengths G i) → Bool) (μ : Nominations.Nom G)

theorem histogram_eq :
    (Data.ofNomination Q degree root hdr (nominationEquiv G μ)).hist = histogram G μ := by
  unfold Data.hist histogram
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact (G.constants.grammarLabels_eq G.g).symm
  · intro k hk hk'
    simp only [List.getElem_ofFn,Data.ofNomination_word]
    change Fin.ofNat _ (μ ((order G) ((labelIndex _ _ _).symm _))).val = Fin.ofNat _ (μ _).val
    rw [order,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl

/-- Every address of the actual auxiliary RAM, including unused addresses,
has its prescribed value immediately after the linked copy stage. -/
theorem shadow_initial {m : Memory G.w} {N : Indexed G Stage.nominations m (Nominations.Nom G)}
    (B : PreparedBranch G m i hdr N μ) (a : ℕ) :
    B.copy.memory () ((shadow G).val+a) = (Data.ofNomination Q degree root hdr (nominationEquiv G μ)).initial a := by
  rw [B.shadowRead,Data.initial,histogram_eq]
  rfl

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
