import OAI.Hierarchy.DescentDatedOperandReadPipeline

namespace OAI
/-! # The local width shared by the five published selections and the final ticket table -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates ProtocolRAM
noncomputable section
variable (g : Geometry)

theorem family_room {h n : ℕ} (arity : n≤17) (fit : purchase g*g.lanes≤ h/2) :
    DescentOperandFamilyBook.unit n g.digitBits*g.lanes≤ h/2 :=by
  apply (Nat.mul_le_mul_right g.lanes _).trans fit
  apply (le_trans _ (Nat.le_max_left _ _))
  unfold DescentOperandFamilyBook.unit
  have step:=Nat.mul_le_mul_left g.digitBits arity
  omega

theorem selector_room (q : Fin 5) {h : ℕ} (fit : purchase g*g.lanes≤ h/2) :
    DescentResetStemMux.unit (keyWidth (candidateCount g q)) g.digitBits*g.lanes≤ h/2 :=by
  have count : candidateCount g q≤ candidateLimit g:=Finset.le_sup (Finset.mem_univ q)
  have key :=Nat.clog_mono_right 2 (Nat.add_le_add_right count 1)
  apply (Nat.mul_le_mul_right g.lanes _).trans fit
  refine (le_trans ?_ (Nat.le_max_right _ _))
  unfold DescentResetStemMux.unit
  exact max_le_max (Nat.add_le_add_right key _) le_rfl

theorem endAddress_eq_pipelineWords (base : ℕ) : endAddress g base=base+g.pipelineWords :=by
  rw [footprint]
  congr 1
  unfold endAddress finalBase rankBase rawBase anchorBase pathBase after
    DescentDatedOperandSelectionRun.endAddress DescentDatedOperandSelectionRun.nextAddress
    DescentDatedOperandMux.endAddress DescentDatedOperandMux.start DescentDatedOperandMux.tables DescentDatedOperandMux.span
    DescentOperandFamilyBook.endAddress DescentOperandFamilyBook.words DescentOperandFamilyBook.unit
    DescentResetStemMux.words DescentResetStemMux.unit
    Geometry.pipelineWords Geometry.stageWords
  simp only [layout,keyWidth,Nat.zero_add,Nat.add_assoc]; rfl

/-- Work of the incoming physical row expressions at the candidate and origin ports. -/
structure Sources.Work (s : Sources g) (limit : ℕ) : Prop where
  origin : ∀j f,(s.origin j f).work≤ limit
  prior : ∀j f,(s.prior j f).work≤ limit
  mouth : ∀j f,(s.mouth j f).work≤ limit
  old : ∀j f i,(s.old j f i).work≤ limit
  path : ∀i,(s.path i).work≤ limit
  anchor : ∀j f i,(s.anchor j f i).work≤ limit
  raw : ∀j f i,(s.raw j f i).work≤ limit
  rank : ∀i,(s.rank i).work≤ limit

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
