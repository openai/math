import OAI.Hierarchy.DescentOperandSelectorWidth
import OAI.Hierarchy.DescentSelectorNativeCharge
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # The five conditioned reads, final ticket dictionary, and eight returned expressions -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open DescentDatedOperandSelectionRun DescentStaticWordColumn ProtocolRAM
noncomputable section
variable (g : Geometry) (s : Sources g)

private theorem read_fee {cols count n : ℕ} (q : Fin 5)
    (law : Fin 1 → (Fin n → Cell g.digitBits) → Cell (keyWidth count))
    (args : Fin g.jobs → Fin n → Expr) (head : Fin g.jobs → Fin cols → Fin count → Expr)
    (base w h ratio short limit : ℕ)
    (shape : n=readArity q ∧ cols=returnedFields q ∧ count=candidateCount g q)
    (fit : purchase g*g.lanes≤ h/2) (bus : w≤ ratio*h) (fill : h≤ g.lanes*short)
    (keys : ∀j i,(args j i).work≤ limit) (heads : ∀j f i,(head j f i).work≤ limit) :
    (readStage g law args head base w).wordInvoice≤ scanCharge g q h ratio short limit :=by
  obtain ⟨hn,hc,hk⟩:=shape
  have ar : n≤17:=by rw [hn];fin_cases q <;> decide
  have mux : DescentResetStemMux.unit (keyWidth count) g.digitBits*g.lanes≤ h/2 :=by
    rw [hk];exact selector_room g q fit
  have billed:=stage_word_bill (layout g cols count) law (fun _=>0)
    (fun p=>args (finProdFinEquiv.symm p).1)
    (fun p=>head (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
    base w h ratio short limit limit bus fill (family_room g ar fit) mux
    (fun p i=>keys _ i) (fun p i=>heads _ _ i)
  refine billed.trans_eq ?_
  unfold scanCharge selectionFactor
  rw [←hn,←hc,←hk]
  change readFactor 1 n count limit limit*ratio*(g.jobs*cols+1)*(h+g.hosts*h+g.hosts*g.groups*short)+
    readFactor 1 n count limit limit*ratio*(g.jobs*cols+1)*2^(h/2)*h = _
  ring

private theorem bank_fee (base w h ratio : ℕ) (fit : purchase g*g.lanes≤ h/2) (bus : w≤ ratio*h) :
    (bankPhase g base w).wordInvoice≤ finalCharge h ratio :=by
  have cells:=DescentOperandFamilyBook.size_le 8 17 g.digitBits g.lanes h (family_room g (by decide) fit)
  have names_:=Book.names (DescentOperandFamilyBook.gates (finalLaw g)) (DescentOperandFamilyBook.unit 17 g.digitBits)
    g.lanes w (finalBase g base)
  let size:=DescentOperandFamilyBook.words 8 17 g.digitBits g.lanes
  change (4+10*size+7*names (DescentOperandFamilyBook.program (finalLaw g) g.lanes (finalBase g base) w))*w≤_
  change names (DescentOperandFamilyBook.program (finalLaw g) g.lanes (finalBase g base) w)=15*(size+1) at names_
  change size≤(17+8)*(2*2^(h/2)) at cells
  rw [names_]
  have price : 4+10*size+7*(15*(size+1))≤8192*(1+2^(h/2)):=by omega
  exact (Nat.mul_le_mul price bus).trans_eq (by unfold finalCharge;ring)

/-- The complete prefix is paid on arbitrary memory. Its only data-dependent cost
parameter bounds the native syntax of the numerical input fields. -/
theorem phase_charge (base w h ratio short limit : ℕ) (fit : purchase g*g.lanes≤ h/2)
    (bus : w≤ ratio*h) (fill : h≤ g.lanes*short) (input : Sources.Work g s limit) (read : 7≤ limit) :
    (phase g s base w).wordInvoice≤ scanCharge g 0 h ratio short limit+scanCharge g 1 h ratio short limit+
      scanCharge g 2 h ratio short limit+scanCharge g 3 h ratio short limit+scanCharge g 4 h ratio short limit+
      finalCharge h ratio :=by
  have lookupWork (n cols C start : ℕ) (j : Fin g.jobs) (f : Fin cols) :
      (lookup g n cols C start j f).work≤ limit :=read
  have oldWork (j : Fin g.jobs) (f : Fin 4) : (old g base j f).work≤ limit :=lookupWork ..
  have pathWork (j : Fin g.jobs) : (path g base j).work≤ limit:=lookupWork ..
  have anchorWork (j : Fin g.jobs) (f : Fin 5) : (anchor g base j f).work≤ limit:=lookupWork ..
  have a : (oldPhase g s base w).wordInvoice≤ scanCharge g 0 h ratio short limit:=by
    apply read_fee g 0 _ _ _ _ _ _ _ _ _ ⟨rfl,rfl,rfl⟩ fit bus fill _ input.old
    intro j i
    fin_cases i <;> first | exact input.origin _ _ | exact input.prior _ _
  have b : (pathPhase g s base w).wordInvoice≤ scanCharge g 1 h ratio short limit:=by
    apply read_fee g 1 _ _ _ _ _ _ _ _ _ ⟨rfl,rfl,rfl⟩ fit bus fill _ (fun _ _ i=>input.path i)
    intro j i
    fin_cases i <;> first | exact input.origin _ _ | exact oldWork _ _
  have c : (anchorPhase g s base w).wordInvoice≤ scanCharge g 2 h ratio short limit:=by
    apply read_fee g 2 _ _ _ _ _ _ _ _ _ ⟨rfl,rfl,rfl⟩ fit bus fill _ input.anchor
    intro j i
    fin_cases i <;> first | exact input.origin _ _ | exact input.prior _ _ | exact input.mouth _ _ | exact oldWork _ _ | exact pathWork _
  have d : (rawPhase g s base w).wordInvoice≤ scanCharge g 3 h ratio short limit:=by
    apply read_fee g 3 _ _ _ _ _ _ _ _ _ ⟨rfl,rfl,rfl⟩ fit bus fill _ input.raw
    intro j i
    fin_cases i <;> first | exact input.origin _ _ | exact input.mouth _ _ | exact anchorWork _ _ | exact pathWork _
  have e : (rankPhase g s base w).wordInvoice≤ scanCharge g 4 h ratio short limit:=by
    apply read_fee g 4 _ _ _ _ _ _ _ _ _ ⟨rfl,rfl,rfl⟩ fit bus fill _ (fun _ _ i=>input.rank i)
    intro j i
    fin_cases i <;> first | exact input.origin _ _ | exact input.prior _ _
  have f:=bank_fee g base w h ratio fit bus
  simp only [phase,NativePhase.wordInvoice_seq]
  omega

theorem expression_charge (base limit : ℕ) (input : Sources.Work g s limit) (read : 7≤ limit)
    (j : Fin g.jobs) (f : Fin 8) : (expression g s base j f).work≤14+17*(limit+11) :=by
  apply source_work
  intro i
  fin_cases i <;> first | exact input.origin _ _ | exact input.prior _ _ | exact input.mouth _ _ | exact read

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
