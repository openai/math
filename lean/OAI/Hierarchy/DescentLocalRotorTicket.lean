import OAI.Hierarchy.DescentPackedTicketChronology
import OAI.Hierarchy.DescentPhysicalFallbackPanel
import OAI.Hierarchy.DescentSignedRotorPair
import OAI.Hierarchy.DescentResetDigits

namespace OAI
/-! # The native directed reservation serial counts the signed rows of its one source cell -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentPackedTicketChronology DescentPacking StarKeys
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "fits" => frame.enough.trans (Nat.sub_le ..)
local notation "R" => Z.placement
local notation "E" => Grain A
local notation "endAt" => DescentIssuedFallbackPanel.endSite (W:=W) A
local notation "use" => useRotor (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "headAt" => base (R).b (R).depth (R).L (R).keys (R).hub (R).old
local notation "ticketKey" => DescentOrderedReset.grains W A.grainCount order
local notation "native" => order.trans Fin.valEmbedding

def sameRotorPair (p : {e : E // use e}) (e : E) : Prop :=
  ∃good : use e,∀s,headAt ⟨e,good⟩ s=headAt p s

def rotorSourceHigh (side : Bool) (p : {e : E // use e}) : Block c :=
  selectedRoot A S ready Z T (T.home (endAt side p.val))

theorem sameRotorPair_source (side : Bool) (p : {e : E // use e}) (e : E)
    (eqn : sameRotorPair A S ready Z p e) :
    (A.pos (endAt side e)).2=(A.pos (endAt side p.val)).2 ∧
      group c (rearrange frame.basis (oldBlock digits (home A (endAt side e))))=
        (rotorSourceHigh A S ready Z T side p).val := by
  obtain ⟨good,same⟩:=eqn
  have row (f : E) (ok : use f) :
      T.code (T.home (endAt side f))=
        goodAddress (R).b (R).keys (R).hub (headAt ⟨f,ok⟩ side,(R).row side ((R).old side f)) := by
    have ident : endAt side f=ends (Wold).graph side f:=by cases side <;> rfl
    exact (congrArg T.code ((congrArg T.home ident).trans (T.attach side f))).trans (T.source side f ok)
  have eRow:=row e good
  have pRow:=row p.val p.property
  rw [same side] at eRow
  constructor
  · apply frame.host.injective
    exact (frame.homeHost (endAt side e)).symm.trans ((congrArg Prod.fst eRow).trans
      ((congrArg Prod.fst pRow).symm.trans (frame.homeHost (endAt side p.val))))
  · change group c (rearrange frame.basis (filled W.graph A.pos A.block digits (endAt side e)))=
      coarseName c (T.code (T.home (endAt side p.val)))
    exact (frame.homeHigh (endAt side e)).symm.trans ((congrArg (coarseName c) eRow).trans
      (congrArg (coarseName c) pRow).symm)

def rotorPrevious (p : {e : E // use e}) (e : E) : Bool :=
  decide (DescentPackedTicketChronology.before
    (originalId W.graph.Site (W.graph.src e.1)) (outgoingSlot A S ready order e).val e.2.val
    (originalId W.graph.Site (W.graph.src p.val.1)) (outgoingSlot A S ready order p.val).val p.val.2.val)

theorem true_ticket_count (tickets : (R).OrderedTickets ticketKey) (sorted : SourceSorted W order)
    (side : Bool) (p : {e : E // use e}) :
    ((R).ticket p).2.val=(Finset.univ.filter (fun j=>
      (panel A native S ready digits frame.basis fits side (A.pos (endAt side p.val)).2
        (rotorSourceHigh A S ready Z T side p) (sameRotorPair A S ready Z p) j).any
        (rotorPrevious A S ready order Z p))).card % (R).span ((R).ticket p).1 := by
  rw [DescentIssuedFallbackPanel.count _ _ _ _ _ _ _ _ _ _ _ (sameRotorPair_source A S ready digits Z T frame side p)]
  refine (tickets.serial p).trans ?_
  congr 1
  apply Finset.card_bij (fun x _=>x.val)
  · intro x hx
    obtain ⟨prior,baseEq⟩ := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x.property,baseEq⟩,
      decide_eq_true ((actual_before A S ready order sorted x.val p.val).mp prior)⟩
  · intro x _ y _ eqn
    exact Subtype.ext eqn
  · intro y hy
    obtain ⟨⟨ok,baseEq⟩,prior⟩ := (Finset.mem_filter.mp hy).2
    exact ⟨⟨y,ok⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (actual_before A S ready order sorted y p.val).mpr (of_decide_eq_true prior),baseEq⟩,rfl⟩

/-- At the scheduled reset, the full input digit read by the existing inverse-GL comparator
is exactly the numerically ordered group and previous low block. -/
theorem old_inputDigit {tail : ℕ} (baseGroups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (A₀ : GroupStage W G q ε (Fin (S.groupCount i)) V k) (u : W.graph.Site) :
    (filled W.graph A₀.pos A₀.block (S.resetInputDigits baseGroups radix i) u).val=
      (A₀.pos u).1.val*2^k+(A₀.block u).val := by
  change (finProdFinEquiv ((A₀.pos u).1,A₀.block u)).val=_
  change (A₀.block u).val+2^k*(A₀.pos u).1.val=_
  ring

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
