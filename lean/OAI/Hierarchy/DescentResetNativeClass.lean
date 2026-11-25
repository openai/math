import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentResetWindowEmittedSources
import OAI.Hierarchy.DescentResetSourceClassRAM

namespace OAI
/-! # The four native header comparisons recover the actual reset source class -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open DescentSortedRoster DescentResetSourceClassRAM DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "ranking" => (Z).rawHostRank T vertexCode

theorem observed_class {pitch p : ℕ} (record : B.Recorded p) (name : B.next.V↪Fin pitch)
    (order : ∀a b,name a<name b↔ranking a<ranking b) (shelf : Fin pitch→Fin 4→Option (Fin pitch))
    (h₀ : Host) (e : Local (blocks B) h₀)
    («fields» : present shelf (name h₀.1.2)=(insert h₀.1.2 ((Z).emittedNear T h₀.1.2)).map name) :
    before shelf (name h₀.1.2) (name ((blocks B).src e.val).1.2)=(sourceClass B h₀ e).val := by
  rw [sourceClass_emitted B record,local_class name _ _ shelf _ «fields»]
  apply congrArg Finset.card
  ext v
  simp only [order]
  rfl

/-- The shared whole-word front end emits only the local rank of the
source. Its four possibly duplicated raw host words come from the same
post-reset neighbor directory as the next signed stage. -/
theorem issue_class {pitch p rows w : ℕ} (record : B.Recorded p) (name : B.next.V↪Fin pitch)
    (order : ∀a b,name a<name b↔ranking a<ranking b) (shelf : Fin pitch→Fin 4→Option (Fin pitch))
    (src : Fin 4→Expr) (query : Expr) (out : Bank) (m : Memory w)
    (h₀ : Fin rows→Host) (entry : ∀r,Local (blocks B) (h₀ r))
    («fields» : ∀r,present shelf (name (h₀ r).1.2)=(insert (h₀ r).1.2 ((Z).emittedNear T (h₀ r).1.2)).map name)
    (small : pitch<2^w) (wide : 4<2^w) (fits : ∀j,(src j).Fits w out.base)
    (qFit : query.Fits w out.base) (space : out.base+rows<2^w)
    (read : ∀r : Fin rows,∀j,(src j).eval m (r.val:Word w)=(target (shelf (name (h₀ r).1.2) j):Word w))
    (queryRow : ∀r : Fin rows,(query.eval m (r.val:Word w)).val=(name ((blocks B).src (entry r).val).1.2).val) :
    let op:=calculate src query
    let code:=scan w out.base rows op
    let o:=image out.base rows op m
    code.Exec m o (4+rows*(2*op.work+4)) ∧
      (∀r : Fin rows,o (out.base+r.val)=((sourceClass B (h₀ r) (entry r)).val:Word w)) ∧
      (∀x,x<out.base ∨ out.base+rows≤x → o x=m x) ∧
      DescentStaticWordColumn.names code=11+4*op.work ∧ CheapCode code := by
  obtain ⟨exec,lookup,frame,hardware,cheap⟩:=issue shelf src query out m (fun r=>name (h₀ r).1.2)
    (fun r=>name ((blocks B).src (entry r).val).1.2) small wide fits qFit space read queryRow
  refine ⟨exec,fun r=>?_,frame,hardware,cheap⟩
  rw [lookup,observed_class B record name order shelf (h₀ r) (entry r) («fields» r)]

/-- The same shared chip supplies the destination class and the receiver's
own class. Every compared host is one of the four emitted neighbors or self. -/
theorem issue_meta_class {pitch p rows w : ℕ} (record : B.Recorded p) (name : B.next.V↪Fin pitch)
    (order : ∀a b,name a<name b↔ranking a<ranking b) (shelf : Fin pitch→Fin 4→Option (Fin pitch))
    (src : Fin 4→Expr) (query : Expr) (out : Bank) (m : Memory w)
    (focus word_ : Fin rows→Host) (valid : ∀r,word_ r∈DescentResetWindowResidentSources.sources (A) (focus r))
    («fields» : ∀r,present shelf (name (focus r).1.2)=(insert (focus r).1.2 ((Z).emittedNear T (focus r).1.2)).map name)
    (small : pitch<2^w) (wide : 4<2^w) (fits : ∀j,(src j).Fits w out.base)
    (qFit : query.Fits w out.base) (space : out.base+rows<2^w)
    (read : ∀r : Fin rows,∀j,(src j).eval m (r.val:Word w)=(target (shelf (name (focus r).1.2) j):Word w))
    (qr : ∀r : Fin rows,(query.eval m (r.val:Word w)).val=(name (word_ r).1.2).val) :
    let op:=calculate src query
    let text:=scan w out.base rows op
    let o:=image out.base rows op m
    text.Exec m o (4+rows*(2*op.work+4)) ∧
      (∀r : Fin rows,o (out.base+r.val)=(localClass B (focus r) (word_ r):Word w)) ∧
      (∀u,u<out.base ∨ out.base+rows≤u → o u=m u) ∧
      DescentStaticWordColumn.names text=11+4*op.work ∧ CheapCode text := by
  obtain ⟨exec,lookup,frame,hw,cheap⟩:=issue shelf src query out m (fun r=>name (focus r).1.2)
    (fun r=>name (word_ r).1.2) small wide fits qFit space read qr
  refine ⟨exec,fun r=>?_,frame,hw,cheap⟩
  rw [lookup,class_host B _ _ (valid r),rendered_near B record,
    local_class name _ _ shelf _ («fields» r)]
  congr 2
  ext u
  simp only [order]
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
