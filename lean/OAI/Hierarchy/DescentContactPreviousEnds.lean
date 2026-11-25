import OAI.Hierarchy.DescentContactReceiver
import OAI.Hierarchy.DescentIssuedReset

namespace OAI
/-! # Every joined contact, including an empty reservation, has the endpoints of a previous grain -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentChosenRouter DescentResetAttachments DescentColonies
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] {d k g : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
    {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
    (frame : Z.SourceFrame T pos ix hub g)
local notation "R" => Z.placement

theorem SourceFrame.contact_old_edge {M : ℕ} {key : A.graph.Edge↪Fin M} (tickets : (R).OrderedTickets key)
    (c : (R).Contact) : ∃i : A.graph.Edge,∀s,rootVertex Z T ((R).owner s c)=frame.host (pos (ends A.graph s i)) := by
  rcases c with ⟨a,j⟩|⟨z,seen⟩
  · obtain ⟨p,atPair⟩:=tickets.pair_observed a
    refine ⟨p.val,fun s=>?_⟩
    change ((R).ends s a).val.1=_
    rw [←atPair,(R).owned p s]
    exact frame.actor s p.val
  · obtain ⟨p,_,atPair⟩:=Finset.mem_image.mp seen
    refine ⟨p.val,fun s=>?_⟩
    cases s
    · have actual:=congrArg Prod.fst atPair
      change (R).fall false ((R).old false p.val)=z.1 at actual
      change (T.code z.1).1=_
      rw [←actual,←T.attach,frame.homeHost]
    · have actual:=congrArg Prod.snd atPair
      change (R).fall true ((R).old true p.val)=z.2 at actual
      change (T.code z.2).1=_
      rw [←actual,←T.attach,frame.homeHost]

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentResetAttachments
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n



local notation "A" => input.placement
local notation "oldVertex" => fun s (c : (placement).Contact)=>B.frame.host.symm ((Z).rootVertex T ((placement).owner s c))

theorem contact_previous_ends (c : (placement).Contact) :
    ∃e : W.graph.Edge,0<B.count e ∧ ∀s,oldVertex s c=((A).pos (ends W.graph s e)).2 := by
  obtain ⟨i,observed⟩:=B.frame.contact_old_edge B.tickets c
  refine ⟨i.1,Nat.zero_lt_of_lt i.2.isLt,?_⟩
  intro s
  have same := congrArg B.frame.host.symm (observed s)
  rw [B.frame.host.symm_apply_apply] at same
  cases s <;> exact same

theorem contact_previous_near (c : (placement).Contact) (s : Bool) :
    oldVertex (!s) c∈(A).mutual (oldVertex s c) := by
  obtain ⟨e,_,endpoint⟩:=contact_previous_ends B c
  obtain ⟨l,nearL,setL⟩:=Finset.mem_map.mp ((A).peers e).1
  obtain ⟨rightEnd,nearR,setR⟩:=Finset.mem_map.mp ((A).peers e).2
  have fore : ((A).pos (W.graph.dst e)).2∈(A).near (((A).pos (W.graph.src e)).2):=
    congrArg Prod.snd setL ▸ nearL
  have back : ((A).pos (W.graph.src e)).2∈(A).near (((A).pos (W.graph.dst e)).2):=
    congrArg Prod.snd setR ▸ nearR
  simp only [endpoint]
  cases s <;> exact Finset.mem_filter.mpr (by first | exact ⟨fore,back⟩ | exact ⟨back,fore⟩)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
