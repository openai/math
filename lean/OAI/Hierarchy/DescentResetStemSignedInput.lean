import OAI.Hierarchy.DescentResetStemObservedInputs
import OAI.Hierarchy.DescentResetStemChipProjection
import OAI.Hierarchy.DescentResetHostParentDirectory

namespace OAI
/-! # Original signed low-block and its actual owner on the stem ordinal shelf -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Kind" => (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
local notation "Short" => DescentResetCompactParent.Word H r Y L (A).cap slots pcCap

local notation "tape" => (Z).nativeResetEdges T vertex birth


local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fitBlock" => B.frame.enough.trans (Nat.sub_le ..)
local notation "previous" => input.order.trans Fin.valEmbedding
local notation "groupTable" => fun u : Host=>groupDomain digits B.frame.basis fitBlock (B.frame.host.symm (receiverRoot B u).1) (receiverRoot B u).2
local notation "halo" => fun u : Host=>hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1)

open DescentIssuedFallbackPanel DescentResetStemWord
local notation "coarseFit" => (T).commonDepth
local notation "Slot" => Block (S.groupWidth k tail i+k-coarseFit)×Fin (2*(A).cap)
local notation "actor" u => B.frame.host.symm (receiverRoot B u).1
local notation "short" u => (receiverRoot B u).2
local notation "siteNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans Fin.valEmbedding))

open DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "ng" => S.groupCount (i+1)
local notation "X" => 2^k
local notation "J" => stemsCount B
local notation "K" => totalLocal B
local notation "count₀" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
variable {N field b M Wd : ℕ}
open DescentResetFieldAssembler DescentResetStemProjectIndex DescentResetStemGroupPlane
variable (receivers : Fin N→Option B.next.V)

open DescentSharedCableNames.Stage DescentResetStemChipProjection
variable {P₀ srcM : ℕ}
local notation "Q₀" => count₀*(2*(A).cap)
local notation "C₀" => (T).commonDepth
local notation "oldEnd" => fun base => DescentResetStemProject.endAddress base Q₀ P₀ ng X field srcM M
local notation "tailEnd" => fun base => oldEnd base+DescentResetStemKeyReindex.size P₀ N ng M

def signedSlot (j : Fin J) : Fin Q₀:=finProdFinEquiv (stemTag B j).2

def signedOldRaster (field : ℕ) (chips : Fin P₀→Block C₀→Slot→Option (Live (A).degree (A).cap))
    (q₀ : Fin Q₀) (v : Fin P₀) (gx : Fin (ng*X)) : Cell field :=
  (DescentSignedCableCodec.encode (chips v (Fin.cast (stem_project_size B).symm gx)
    (finProdFinEquiv.symm q₀))).val

theorem stem_chip_live (field : ℕ) (chips : Fin P₀→Block C₀→Slot→Option (Live (A).degree (A).cap))
    (actorId : input.V↪Fin P₀) (owner : Fin N→Fin P₀)
    (named : ∀v h₀,receivers v=some h₀ → owner v=actorId (stemOldHost B h₀))
    (signs : ∀vv rack slot,chips (actorId vv) rack slot=
      signedPanel A previous S input.valid siteNames (donor digits B.frame.basis fitBlock vv rack slot.1) slot.2)
    (x : Block k) (j : Fin J) (v : Fin N) (g₀ : Fin ng) (h₀ : B.next.V) (real : receivers v=some h₀) :
    signedOldRaster B field chips (signedSlot B j) (owner v) (finProdFinEquiv (g₀,x))=
    (stemObservedChip B receivers x j v g₀:Cell field) := by
  let u : Host:=((g₀,h₀),x)
  have high:=stem_project_rack B u
  change Fin.cast (stem_project_size B).symm (finProdFinEquiv (g₀,x))=(receiverRoot B u).2 at high
  simp only [signedOldRaster,signedSlot,Equiv.symm_apply_apply,named _ _ real,high,signs,stemObservedChip,real,Option.elim_some]
  rfl

theorem issued_chip (base ptr : ℕ) (src : Fin Q₀→Expr)
    (chips : Fin P₀→Block C₀→Slot→Option (Live (A).degree (A).cap))
    (actorId : input.V↪Fin P₀) (owner : Fin N→Fin P₀) (mem : Memory Wd)
    (hs : 0<srcM) (hm : 0<M) (fits : ∀q,(src q).Fits Wd base)
    (signed : ∀q,Source (src q) (signedOldRaster B field chips q) srcM mem)
    (directory : DescentResetStemKeyReindex.Directory ptr owner mem)
    (parents : ∀v h₀,receivers v=some h₀ → owner v=actorId (stemOldHost B h₀))
    (signs : ∀vv rack slot,chips (actorId vv) rack slot=
      signedPanel A previous S input.valid siteNames (donor digits B.frame.basis fitBlock vv rack slot.1) slot.2)
    (ptrRoom : ptr+DescentDyadicSpan.span N≤base) (room : tailEnd base<2^Wd) :
    let props:=DescentResetStemProjectExpr.program base P₀ ng X field srcM M src Wd
    let phase:=DescentResetStemKeyReindex.phase Wd (oldEnd base) P₀ N ng M
    let result:=phase.image (DescentResetStemProjectExpr.image base P₀ ng X field srcM M src mem)
    let value:=fun (x : Block k) (j : Fin J) (v : Fin N) (g₀ : Fin ng)=>signedOldRaster B field chips (signedSlot B j) (owner v) (finProdFinEquiv (g₀,x))
    (props.seq phase.program).Exec mem result (DescentResetStemProjectExpr.ticks base P₀ ng X field srcM M src+phase.ticks) ∧
    CheapCode (props.seq phase.program) ∧
    (∀x j,(source base ptr P₀ N ng X field srcM M (signedSlot B j) x).Fits Wd (tailEnd base) ∧
      Source (source base ptr P₀ N ng X field srcM M (signedSlot B j) x) (value x j) M result) ∧
    (∀x j v g₀ h₀,receivers v=some h₀→value x j v g₀=(stemObservedChip B receivers x j v g₀:Cell field)) ∧
    ∀addr,addr<base ∨ tailEnd base≤addr → result addr=mem addr := by
  intro props phase result value
  have execution := DescentResetStemChipProjection.project base ptr src (signedOldRaster B field chips) owner mem hs hm
    (Nat.two_pow_pos _) fits signed directory ptrRoom room
  exact ⟨@execution.1, @execution.2.1, fun x j => execution.2.2.1 (signedSlot B j) x,
    stem_chip_live B receivers field chips actorId owner parents signs, execution.2.2.2⟩

/-- Data in empty host rows may retain their previously measured physical bits.
The live digit of the actual six-word query alone controls the empty tag. -/
theorem observed_on_receivers (x : Block k) (j : Fin J) (trueRows got : Fin N→Fin ng→Fin 6→Cell field)
    (held : StemInputs B receivers x (stemTag B j).1 (stemTag B j).2 trueRows)
    (live : ∀v g₀ h₀,receivers v=some h₀ → got v g₀=trueRows v g₀)
    (blank : ∀v g₀,receivers v=none→(got v g₀ 4).val=0) :
    StemInputs B receivers x (stemTag B j).1 (stemTag B j).2 got :=
  ⟨blank,fun v g h row=>(congrArg (fun z : Fin 6→Cell field=>(z 0).val) (live v g h row)).trans (held.chip v g h row),
   fun v g h row=>(congrArg (fun z : Fin 6→Cell field=>(z 1).val) (live v g h row)).trans (held.group v g h row),
   fun v g h row=>(congrArg (fun z : Fin 6→Cell field=>(z 2).val) (live v g h row)).trans (held.self v g h row),
   fun v g h row=>(congrArg (fun z : Fin 6→Cell field=>(z 3).val) (live v g h row)).trans (held.fine v g h row),
   fun v g h row=>by rw [live v g h row];exact held.active v g h row,
   fun v g h row=>by rw [live v g h row];exact held.zero v g h row⟩
end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
