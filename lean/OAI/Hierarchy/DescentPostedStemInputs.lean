import OAI.Hierarchy.DescentDateStemRegisterRead
import OAI.Hierarchy.DescentCalendarOriginalStems
import OAI.Hierarchy.DescentPhysicalPublicOriginalFrame
import OAI.Hierarchy.DescentOriginalStemWordIssue

namespace OAI
/-! # The six acquired stem inputs in the memory read by the numbered stem pass -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentDatedAddressBook
open DescentResetFieldAssembler DescentStemNumberOperands DescentResetStemFlagInputs
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 750000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {a : PhysicalReset} {start Wd : ℕ} (u : a.DateInputs start Wd)
local notation "v" => a.successor
local notation "fr" => (v).front
local notation "s" => (v).sheets
local notation "b₀" => a.rebased start
local notation "cut₀" => (v).actorEnd b₀
local notation "base" => (s).metaEnd (((v).remap b₀).endAddress)
local notation "N" => (s).hosts
local notation "M" => (s).lanes
local notation "field" => (s).stemBits
local notation "sg" => (s).stemSignedBits
local notation "bw" => (s).metaBits
local notation "ng" => S.groupCount (i+1)
local notation "J" => stemsCount B
local notation "receivers" => originalTrunkRack (H:=N) B
local notation "bias" => (v).peerAux b₀ 3
local notation "stemPage" => (fr).stemOperand cut₀
local notation "P₀" => numberPlan B N M field sg bw bw


local notation "area" => ((v).remap b₀).endAddress
local notation "top" => (s).coordinateEnd area
local notation "mid" m => u.masked.image (u.privateResult m)
local notation "post" m => (u.numbered.publicSide area).dst (u.numbered.prefixOutput area (mid m))
local notation "trunk" m => ((fr).trunkScene cut₀ ((v).issuedScene b₀ u.earlier) u.sceneFits).image m

theorem posted_stem_inputs (ok : u.Ready) (m : Memory Wd)
    (schedule : (s).stemSources=P₀)
    (xRoom : 2^k≤(fr).blocks) (jRoom : J≤(fr).signedQueries) (cap : a.c/2=input.placement.cap)
    (chosen : (mid m) u.originalBasis.base=((DescentExterior.matrixCode B.frame.basis).val:Word Wd))
    (saved : u.originalBasis.Fits Wd base) (space : top<2^Wd)
    (signedWidth : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤ sg)
    (signed : ∃chip : Block k→Fin J→Fin N→Fin ng→Cell sg,
      (∀x j,(u.previousSigned x.val j.val).Fits Wd ((v).trunkEnd b₀) ∧
        Source (u.previousSigned x.val j.val) (chip x j) M (trunk m)) ∧
      ∀x j r h v',receivers r=some v'→chip x j r h=(stemObservedChip B (receivers) x j r h:Cell sg))
    (aux : ∃self : Fin N→Cell bw,
      Source (bias) (fun r (_:Fin ng)=>self r) M (mid m) ∧
      ∀r v',receivers r=some v'→(self r).val=stemSelfDigit B (receivers) r)
    (bf : (bias).Fits Wd base)
    (head : ∀(x : Block k) (j : Fin J),(stemPage x.val j.val).Fits Wd ((v).trunkEnd b₀) ∧
      Source (stemPage x.val j.val) (fun r h=>DescentResetFieldAssembler.raw bw (actualMeta B (receivers) x (stemShelf B j) r h)) M (trunk m))
    (metaPos : 0<bw)
    (signedFits : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤field)
    (groupsFit : 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)<2^field)
    (hostsFit : 2*(input.placement.degree+1)+1<2^field) (fineFit : k≤field) :
    ∃values : Block k→Fin J→Fin N→Fin ng→Fin 6→Cell field,
      (∀x j t,Source (u.stemRegisters x.val j.val t) (fun h g=>values x j h g t) M (post m)) ∧
      ∀x j,StemInputs B (receivers) x (stemTag B j).1 (stemTag B j).2 (values x j) :=by
  obtain ⟨chip,old,chipAt⟩:=signed
  obtain ⟨self,biasRead,selfAt⟩:=aux
  have below : (v).trunkEnd b₀≤base:=by
    have limits:=(v).receipt_order b₀
    rw [←u.masks_end]
    exact ok.ordered.2.2.2.1.trans (limits.1.trans (limits.2.trans (u.masked.ordered.1.trans u.masked.ordered.2)))
  have coord : base≤top:=by
    change _≤(s).stemSources.endAddress base
    rw [(s).stemSources.extent];exact Nat.le_add_right ..
  have low (z : ℕ) (hz : z<(v).trunkEnd b₀) : (mid m) z=(trunk m) z:=by
    have frame:=((s).stemSources.any base (mid m) space).2.2 z (.inl (hz.trans_le below))
    exact frame.symm.trans ((u.public_original_frame ok m z (hz.trans_le (below.trans coord))).symm.trans (u.public_original_scene ok m z hz))
  have keep {width : ℕ} (e : Expr) (val : Fin N→Fin ng→Cell width)
      (fit : e.Fits Wd ((v).trunkEnd b₀)) (earlier : Source e val M (trunk m)) :
      Source e val M (mid m):=fun t=>(eval_below e _ _ _ fit low).trans (earlier t)
  obtain ⟨fits,reg₀,reg₁,reg₂,reg₃,reg₄,reg₅,agree,agreeSelf⟩:=
    real_stem_inputs B u (mid m) schedule xRoom jRoom cap chosen saved space chip
      (fun x j=>keep _ _ (old x j).1 (old x j).2)
      (fun x j r h v' live=>by rw [chipAt x j r h v' live,Fin.val_cast_of_lt (observed_chip_bound (a:=a) B x j r h signedWidth)])
      (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ below (old x j).1)
      self biasRead selfAt bf (fun x j=>keep _ _ (head x j).1 (head x j).2)
      (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ below (head x j).1) metaPos
  let vals (x : Block k) (j : Fin J) (r : Fin N) (h : Fin ng) : Fin 6→Cell field:=
    ![((chip x j r h).val:ℕ),(stemGroupDigit B x (stemTag B j).2.1 h:ℕ),(self r).val,
      (stemFineDigit B x (stemTag B j).2.1 h:ℕ),(actualMeta B (receivers) x (stemShelf B j) r h).live.toNat,
      (DescentResetStemFlagInputs.firstDigit field x.val h)]
  refine ⟨vals,?_,?_⟩
  · intro x j t q
    have past : Source (u.stemRegisters x.val j.val t) (fun r h=>vals x j r h t) M (u.coordinateResult m):=by
      fin_cases t <;> first | exact reg₀ x j | exact reg₁ x j | exact reg₂ x j | exact reg₃ x j | exact reg₄ x j | exact reg₅ x j
    exact (eval_below _ _ _ _ (fits x j t) (u.public_original_frame ok m)).trans (past q)
  · intro x j
    apply observed_on_receivers B (receivers) x j _ _
      (stem_observed B (receivers) field signedFits groupsFit hostsFit fineFit x j)
    · intro r h v' seen
      funext t;fin_cases t
      · exact agree x j r h v' seen
      · rfl
      · exact agreeSelf r v' seen
      · rfl
      · rfl
      · exact (stem_public_zero («field»:=field) x h).symm
    · intro h g₀ ghost
      simp [vals,actualMeta,ghost,Meta.blank]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
