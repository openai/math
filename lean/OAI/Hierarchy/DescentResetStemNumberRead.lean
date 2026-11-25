import OAI.Hierarchy.DescentResetStemSignedInput
import OAI.Hierarchy.DescentResetStemFlagInputs

namespace OAI
/-! # Publishing all stem numbers from original signed and reset metadata words -/
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

open DescentResetStemFlagInputs
theorem stem_public_zero (x : Block k) (g₀ : Fin ng) :
    (stemZeroDigit (S:=S) (i:=i) x g₀:Cell field)=firstDigit field x.val g₀ := by
  simp only [stemZeroDigit,firstDigit,Nat.add_eq_zero_iff,Nat.mul_eq_zero,(Nat.two_pow_pos k).ne',or_false]

/-- The inputs are the printed scalar fields. Only the stored chip and the old
host's cached descriptor may take an arbitrary value on an unoccupied host. -/
theorem original_numbers (book original : ℕ) (src : Fin X→Fin J→Fin 6→Expr)
    (signVal : Fin X→Fin J→Fin N→Fin ng→Cell field) (hostVal : Fin N→Cell field)
    (m₀ : Memory Wd) (fits : ∀x j t,(src x j t).Fits Wd book)
    (chip : ∀x j,Source (src x j 0) (signVal x j) M m₀)
    (chipAt : ∀x j v g₀ h₀,receivers v=some h₀→signVal x j v g₀=(stemObservedChip B receivers x j v g₀:Cell field))
    (rank : ∀x j,Source (src x j 1) (fun (_:Fin N) g₀=>(stemGroupDigit B x (stemTag B j).2.1 g₀:Cell field)) M m₀)
    (host : ∀x j,Source (src x j 2) (fun v (_:Fin ng)=>hostVal v) M m₀)
    (hostAt : ∀v h₀,receivers v=some h₀→hostVal v=(stemSelfDigit B receivers v:Cell field))
    (low : ∀x j,Source (src x j 3) (fun (_:Fin N) g₀=>(stemFineDigit B x (stemTag B j).2.1 g₀:Cell field)) M m₀)
    (live : ∀x j,Source (src x j 4) (fun v g₀=>((actualMeta B receivers x (stemShelf B j) v g₀).live.toNat:Cell field)) M m₀)
    (zero : ∀x j,Source (src x j 5) (fun (_ : Fin N) (g₀ : Fin ng)=>firstDigit field x.val g₀) M m₀)
    (signedFits : DescentSignedCableCodec.width (A).degree (A).cap≤field) (groupsFit : count₀<2^field)
    (hostsFit : 2*((A).degree+1)+1<2^field) (fineFit : k≤field)
    (header : book+DescentOperandPairBook.words 6 field M≤original)
    (space : DescentResetOriginalSlots.finish original (N*chunks ng M) X K<2^Wd) :
    let phase:=originalStemPhase B field b M N Wd book original src fits header space
    phase.Runs m₀ ∧
    (∀x j,∀p : Row N ng M,phase.image m₀
      (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val (stemShelf B j).val+(row N ng M p).val)=
      ((data (fun v g=>(actualParentNumber B receivers x (stemShelf B j) v g:Cell b)) p).val:Word Wd)) ∧
    (∀x : Fin X,∀j : Fin K, J≤j.val→∀p : Fin (N*chunks ng M),
      phase.image m₀ (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val j.val+p.val)=
        m₀ (DescentResetOriginalSlots.offset original (N*chunks ng M) K x.val j.val+p.val)) ∧
    ∀addr,addr<book ∨ DescentResetOriginalSlots.finish original (N*chunks ng M) X K≤addr→phase.image m₀ addr=m₀ addr := by
  intro phase
  let vals (x : Fin X) (j : Fin J) (v : Fin N) (g₀ : Fin ng) : Fin 6→Cell field :=
    ![signVal x j v g₀,(stemGroupDigit B x (stemTag B j).2.1 g₀:Cell field),hostVal v,
      (stemFineDigit B x (stemTag B j).2.1 g₀:Cell field),
      ((actualMeta B receivers x (stemShelf B j) v g₀).live.toNat:Cell field),firstDigit field x.val g₀]
  have sources (x : Fin X) (j : Fin J) (i : Fin 6) : Source (src x j i) (fun v g₀=>vals x j v g₀ i) M m₀:=by
    fin_cases i
    · exact chip x j
    · exact rank x j
    · exact host x j
    · exact low x j
    · exact live x j
    · exact zero x j
  have seen (x : Fin X) (j : Fin J) : StemInputs B receivers x (stemTag B j).1 (stemTag B j).2 (vals x j) := by
    apply observed_on_receivers B receivers x j _ _
      (stem_observed B receivers field signedFits groupsFit hostsFit fineFit x j)
    · intro v g₀ h₀ hv
      funext fin
      fin_cases fin
      · exact chipAt x j v g₀ h₀ hv
      · rfl
      · exact hostAt v h₀ hv
      · rfl
      · rfl
      · exact (stem_public_zero (field:=field) x g₀).symm
    · intro v g₀ hv
      simp [vals,actualMeta,hv,DescentResetFieldAssembler.Meta.blank]
  obtain ⟨run,_,read,keep,other⟩:=original_stems (b:=b) B receivers book original src vals m₀ fits sources seen
    (by omega) header space
  exact ⟨run,read,keep,other⟩

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
