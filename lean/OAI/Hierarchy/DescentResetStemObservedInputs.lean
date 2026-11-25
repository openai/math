import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetStemProjectIndex

namespace OAI
/-! # Observations supplying the six inputs to every native stem word -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "priorWorld" => W.granular B.count (z*G.b) B.fit
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
local notation "Kind" => (Bool×(priorWorld).graph.Edge) ⊕ ((Z).Fallback ⊕ ((R).Contact ⊕ PrivateOccurrence B))
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
local notation "actor" u:arg => B.frame.host.symm (receiverRoot B u).1
local notation "short" u:arg => (receiverRoot B u).2
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

def stemGroupDigit (x : Block k) (lo : Block (S.groupWidth k tail i+k-coarseFit)) (g₀ : Fin ng) :=
  let addr:=oldCell B x lo g₀
  compress (groupDomain digits B.frame.basis fitBlock () (high fitBlock addr))
    (digits ((rearrange B.frame.basis).symm addr)).1.val

def stemFineDigit (x : Block k) (lo : Block (S.groupWidth k tail i+k-coarseFit)) (g₀ : Fin ng) :=
  ((rearrange B.frame.basis).symm (oldCell B x lo g₀)).val%2^k

def stemZeroDigit (x : Block k) (g₀ : Fin ng) := (decide (g₀.val*2^k+x.val=0)).toNat

def stemOldHost (h₀ : B.next.V) : input.V := B.frame.host.symm
  (DescentDenseHostOrder.position (Z).graph h₀.val)

def stemSelfDigit (v : Fin N) :=
  (receivers v).elim 0 (fun h₀=>
    let v₀:=stemOldHost B h₀
    hostCode (compress (hostDomain A input.vertex v₀) (input.vertex v₀).val)
      (decide (v₀∉(A).near v₀)))

def stemLiveDigit (x : Block k) (j : Fin J) (v : Fin N) (g₀ : Fin ng) :=
  (actualMeta B receivers x (stemShelf B j) v g₀).live.toNat

def stemObservedChip (x : Block k) (j : Fin J) (v : Fin N) (g₀ : Fin ng) :=
  let slot:=(stemTag B j).2
  (receivers v).elim 0 (fun h₀=>
    let u : Host:=((g₀,h₀),x)
    (DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid siteNames
      (donor digits B.frame.basis fitBlock (actor u) (short u) slot.1) slot.2)).val)

def stemObservedInputs (field : ℕ) (x : Block k) (j : Fin J) (v : Fin N) (g₀ : Fin ng) :
    Fin 6→Cell field :=
  let lo:=(stemTag B j).2.1
  fun idx=>((![(stemObservedChip B receivers x j v g₀:ℕ),(stemGroupDigit B x lo g₀:ℕ),
    (stemSelfDigit B receivers v:ℕ),(stemFineDigit B x lo g₀:ℕ),
    (stemLiveDigit B receivers x j v g₀:ℕ),(stemZeroDigit (S:=S) (i:=i) x g₀:ℕ)] : Fin 6→ℕ) idx:Cell field)

theorem stem_rank_digit (u : Host) (lo : Block (S.groupWidth k tail i+k-coarseFit)) :
    stemGroupDigit B u.2 lo u.1.1=compress (groupTable u)
      (digits ((rearrange B.frame.basis).symm (oldCell B u.2 lo u.1.1))).1.val := by
  have highCell : high fitBlock (oldCell B u.2 lo u.1.1)=short u := by
    apply Fin.ext
    change (((short u).val*2^(_-coarseFit)+lo.val)/2^(_-coarseFit))=(short u).val
    rw [Nat.mul_comm (short u).val, Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt lo.isLt,Nat.add_zero]
  exact congrArg (fun hi=>compress (groupDomain digits B.frame.basis fitBlock () hi)
    (digits ((rearrange B.frame.basis).symm (oldCell B u.2 lo u.1.1))).1.val) highCell

theorem stem_zero_digit (u : Host) :
    decide (stemZeroDigit (S:=S) (i:=i) u.2 u.1.1≠0)=zeroCoarse B u := by
  have hi:=congrArg Fin.val (stem_project_rack B u)
  rw [index_val] at hi
  simp [stemZeroDigit,zeroCoarse,hi]

theorem stem_observed (field : ℕ) (scale : DescentSignedCableCodec.width (A).degree (A).cap≤field)
    (groupsFit : count₀<2^field) (hostsFit : 2*((A).degree+1)+1<2^field) (fineFit : k≤field)
    (x : Block k) (j : Fin J) :
    StemInputs B receivers x (stemTag B j).1 (stemTag B j).2 (stemObservedInputs B receivers field x j) := by
  let s:=(stemTag B j).1
  let slot:=(stemTag B j).2
  have bit : 1<2^field:=by omega
  have selfBound (u : Host) : oldSelfCode B u<2^field := by
    have rank:compress (halo u) (input.vertex (actor u)).val≤(A).degree+1:=
      (compress_bound ..).trans (host_bound A input.vertex (actor u))
    have last:=Bool.toNat_le (decide (actor u∉(A).near (actor u)))
    exact (Nat.add_le_add (Nat.mul_le_mul_left 2 rank) last).trans_lt hostsFit
  constructor
  · intro v g₀ none_
    simp [stemObservedInputs,stemLiveDigit,actualMeta,none_,Meta.blank]
  · intro v g₀ h₀ hv
    let u : Host:=((g₀,h₀),x)
    have bound: (DescentSignedCableCodec.encode (Stage.signedPanel A previous S input.valid siteNames
      (donor digits B.frame.basis fitBlock (actor u) (short u) slot.1) slot.2)).val<2^field:=
      (Fin.isLt _).trans_le (Nat.pow_le_pow_right (by decide) scale)
    simp [stemObservedInputs,stemObservedChip,hv,slot,u,Fin.val_cast_of_lt bound]
  · intro v g₀ h₀ hv
    let u : Host:=((g₀,h₀),x)
    have eqn:=stem_rank_digit B u slot.1
    have bound:stemGroupDigit B x slot.1 g₀<2^field:=by
      rw [eqn];exact ((compress_bound ..).trans (group_bound _ _ _ _ _)).trans_lt groupsFit
    simpa [stemObservedInputs,slot,Fin.val_cast_of_lt bound] using
      (Fin.val_cast_of_lt (n:=2^field) bound).trans eqn
  · intro v g₀ h₀ hv
    let u : Host:=((g₀,h₀),x)
    have eqn : stemSelfDigit B receivers v=oldSelfCode B u:=by simp only [stemSelfDigit,hv,Option.elim_some]; rfl
    exact (Fin.val_cast_of_lt (n:=2^field) (eqn.le.trans_lt (selfBound u))).trans eqn
  · intro v g₀ h₀ hv
    have less:stemFineDigit B x slot.1 g₀<2^field:=
      (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) fineFit)
    simpa [stemObservedInputs,slot,stemFineDigit] using Fin.val_cast_of_lt (n:=2^field) less
  · intro v g₀ h₀ hv
    let u : Host:=((g₀,h₀),x)
    have active : (actualMeta B receivers x (stemShelf B j) v g₀).live=
        (localOrigin B u (stemShelf B j)).isSome:=by
      simp only [actualMeta,hv,Option.elim_some]
      change («meta» B u (localOrigin B u (stemShelf B j))).live=_
      cases hit:localOrigin B u (stemShelf B j) <;> rfl
    have liveBound : stemLiveDigit B receivers x j v g₀<2^field:=(Bool.toNat_le _).trans_lt bit
    change (((stemLiveDigit B receivers x j v g₀:ℕ):Cell field).val≠0 ↔ _)
    rw [Fin.val_cast_of_lt liveBound,stem_shelf_number B j]
    change ((actualMeta B receivers x (stemShelf B j) v g₀).live.toNat≠0 ↔ _)
    rw [active]
    cases (localOrigin B u (stemShelf B j)).isSome <;> decide
  · intro v g₀ h₀ hv
    have bound:stemZeroDigit (S:=S) (i:=i) x g₀<2^field:=(Bool.toNat_le _).trans_lt bit
    simpa [stemObservedInputs,Fin.val_cast_of_lt bound] using stem_zero_digit B ((g₀,h₀),x)

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
