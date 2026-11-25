import OAI.Hierarchy.DescentReachedGoodTapRows
import OAI.Hierarchy.DescentBankSavedPacket

namespace OAI
/-! # The recorded matrix page at the installed good bank -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentRotorWindowArchive
noncomputable section

/-- Reindexing the original tape preserves the value of every numerical
matrix entry, including unused input rows. -/
theorem tapDataCast_matrix (cfg : DescentResetPublicOperandBook.Config)
    (degree cap c k field n : ℕ) {a b : ℕ} (eqn : a=b)
    (x : (matrixConfig cfg degree cap (2^(a-c)) k field).Data n)
    (j : DescentRotorWindowArchive.Input degree (2^(b-c)) cap) :
    let size:=congrArg (fun z=>count degree (2^(z-c)) cap) eqn
    (matrixConfig cfg degree cap (2^(b-c)) k field).oldData
      (tapDataCast cfg degree cap c k field n eqn x) j=
    (matrixConfig cfg degree cap (2^(a-c)) k field).oldData x (ix.symm ((ix j).cast size.symm)) :=by
  subst b
  exact congrArg ((matrixConfig cfg degree cap (2^(a-c)) k field).oldData x)
    (DescentRotorWindowArchive.ix.symm_apply_apply j).symm

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentResetHostSize DescentSIMDLookup DescentSharedBookScan
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentPaidResidentCount.Reset DescentOldContactSender DescentStageEdgeReceipt DescentRosterOrder
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentResetLocalRoster DescentPacking
open DescentResetStemCompactOrder DescentChosenRouter DescentPackedTicketChronology DescentPackedFlowPair
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d p : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail field query lanes nodes args grain : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rankKey" => B.frame.host.symm.toEmbedding.trans host
local notation "next_" => PackedFlow.Padded.roster (D:=(A).degree) (A) (Recorded.oldName input) input.valid.host
local notation "paid_" => Recorded.paddedValue (b:=field) c r next_ (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "unit" => (Z).unit/p
local notation "cfg" => publicOperandConfig B field query lanes unit unit nodes args grain
local notation "rank_" snap:arg => ranks (a:=r) («Y»:=2^(Z).n) (D:=(A).degree) (snap).chart (2^dep) (dep+2) (snap).memory
local notation "dim" => S.groupWidth k tail i+k
local notation "priorData" x:arg => GroupStage.tapDataCast cfg (A).degree (A).cap c k field (Z).n B.keyWidth x
local notation "cross" => congrArg (fun size=>DescentRotorWindowArchive.count (A).degree size (A).cap)
      (congrArg (fun z=>2^(z-c)) B.keyWidth)
local notation "bankSite" b₀:arg => DescentSharedCableNames.Stage.home B.next.placement (B.reblock.destination (((Z).resetNames T).symm (.inr b₀)))
variable (snap : PaddedSnapshot B input.valid.host field) (positive : 0<S.hostSize i)
    (side : Bool) (root : B.reset.placement.Good) (cell : (DescentCommonPalette.rotor B.reset.graph).Site)
local notation "venue" => (⟨(side,.inl root),DescentCommonPalette.rotorSiteEquiv (Z).graph d
  (DescentChosenRouter.selectedRotorLayers (Z).placement (Z).graph (Z).positive (Z).pay (Z).circuit side root)
  C (Z).width (Z).unit cell⟩ : (Z).bank.Site)
local notation "who" => (Z).packetOwner T rankKey positive (((denseOrder B) (bankSite venue).1.2).castLE B.next.valid.host)
local notation "position" => (bankSite venue).2
local notation "group_" => (bankSite venue).1.1

/-- The recorded-matrix clause of the issued public row at this gate is the
gathered physical matrix in the predecessor's actual dimension. -/
theorem good_matrix_gathered (groupAt : S.groupCount (i+1)*2^k=2^c) (x : (cfg).Data (Z).n)
    (received : ∀(j : DescentRotorWindowArchive.Input (A).degree (2^r) (A).cap) (old : input.V),
      who=host old →
      ((cfg).oldData x j).val=
        (recordedBoard B snap old ((finProdFinEquiv (group_,position)).cast groupAt)
          (ix.symm ((ix j).cast cross))).val) :
    ∀j,(GroupStage.matrixConfig cfg (A).degree (A).cap (2^(dim-c)) k field).oldData (priorData x) j=
      RootSources.paddedRow snap.stencil next_ snap.marks (fun v j=>((rank_ snap) v j).val)
        (fun _=>Receiver.matrixBefore B.frame.basis small) paid_
        (host (B.frame.host.symm root.val.1)) ((Z).rootBlock T (.inl root)) (ix j) :=by
  intro j
  let old:=B.frame.host.symm root.val.1
  obtain ⟨whereHost,whereGroup⟩:=bank_packet_address B input.valid.host B.next.valid.host positive venue rfl rfl groupAt
  have home : who=host old:=whereHost
  let row:=ix.symm ((ix j).cast (cross).symm)
  have read:=received row old home
  change (finProdFinEquiv (group_,position)).cast groupAt=(Z).rootBlock T (.inl root) at whereGroup
  rw [whereGroup] at read
  have indexBack : ix.symm ((ix row).cast cross) = j := by
    apply ix.injective
    rw [Equiv.apply_symm_apply]
    unfold row
    rw [Equiv.apply_symm_apply]
    exact Fin.ext rfl
  rw [indexBack] at read
  have previous:=GroupStage.tapDataCast_matrix cfg (A).degree (A).cap c k field (Z).n B.keyWidth x j
  have same : (GroupStage.matrixConfig cfg (A).degree (A).cap (2^(dim-c)) k field).oldData (priorData x) j=
      recordedBoard B snap old ((Z).rootBlock T (.inl root)) j:=previous.trans (Fin.ext read)
  exact same.trans (recorded_padded_board B snap snap.stencil snap.marks snap.stencilRead snap.markRead old
    ((Z).rootBlock T (.inl root)) j).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
