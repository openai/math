import OAI.Hierarchy.DescentMeasuredSenderDesk

namespace OAI
/-! # The prepared chronological sender register at the reset calendar's physical leaf count -/
namespace Hierarchy.DescentOldContactSender
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSIMDLookup DescentSharedBookScan DescentContactSenderDate
noncomputable section
variable {D L L' cap n r field H G : ℕ}

def matrixCast (eqn : L'=L) (m : Fin H→Fin G→Fin (DescentRotorWindowArchive.count D L cap)→Cell field)
    (v : Fin H) (hi : Fin G) (j : Fin (DescentRotorWindowArchive.count D L' cap)) : Cell field:=
  m v hi (j.cast (congrArg (fun t=>DescentRotorWindowArchive.count D t cap) eqn))

theorem matrixCast_words (eqn : L'=L) (m : Fin H→Fin G→Fin (DescentRotorWindowArchive.count D L cap)→Cell field)
    (rank : Fin H→Fin (width r (2^n) D)→Cell field) :
    Prior.castValues eqn (RootSources.senderWords (matrixCast eqn m) rank)=
      RootSources.senderWords (n:=n) m rank:=by subst L';rfl

theorem matrixCast_padded (eqn : L'=L) (own : Fin H→Fin G→Fin L→ℕ)
    (peers : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin G→Fin L→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ) (old : Fin H→Fin G→Fin L→Fin L→Bool)
    (paid : Fin H→Fin D→Fin D→Fin 6→Cell field) :
    matrixCast eqn (RootSources.paddedRow own peers marks rank old paid)=
      RootSources.paddedRow (fun u hi lo=>own u hi (lo.cast eqn)) peers
        (fun u hi lo=>marks u hi (lo.cast eqn)) rank
        (fun u hi a b=>old u hi (a.cast eqn) (b.cast eqn)) paid:=by subst L';rfl

end
end Hierarchy.DescentOldContactSender

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetHostSize DescentSIMDLookup DescentSharedBookScan DescentResetLocalRoster
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentContactSenderDate
open DescentPaidResidentCount.Reset DescentOldContactSender DescentPacking
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (M field : ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "Y" => 2^(Z).n
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "slots" => congrArg (fun t=>2^(t-c)) B.keyWidth
variable {bw N K R hm l tiny : ℕ}
    (rc : Receiver (A).degree (A).cap N (Z).n r c H (S.groupCount i) K R M hm l tiny field dep bw)
    (book : RootBook (Z).n r (A).degree (2^r) (A).cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B input.valid.host rc book mem) (x : OriginalArrays B input.valid.host field)
local notation "view" => root_snapshot B input.valid.host rc book space mem hdr x

/-- The order, signed wires and six directed fields are read in the native matrix
at the reset key width. The fallback ranks come from its original prepared memory. -/
def calendar_sender_matrix := matrixCast slots (senderMatrix B view)

/-- A row equality on the whole padded rectangle, including its vacant old hosts.
At the public leaf count the acquired inverse-GL order and quota fields are unchanged. -/
theorem calendar_sender_matrix_eq :
    calendar_sender_matrix B M field rc book space mem hdr x =
      RootSources.paddedRow (fun u hi lo=>x.stencil u hi (lo.cast slots)) x.peers
        (fun u hi lo=>x.marks u hi (lo.cast slots))
        (fun u j=>(ranks (a:=r) («Y»:=Y) (D:=(A).degree) (book.common rc.projectionEnd H)
          (2^dep) (dep+2) (rc.preparedMid book space mem) u j).val)
        (fun _ hi a b=>GroupStage.previousDigit B.frame.basis (B.frame.enough.trans (Nat.sub_le ..)) hi
          (a.cast slots) (b.cast slots))
        (Recorded.paddedValue (b:=field) c r
          (PackedFlow.Padded.roster (D:=(A).degree) (A) (Recorded.oldName input) input.valid.host)
          (Recorded.oldDepth B) (Recorded.oldWidth B)):=by
  apply matrixCast_padded

theorem calendar_measured_sender (elapsed : 0< i) (sorted : SourceSorted W input.order)
    (baseRoom : max (max r Y) (2^r)<2^field) (dimRoom : (Z).n<field)
    (socketRoom : rootSlots r Y*(Y+2^dep)<2^field) (heightRoom : dep<2^field)
    (portRoom : (A).degree≤2^field) :
    ∃setup : (senderDesk B field).Inputs,∀v hi,
      decode (calendar_sender_values B M field rc book space mem
        (calendar_sender_matrix B M field rc book space mem hdr x) (host v) hi)=
        (senderDesk B field).sample setup v hi:=by
  obtain ⟨setup,measured⟩:=measured_sender_desk B view elapsed sorted baseRoom dimRoom socketRoom heightRoom portRoom
  refine ⟨setup,fun v hi=>?_⟩
  change decode (Prior.castValues slots (RootSources.senderWords
    (matrixCast slots (senderMatrix B view)) (senderRank B view)) (host v) hi)=_
  rw [matrixCast_words]
  exact measured v hi

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
