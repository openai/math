import OAI.Hierarchy.DescentResetPeerIssued

namespace OAI
/-! # Calendar-sized axes for the four genuine raw reset probes -/
namespace Hierarchy.DescentResetPeerUnionRAM.Axes
noncomputable section
variable {s c p : ℕ}

abbrev Index (s c p : ℕ) := Fin s ⊕ (Fin 1 ⊕ ((Fin c×Fin s) ⊕ Fin p))
def rows (s c p : ℕ) := s+(1+(c*s+p))
def order (s c p : ℕ) : Index s c p ≃ Fin (rows s c p) :=
  let last:=(Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin p))).trans finSumFinEquiv
  let tail:=(Equiv.sumCongr (Equiv.refl (Fin 1)) last).trans finSumFinEquiv
  (Equiv.sumCongr (Equiv.refl (Fin s)) tail).trans finSumFinEquiv

structure Fields (s c p : ℕ) (α : Type*) where
  stem : Fin s→α
  trunk : α
  contact : Fin c→Fin s→α
  privateEdge : Fin p→α

def Fields.atIndex {α : Type*} (f : Fields s c p α) : Index s c p→α
  | .inl j=>f.stem j
  | .inr (.inl _)=>f.trunk
  | .inr (.inr (.inl v))=>f.contact v.1 v.2
  | .inr (.inr (.inr j))=>f.privateEdge j

def Fields.all {α : Type*} (f : Fields s c p α) (j : Fin (rows s c p)) : α :=
  f.atIndex ((order s c p).symm j)

theorem Fields.all_at {α : Type*} (f : Fields s c p α) (j : Index s c p) :
    f.all (order s c p j)=f.atIndex j := congrArg f.atIndex ((order s c p).symm_apply_apply j)

def kind (s c p : ℕ) : Fin (rows s c p)→Fin 4 :=
  (Fields.mk (fun _=>0) 1 (fun _ _=>2) (fun _=>3) : Fields s c p (Fin 4)).all

theorem rows_le (s c p : ℕ) : rows s c p ≤ (s+(1+(c+p))+1)^2 := by
  unfold rows
  nlinarith only [Nat.zero_le (s*s),Nat.zero_le (s*c),Nat.zero_le (s*p),
    Nat.zero_le (c*c),Nat.zero_le (p*p),Nat.zero_le (c*p)]

end
end Hierarchy.DescentResetPeerUnionRAM.Axes

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetLocalRoster DescentResetPeerUnionRAM
open DescentDenseHostOrder DescentSIMDLookup DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "height" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card

/-- A query for a reserved contact also selects a previous real signed donor.
Scanning that additional short axis covers reserved sockets with zero flow. -/
def peerEvidenceRows := Axes.rows (stemsCount B) (contactCount B) (privateCount B)

def publicEvidenceRows {n h : ℕ} (board : NonlinearExpanders.Graph n h) (Ht k cap : ℕ) :=
  let Y:=2^n
  let roots:=rootSlots k Y
  Axes.rows (2*(2^k*(2*cap))) (2*(roots*(Y+2^Ht))) (2*(roots*DescentResetCableSlots.cableCap board Ht))

theorem peerEvidenceExact :
    peerEvidenceRows B=publicEvidenceRows ctl.board height k input.placement.cap := by
  have same {m' : ℕ} (Y : NonlinearExpanders.Graph m' h) (m_ : B.reset.n=m') (graph : HEq B.reset.graph Y) :
      publicEvidenceRows B.reset.graph height k input.placement.cap=publicEvidenceRows Y height k input.placement.cap := by
    cases m_
    rw [eq_of_heq graph]
  rw [←same ctl.board B.dimension B.graph]
  unfold peerEvidenceRows publicEvidenceRows stemsCount contactCount privateCount DescentResetCableSlots.cableCap
  simp only [B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left]

theorem peer_program_span (start oldHosts degree bits M : ℕ) :
    Program.endAddress start oldHosts shelf degree (peerEvidenceRows B) bits M=
      Program.endAddress start oldHosts (DescentDenseHostOrder.roster ctl.board k height).card degree
        (publicEvidenceRows ctl.board height k input.placement.cap) bits M := by
  rw [peerEvidenceExact,B.public_hub_slots]

theorem peerEvidenceBound : peerEvidenceRows B ≤ (totalLocal B+1)^2 :=
  Axes.rows_le ..

theorem peerEvidencePower :
    peerEvidenceRows B ≤ (S.epochPower^(S.fallbackExponent cut+Nat.clog 2 (rosterFactor ctl.board height))+1)^2 :=
  (peerEvidenceBound B).trans (Nat.pow_le_pow_left (Nat.add_le_add_right (local_roster_power B) 1) _)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
