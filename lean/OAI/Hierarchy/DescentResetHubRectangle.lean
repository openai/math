import OAI.Hierarchy.DescentResetHubBits

namespace OAI
/-! # Fixed-width reset host compaction and the actual chronological chooser -/
namespace Hierarchy.DescentDenseHostOrder
open scoped Classical
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)

def publicTag (r t j : ℕ) : Bool :=
  if existsRow : 0<(roster G r t).card then
    hubCode G r t ⟨j%(roster G r t).card,Nat.mod_lt _ existsRow⟩
  else false

theorem publicTag_slot (r t : ℕ) {H : ℕ} (p : Fin H×Fin (roster G r t).card) :
    publicTag G r t (finProdFinEquiv p).val=hubCode G r t p.2 := by
  have live:=p.2.pos
  unfold publicTag
  rw [dite_eq_left live]
  apply congrArg
  apply Fin.ext
  change (p.2.val+(roster G r t).card*p.1.val)%(roster G r t).card=p.2.val
  rw [Nat.add_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt p.2.isLt]

theorem rosterCard_board {n' : ℕ} (Y : NonlinearExpanders.Graph n' h) (eqn : n=n') (same : HEq G Y)
    (r t : ℕ) : (roster G r t).card=(roster Y r t).card := by
  subst n'
  rw [eq_of_heq same]

theorem publicTag_board {n' : ℕ} (Y : NonlinearExpanders.Graph n' h) (eqn : n=n') (same : HEq G Y)
    (r t j : ℕ) : publicTag G r t j=publicTag Y r t j := by
  subst n'
  rw [eq_of_heq same]

end
end Hierarchy.DescentDenseHostOrder

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCommonHost DescentDenseHostOrder
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {H H' : ℕ} (old : Z.V↪Fin H) (pad : H≤H')

theorem rawHostRank_extend (v : ↥(commonNames Z T)) :
    (Z.rawHostRank T (old.trans (Fin.castLEEmb pad)) v).val=(Z.rawHostRank T old v).val := rfl

theorem denseHostRank_extend :
    Z.denseHostRank T (old.trans (Fin.castLEEmb pad))=Z.denseHostRank T old := by
  ext v
  rw [denseHostRank_read,denseHostRank_read]
  rfl

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.ClosedReset
open DescentPacking.PackedMatch.Local.Stage DescentCompiler DescentColonies DescentHubBits
open DescentCommonHost DescentDenseHostOrder DescentCensusRAM DescentIssuedTerminalId ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z wire hist : ℕ} {W : MarkedWorld F d P bits}
  {D n h C f g cut tail : ℕ} {input : Reached W G q ε S k i z D wire hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
local notation "old" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "height" => GroupStage.depthBound D n f g
set_option quotPrecheck false in
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card

theorem public_hub_slots : shelf=(DescentDenseHostOrder.roster ctl.board k height).card := by
  rw [rosterCard_board B.reset.graph ctl.board B.dimension B.graph,B.keyWidth,B.commonDepth,Nat.add_sub_cancel_left]

/-- Every tag fetched by the reset is a word of the fixed, degree-calendar-only ROM,
even when the prior measured root shape and true common-host count change. -/
theorem public_hub_rom {H : ℕ} (i : Fin (H*shelf)) :
    B.reset.hubROM B.terminals i=publicTag ctl.board k height i.val := by
  have get:=publicTag_slot B.reset.graph (B.reset.k-B.terminals.commonDepth) height (finProdFinEquiv.symm i)
  rw [Equiv.apply_symm_apply] at get
  have width : B.reset.k - B.terminals.commonDepth = k := by
    rw [B.keyWidth, B.commonDepth, Nat.add_sub_cancel_left]
  exact get.symm.trans ((publicTag_board B.reset.graph ctl.board B.dimension B.graph _ height i.val).trans
    (congrArg (fun r => publicTag ctl.board r height i.val) width))

/-- Both sides of the host update have public, branch-independent capacities. Padding
the predecessor's sparse roster changes no survivor rank. Thus the same fixed passes
publish every true flag at its very next chronological ID and clear every unused ID. -/
theorem issued_hubs {H cap w : ℕ} (previous : Fintype.card input.V≤H)
    (nextRoom : Fintype.card B.next.V≤cap) (banks : Banks w (H*shelf) (cap+1))
    (flags ids codes : Bank) (m : Memory w)
    (ff : flags.Fits w banks.first) (idd : ids.Fits w banks.first) (cf : codes.Fits w banks.first)
    (roomF : H*shelf≤flags.size) (roomI : H*shelf≤ ids.size) (roomC : H*shelf≤codes.size)
    (fl : flags.base+H*shelf≤ ids.base) (cd : codes.base+H*shelf≤ ids.base)
    (headRoom : ids.base+H*shelf+1<2^w)
    (presence : ∀i : Fin (H*shelf),m (flags.base+i.val)=
      (DescentEdgeTapePrefix.row (fun _ : ↥(ResetInput.commonNames B.reset B.terminals)=>1)
        (fun v=>(B.reset.rawHostRank B.terminals ((old).trans (Fin.castLEEmb previous)) v).val) i.val:Word w))
    (static : ∀j : Fin (H*shelf),m (codes.base+j.val)=((publicTag ctl.board k height j.val).toNat:Word w)) :
    let expr:=destination banks.bins cap flags ids
    let first:=ProtocolRAMEndpointPrefix.exclusive w flags.base ids.base (H*shelf)
    ∃out : Memory w,(first.seq (tally banks expr (.lookup codes .row))).Exec m out
        ((10+(3+12*(H*shelf)))+tallyCost banks expr (.lookup codes .row)) ∧
      (∀j : Fin cap,out (banks.bins+j.val)=((Census.hub B.next.placement
        (B.next.vertex.trans (Fin.castLEEmb nextRoom)) j).val:Word w)) ∧
      ∀a< min ids.base banks.first,out a=m a := by
  obtain ⟨out,go,real,padding,frame⟩:=B.reset.prefix_hubs B.terminals
    ((old).trans (Fin.castLEEmb previous)) nextRoom banks flags ids codes m ff idd cf
    roomF roomI roomC fl cd headRoom presence (fun j=>by simpa only [B.public_hub_rom] using static j)
  have ord:=B.reset.denseHostRank_extend B.terminals (old) previous
  rw [ord] at real padding
  exact ⟨out,go,B.hub_for_chooser nextRoom banks.bins out real padding,frame⟩

end
end Hierarchy.DescentSixParty.ClosedReset

end OAI
