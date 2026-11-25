import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentFundedRootObservation

namespace OAI
/-! # The fallback item leaf read from its issued operand packet -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groups : J↪ℕ) (vertex : V↪Fin H)
variable (Z : ResetInput (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
    (T : ResetInput.Terminals (F:=F) Z)
    (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (snap : RootObservation A S ready digits native groups vertex Z T frm field)
set_option quotPrecheck false
local notation "stageCfg" sample => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := 2^(m-T.commonDepth)
  fineBits := k
  fieldBits := field
  residual := Z.k-T.commonDepth
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation "rank" => ranks (a:=Z.k-T.commonDepth) (Y:=2^Z.n) (D:=A.degree)
  snap.chart (2^Ht) (Ht+2) snap.memory

/-- All signed positions of the reached packet determine the same occupied and
empty leaves as the physical fallback tree, including its padded rows. -/
theorem rowsAt_leaf (sample : DescentFallbackOperandBranch.Config) (s : Bool) (t : Z.Fallback)
    (x : (stageCfg sample).Data Z.n)
    (packet : (stageCfg sample).packet x=DescentFallbackPeriod.inputs (field:=field)
      snap.stencil snap.peers snap.marks (fun u j=>(rank u j).val)
      (vertex (frm.host.symm (T.code t).1)) (Z.rootBlock T (.inr t))) (j : Fin (2^(m-T.commonDepth)*(2*A.cap))) :
    ((stageCfg sample).rowsAt x s (Z.fallLabel T t,(T.code t).2.2) (chartShape A S ready Z T t)
      (T.leaves.window (shortName T.commonDepth (T.code t))).card j).leaf =
      (leafPanel A S ready digits native Z T frm s t j).map Fin.val := by
  have truthful := window_input (field:=field) A S ready digits native Z T frm groups vertex snap.word rank
    snap.stencilRead snap.rosterRead snap.markRead (frm.host.symm (T.code t).1) (Z.rootBlock T (.inr t))
  obtain ⟨⟨lo,z⟩,rfl⟩:=finProdFinEquiv.surjective j
  simp only [DescentFallbackOperandBranch.Config.rowsAt,Equiv.symm_apply_apply,packet,truthful]
  apply congrArg (Option.map Fin.val)
  apply window_slot A S ready digits native Z T frm groups vertex snap.word rank snap.wordFits
    snap.signedFits snap.onWire snap.countFits s t lo z
  have prior := measured_before A S ready digits native Z T frm groups vertex snap.n snap.f snap.B snap.wire snap.K
    snap.wt snap.flow snap.roster snap.chart snap.memory snap.cutoff snap.header snap.room snap.layouts
    snap.old snap.hubs snap.pos snap.heightFits snap.available snap.encoded s t (finProdFinEquiv (lo,z))
  simpa only [Equiv.symm_apply_apply, shortName] using prior

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
