import OAI.Hierarchy.DescentSignedFallbackGather
import OAI.Hierarchy.DescentPackedLeafSelector

namespace OAI
/-! # True signed slots and shared measured book tables feed the finite SIMD leaf function -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentPackedLeafSelector DescentRosterOrder
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "R" => Z.placement
local notation "N" => 2^(m-c)*(2*A.cap)
local notation "shortT" => fun t=>shortName c (T.code t)
local notation "ztype" => Z.V×DescentContacts.Endpoint (2^Z.n)
local notation "term" => fallbackCell A S ready digits Z T frame
local notation "bad" => exceptionalCell A S ready digits Z T frame
variable (names : Host J V k ↪ ℕ)

/-- Directory shared by every group. It is indexed on the *normalized* source
and destination only, with no external group number. -/
def leafRankAt (a b : ztype) := (Finset.univ.filter (fun y : ↥(T.leaves.window a)=>
  endpoint T.columns.host y.val<endpoint T.columns.host b)).card

theorem leafRankAt_le (a b : ztype) : leafRankAt A S ready Z T a b≤(T.leaves.window a).card := by
  simpa only [leafRankAt,Finset.card_univ,Fintype.card_coe] using
    (Finset.card_filter_le (s:=Finset.univ) (fun y : ↥(T.leaves.window a)=>endpoint T.columns.host y.val<endpoint T.columns.host b))

theorem leafAmount_fit (s : Bool) (t : Z.Fallback) : (T.leaves.window (shortT t)).card<2^(Ht+2) := by
  let n:=(T.leaves.window (shortT t)).card
  have small : Nat.clog 2 n≤Ht:=(T.leaves.depth s t).symm.le.trans (T.bookHeight s t)
  exact ((Nat.le_pow_clog (by decide : 1<2) n).trans (Nat.pow_le_pow_right (by decide) small)).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))

def signedFields (s : Bool) (t : Z.Fallback) (q : Fin N) : Slot :=
  let j:=finProdFinEquiv.symm q
  let u:=oldCellAt A S ready digits Z T frame t j.1
  let peer:=signedPeer A native S ready names s u j.2
  ⟨peer.isSome,decide (shortT (term s u)=shortT t),bad u,
    peer.elim false bad,
    peer.elim 0 (fun v=>leafRankAt A S ready Z T (shortT t) (shortT (term (!s) v)))⟩

theorem signedFields_pick (s : Bool) (t : Z.Fallback) (q : Fin N) :
    pick Ht (T.leaves.window (shortT t)).card (signedFields A S ready digits native Z T frame names s t q)=
      leafPanel A S ready digits native Z T frame s t q := by
  obtain ⟨j,rfl⟩:=finProdFinEquiv.surjective q
  rw [←signedLeaf_read A S ready digits native Z T frame names s t j]
  simp only [signedFields,Equiv.symm_apply_apply,signedLeaf]
  cases signedPeer A native S ready names s (oldCellAt A S ready digits Z T frame t j.1) j.2 with
  | none=>simp [pick]
  | some v=>
    simp only [pick,cellLeaf,Option.bind_some,Option.isSome_some,Option.elim_some,Bool.true_and]
    rw [Bool.and_comm]; rfl

theorem issued_panel (s : Bool) (t : Z.Fallback) :
    let number:=(T.leaves.window (shortT t)).card
    let operand:=signedFields A S ready digits native Z T frame names s t
    render Ht N (DescentSIMDLookup.encode (Ht+2) (countFields N) (rawFields Ht N number operand))=
      DescentPackedFallbackTree.pack Ht ((R).fallbackBook s t).height (leafPanel A S ready digits native Z T frame s t) := by
  dsimp only
  have room:=leafAmount_fit A S ready Z T s t
  rw [render_read _ _ _ _ room, T.leaves.depth]
  · apply congrArg (DescentPackedFallbackTree.pack _ _)
    exact funext (signedFields_pick A S ready digits native Z T frame names s t)
  · intro q
    dsimp only [signedFields]
    cases eqn : signedPeer A native S ready names s _ _ with
    | none=>exact Nat.two_pow_pos _
    | some v=>exact (leafRankAt_le A S ready Z T _ _).trans_lt room

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
