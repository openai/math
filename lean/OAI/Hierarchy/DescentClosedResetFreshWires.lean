import OAI.Hierarchy.DescentResetWireNames
import OAI.Hierarchy.DescentResetPrimitiveWords
import OAI.Hierarchy.DescentArchiveSliceLayout

namespace OAI
/-! # New reset nodes have only incident cable operands in the reached physical archive -/
namespace Hierarchy.DescentResetFreshWires
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
section Installed
variable {H Q Y : Type} [Fintype H] [Fintype Q] {L d' : ℕ} {B : BitDescription W}
    (sh : WorldShape p R B) (hp : 0<p) (one : 1≤R)
    (home : W.graph.Site→H) (grp : Bool→W.graph.Edge→Q) (hub : H→Bool)
    {width : W.graph.Edge→ℕ} (same : width=W.graph.width) (board : Network d' (Bool×Q) (publicWidth grp width))
    (legacy sorted : board.Tables F) (ids : W.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board) (valid : ReadsBits board scalar prog sorted)
    (device : ∀v,Shape p (prog v)) (bound : ∀v u j g,((device v).chunk u j g).stride≤R)
    (widths : ∀e,p∣board.width e)
local notation "post" => B.installed home grp hub same board legacy sorted ids scalar prog valid
local notation "origin" => NodeOrder.installedNames B home grp hub same board legacy sorted ids scalar prog valid
local notation "worldShape" => installedWorldShape sh hp one home grp hub same board legacy sorted ids scalar prog valid device bound widths

omit [Fintype Q] in
theorem new_install (exposed : ∀v u j g i,∃ref,(((device v).chunk u j g).get i)=.inl ref)
    (x : NodeOrder.All (post)) (fresh : ∀a,origin x≠.inl a) :
    nodeWires worldShape x :=by
  subst width
  rcases x with ⟨(⟨side,h⟩|v),u⟩
  · cases side
    · rcases u with ⟨⟨v,rfl⟩,u⟩
      exact (fresh ⟨v,u⟩ rfl).elim
    · exact relay_wires W.graph home grp board ids sh.edges hp h u
  · exact pulled_wires W.graph home grp board ids sh.edges hp v (device v) u (exposed v u)
end Installed

private theorem split_named_shape {B : BitDescription W} (hp : 0<p) (q : ℕ) (pos : 0<q)
    (whole : p∣q) (s : WorldShape p R B) (m : W.graph.Edge→ℕ)
    (cut : ∀e∈W.core,W.graph.width e=m e*q) (vs : Equiv.Perm (W.pieces q m cut).graph.Site)
    (es : Equiv.Perm (W.pieces q m cut).graph.Edge)
    (a : Normalize.CutsEqual q (.split W q m cut (.named _ vs es (.done _)))) :
    WorldShape.follow hp pos whole (.split W q m cut (.named _ vs es (.done _))) a s =
      (s.pieces m q cut hp pos whole).renamed vs es := by
  have h : a = (⟨rfl,trivial⟩ : Normalize.CutsEqual q
      (.split W q m cut (.named _ vs es (.done _)))) := Subsingleton.elim _ _
  subst a
  unfold WorldShape.follow
  rfl

variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<b.reset.unit) (whole : p∣b.reset.unit)
    (wide : max 1 (max b.reset.width (C*b.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular b.count (z*G.b) b.fit hp (b.unit ▸ pos) (b.unit ▸ whole)
local notation "key_" => DescentOrderedReset.grains W b.count b.order
local notation "fit_" => ((Nat.div_mul_cancel whole).symm : b.reset.unit=b.reset.unit/p*p)
local notation "installed" => reentryWorldShape split_ b.reset b.terminals key_ _ hp fit_ (resetMenu b) one wide
local notation "after_" => WorldShape.follow hp pos whole b.reblock b.cuts installed
local notation "next_" => (resetArchive b p hp whole a).bit

local notation "coarse" => b.reset.orderedReentry b.terminals key_
local notation "count_" => fun e=>(coarse).graph.width e/b.reset.unit

local notation "vertices" => b.frame.host.symm.toEmbedding.trans cap.vertex
local notation "hostRank" => (b.reset.rawHostRank b.terminals vertices).trans Fin.valEmbedding
local notation "siteRank" => b.raw.siteFrom
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) hostRank) b.valid.coordinates
local notation "oldRank" => (b.reset.nativeResetEdges b.terminals vertices key_).order.trans Fin.valEmbedding
local notation "edgeRank" => DescentResetLocalOrder.allCode b.raw oldRank S b.valid siteRank
local notation "cutFit" => b.reset.counts_fit b.terminals

theorem closed_shape :
    after_ = ((installed).pieces count_ b.reset.unit cutFit hp pos whole).renamed
      (DescentPhysicalOrder.rename siteRank) (DescentPhysicalOrder.rename edgeRank) :=
  split_named_shape hp b.reset.unit pos whole installed count_ cutFit _ _ b.cuts

/-- Both fresh parts of the actual reset node order, including all public bank sockets
and both sides of every relay, remain incident after the selected grain split and names. -/
theorem closed_wires (x : NodeOrder.All next_) (fresh : ∀y,resetOrigin b hp whole a x≠.inl y) :
    nodeWires after_ x :=by
  rw [closed_shape b hp one pos whole wide a sh]
  refine named_wires ((installed).pieces count_ b.reset.unit cutFit hp pos whole)
    (DescentPhysicalOrder.rename siteRank) (DescentPhysicalOrder.rename edgeRank) x.1 x.2 ?_
  refine piece_wires installed count_ b.reset.unit cutFit hp pos whole _ _ ?_
  unfold reentryWorldShape
  apply new_install
  · intro v u j g i
    cases found : ((b.reset.laneShape key_ _ p hp fit_ v).chunk u j g).get i with
    | inl ref=>exact ⟨ref,found⟩
    | inr h=>exact nomatch h.port
  · exact fresh

theorem closed_pointer (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_)
    (fresh : ∀y,resetOrigin b hp whole a x≠.inl y)
    (j : Fin (((after_).sites x.1).keys x.2).length) :
    ∃(e : Incident _ x.1) (chunk : ℕ) (fit : (chunk+1)*p≤b.reblock.result.graph.width e.val),
      Reached.argumentPointer b.next next_ rank after_ hp pin args x j.val=Reached.firstCable b.next hp x.1 e chunk fit :=
  original_cable after_ b.next rank hp pin args x.1 x.2 (closed_wires b hp one pos whole wide a sh x fresh) j

end
end Hierarchy.DescentResetFreshWires

end OAI
