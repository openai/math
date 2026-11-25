import OAI.Hierarchy.DescentResetTrunkPaddedShape
import OAI.Hierarchy.DescentResetTrunkScalarBanks
import OAI.Hierarchy.DescentResetTrunkCompactScalar
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentResetTrunkScalar
import OAI.Hierarchy.DescentResetStemHeaderAlias

namespace OAI
/-! # The original compact inverse, geometric palette, and measured adjacency issue trunk headers -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

open DescentResetFieldAssembler DescentPackedZip DescentSIMDLookup ProtocolRAM DescentSortedRoster DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_
local notation "rawWord" => DescentResetFieldAssembler.raw
local notation "used" => Fintype.card B.next.V
local notation "N" H:arg => (H*(roster_).card)
local notation "name_" pad:arg => (Z).rawHostRank T ((vertexCode).trans (Fin.castLEEmb pad))

def originalTrunkRack {H : ℕ} (r : Fin H) : Option B.next.V:=
  if active : r.val<used then some ((denseOrder B).symm ⟨r.val,active⟩) else none

theorem original_trunk_headers {H H₁ p word field : ℕ} (pad : Fintype.card input.V≤H) (record : B.Recorded p)
    (ns : Fin (N H)→Fin 3→Option (Fin (N H))) (m : Memory word)
    (number inverse : Bank) (nearBase palBase out : ℕ)
    (positioned : ∀v,present (DescentResetPeerUnionRAM.selfPeers ns) ((name_ pad) v)=
      (insert v ((Z).emittedNear T v)).map (name_ pad))
    (loops : ∀v,(∀j,ns ((name_ pad) v) j≠some ((name_ pad) v)) ↔ v∉(Z).emittedNear T v)
    (rows : ∀(h : Fin (N H)) (j : Fin 3),m (nearBase+j.val*(N H)+h.val)=(DescentPackedColony.target (ns h j):Word word))
    (palette : ∀(c : Fin 3) (h : Fin (N H)),m (palBase+c.val*(N H)+h.val)=
      (DescentResetTrunkPalette.value (Z).graph radius depth_ c h:Word word))
    (counted : m number.base=(used:Word word))
    (ids : ∀v,m (inverse.base+(B.next.vertex v).val)=(((name_ pad) v).val:Word word))
    (bankRoom : used≤ inverse.size) (actorRoom : used≤H₁)
    (namesFit : number.Fits word out) (inverseFit : inverse.Fits word out)
    (nearRoom : ∀j : Fin 3,(scalarBank nearBase (N H) j.val).Fits word out)
    (palRoom : ∀j : Fin 3,(scalarBank palBase (N H) j.val).Fits word out)
    (fieldCap : 5≤2^field) (small : 5≤2^word) (rawWordFit : (N H)<2^word) (room : out+H₁<2^word) :
    let head:=rawTrunkExpr field (N H) nearBase palBase
    let prog:=DescentResetTrunkCompactScalar.phase word H₁ out number inverse head
    prog.Runs m ∧ (∀r : Fin H₁,prog.image m (out+r.val)=
      ((rawWord field ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word word)) ∧
      (∀x,x<out ∨ out+H₁≤x→prog.image m x=m x) ∧
      DescentStaticWordColumn.names prog.program≤11+4*(8*DescentResetTrunkScalar.tableWork+10) ∧
      prog.ticks≤4+H₁*(2*(8*DescentResetTrunkScalar.tableWork+10)+4):=by
  intro head prog
  let descr:=DescentResetTrunkPalette.description (H:=H) (Z).graph radius depth_
  let stored:=fun r : Fin (N H)=>DescentResetTrunkScalar.integer ns r (descr r)
  let here := fun i : Fin used => (name_ pad) ((denseOrder B).symm i)
  have fit (lo k₀ : ℕ) (ok : (scalarBank lo (N H) k₀).Fits word out) (h₀ : Fin (N H)) :
      (Expr.lookup (scalarBank lo (N H) k₀) .row).eval m (h₀.val:Word word)=m (lo+k₀*(N H)+h₀.val):=
    bank_read _ m (h₀.isLt.trans_le (DescentDyadicSpan.span_ge _)) ok
  have values (c : Fin 3) (h₀ : Fin (N H)) : (Expr.lookup (scalarBank palBase (N H) c.val) .row).eval m (h₀.val:Word word)=
      (DescentResetTrunkPalette.value (Z).graph radius depth_ c h₀:Word word):=
    (fit _ _ (palRoom c) h₀).trans (palette c h₀)
  have rt : head.Fits word out:=DescentResetTrunkScalar.fits _ _ _ _ (fun j=>⟨nearRoom j,trivial⟩)
    ⟨palRoom 0,trivial⟩ ⟨palRoom 1,trivial⟩ ⟨palRoom 2,trivial⟩
  have read (v₀ : Fin (N H)) : head.eval m (v₀.val:Word word)=((rawWord field (stored v₀)).val:Word word):=by
    obtain ⟨l,r,c⟩:=DescentResetTrunkPalette.description_at (Z).graph radius depth_ v₀
    apply DescentResetTrunkScalar.read field ns descr v₀ _ _ _ _ m rawWordFit small fieldCap
    · intro j;exact (fit _ _ (nearRoom j) v₀).trans (rows v₀ j)
    · refine (values 0 v₀).trans ?_
      change (((DescentResetTrunkPalette.pointer (Z).graph radius depth_ false v₀).elim (N H) Fin.val : ℕ) : Word word)=_
      rw [←l]
      change (((((descr v₀).map Prod.fst).elim (N H) Fin.val : ℕ) : Word word))=_
      cases descr v₀ <;> rfl
    · refine (values 1 v₀).trans ?_
      change (((DescentResetTrunkPalette.pointer (Z).graph radius depth_ true v₀).elim (N H) Fin.val : ℕ) : Word word)=_
      rw [←r]
      change (((((descr v₀).map (fun x=>x.2.1)).elim (N H) Fin.val : ℕ) : Word word))=_
      cases descr v₀ <;> rfl
    · refine (values 2 v₀).trans ((congrArg (fun n : ℕ=>(n:Word word)) c.symm).trans ?_)
      change (((descr v₀).elim 0 (fun x=>x.2.2.toNat) : ℕ) : Word word)=_
      cases descr v₀ <;> rfl
  have mounted:=DescentResetTrunkCompactScalar.any H₁ out number inverse head m namesFit inverseFit rt room
  refine ⟨mounted.1,?_,mounted.2.1,?_⟩
  · intro r
    have hw:=DescentResetTrunkCompactScalar.words out number inverse head m namesFit inverseFit bankRoom actorRoom room counted here stored
      (fun j=>by simpa only [here,show ∀v,B.next.vertex v=denseOrder B v from fun _=>rfl,Equiv.apply_symm_apply] using ids ((denseOrder B).symm j))
      read r
    by_cases live : r.val<used
    · let j : Fin used:=⟨r.val,live⟩
      let v:=(denseOrder B).symm j
      have trueShape:=trunk_original_scalar B pad record ns v (positioned v) (loops v)
      have phys : DescentResetTrunkCompactScalar.value here stored r = stored (here j) := dite_eq_left live
      have valid : originalTrunkRack B r = some v := dite_eq_left live
      refine hw.trans (congrArg (fun obj => ((rawWord field obj).val : Word word)) ?_)
      rw [valid]
      exact phys.trans trueShape
    · simpa only [DescentResetTrunkCompactScalar.value,originalTrunkRack,dite_eq_right live,Option.elim_none] using hw
  · simpa only [head,raw_trunk_work] using mounted.2.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
