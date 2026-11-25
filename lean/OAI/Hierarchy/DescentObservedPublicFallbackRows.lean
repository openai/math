import OAI.Hierarchy.DescentObservedTreeSocketKey
import OAI.Hierarchy.DescentMeasuredFallbackDonors
import OAI.Hierarchy.DescentStemCoordinateObserved

namespace OAI
/-! # The six authentic old-tree readings from the original coordinate sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentPhysicalOrder DescentStageEdgeReceipt ThreeFlat.Routing
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentStageEdgeReceipt
open DescentFallbackItemSelect DescentNamedContact
open DescentPrimitivePalette DescentLaneGates DescentBundleHistory DescentResetGates DescentResetFreshWires
open DescentResetLocalNodes DescentLocalArchiveOrder DescentKernelHistory DescentTreeLaneProgram DescentContactTree
open Chronology Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation "native" => input.order.trans Fin.valEmbedding
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item (R).contact (R).owner s (.inr t)
local notation:max "token" t:arg => ((Z).fallLabel T t,((T).code t).2.2)
local notation:max "num" t:arg => ((T).leaves.window (shortName c ((T).code t))).card
local notation:max "who" t:arg => B.frame.host.symm ((T).code t).1
local notation:max "hiAt" t:arg => (Z).rootBlock T (.inr t)
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "widthCast" => congrArg (fun l=>2^(l-c)) B.keyWidth
local notation:max "posOld" s:arg e:arg => localAddress A native S input.valid words B.frame.basis («c»:=c) s (beforeStem B e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((posOld s e).1.cast (widthCast).symm),(posOld s e).2)
variable {H field query lanes nodes args grain p size : ℕ} (hp : 0<p) (one : 1≤ size)
  (positive : 0<B.reset.unit) (whole : p∣B.reset.unit) (wide : max 1 (max B.reset.width (C*B.reset.width))≤ size)
  (a : Archive W) (sh : DescentBundleHistory.WorldShape p size a.bit)
local notation "batches" => (Z).unit/p
local notation "unitFit" => ((Nat.div_mul_cancel whole).symm : (Z).unit=batches*p)
local notation "cfg" => flatConfig B field query lanes batches batches nodes args
variable (grp : Fin (S.groupCount i)↪ℕ) (padded : Fintype.card input.V≤H)
local notation "pad" => input.vertex.trans (Fin.castLEEmb padded)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i) (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb padded)) B.reset B.terminals B.frame field)
local notation "ranks₀" => ranks (a:=r) («Y»:=Y) (D:=(A).degree) snap.chart (2^Ht) (Ht+2) snap.memory


local notation "pub" => publicOperandConfig B field query lanes batches batches nodes args grain
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ positive) (B.unit ▸ whole)
local notation "installed" => reentryWorldShape split_ (Z) (T) birth _ hp unitFit (resetMenu B) one wide
local notation "old_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (old_).batchedReset (Z) (T) birth batches p hp unitFit (resetMenu B)
local notation "installedArchive" => (resetArchive B p hp whole a).bit
local notation:max "ord" earlier:arg => DescentLocalArchiveOrder.reset B p hp whole a earlier
variable (s : Bool) (t : B.reset.Fallback)
local notation "bk" => (R).fallbackBook s t
local notation:max "venue" q:arg => (⟨(s,.inr t),q⟩ : (Z).bank.Site)
local notation:max "gateAt" q:arg => (Z).laneRecipe birth batches p hp unitFit (venue q)
local notation:max "header" x:arg => (cfg).header ((pub).basic x)
local notation:max "here" q:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T s (.inr t) q))

/-- The original captured packet and dated coordinate sheet give all six readings
for the exceptional tree, independent of which installed gate will ask for a socket. -/
theorem fallback_rows_at (x : (pub).Data (Z).n) (band : Fin (S.groupCount (i+1))) (block : Block k)
    (joined : band.val*2^k+block.val=(hiAt t).val)
    (earlier : 0< i) (sorted : SourceSorted W input.order)
    (packet : (cfg).packet ((pub).basic x)=DescentFallbackPeriod.inputs (n:=(Z).n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast widthCast)) snap.peers
      (fun u hi lo=>snap.marks u hi (lo.cast widthCast)) (fun u j=>(ranks₀ u j).val) (pad (who t)) (hiAt t))
    (selfWord : ((cfg).header ((pub).basic x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t))))
    (hosts M valueBits : ℕ)
    (read : ∀(e : item s t)(axis : Fin 2),((cfg).digit ((pub).basic x) (row s e.val) (axis.castLE (by decide))).val=
      (coords B hosts M valueBits).value B.frame.basis axis.castSucc block ((posOld s e.val).1) band) :
    FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain) B s t x:=by
  refine ⟨H,grp,padded,snap,⟨packet,selfWord,?_,?_,input.siteName earlier,sorted⟩⟩
  all_goals
    intro e₀
    have sampled:=read e₀
    rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
    rcases B with ⟨ct,rfl,oldFit,order₀,sourceEq,Z₀,T₀,age,date,extent,tickets,unit,dimension,
      tapeWidth,graph,fr,roster_,raw,geometry,hubs,valid,grain₀,wire_,atoms,branch,capacity⟩
    subst order₀
    let digits:=S.resetInputDigits ctl.base ctl.radix i
    have split (y) : (digits y).1.val=y.val/2^k ∧ (digits y).2.val=y.val%2^k:=⟨rfl,rfl⟩
    have original:=GroupStage.fallback_coordinate_values phase S ready digits (oldOrder.trans Fin.valEmbedding)
      Z₀ T₀ fr hosts M valueBits s t block band joined split e₀
    first | exact (sampled 0).trans original.1 | exact (sampled 1).trans original.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
