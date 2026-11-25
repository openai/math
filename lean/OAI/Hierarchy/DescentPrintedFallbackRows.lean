import OAI.Hierarchy.DescentObservedPublicFallbackRows
import OAI.Hierarchy.DescentRelaySocketObserved

namespace OAI
/-! # The saved packet and calibrated GL sheet on the original native fallback configuration -/
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

open DescentResetOperandComponents
local notation "adj" => ({(cfg) with
  oldDegree := (A).degree
  oldCap := (A).cap
  donors := 2^(m-(T).commonDepth)
  fineBits := k
  fieldBits := field
  residual := (Z).k-(T).commonDepth
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)

private theorem header_from_cast {a₀ b₀ : DescentFallbackOperandBranch.Config} (eq : a₀=b₀) {dim}
    (x : b₀.Data dim) (j : Fin 8) : (b₀.header x j).val=(a₀.header (eq.symm ▸ x) j).val :=by subst b₀;rfl

private theorem digit_from_cast {a₀ b₀ : DescentFallbackOperandBranch.Config} (eq : a₀=b₀) {dim}
    (x : b₀.Data dim) (j : Fin b₀.count) (j₀ : Fin a₀.count) (same : j.val=j₀.val) (axis : Fin 12) :
    (b₀.digit x j axis).val=(a₀.digit (eq.symm ▸ x) j₀ axis).val :=by
  subst b₀
  cases Fin.ext same
  rfl

private theorem packet_from_cast (base : DescentFallbackOperandBranch.Config) {a₀ b₀ n H G : ℕ}
    (eq : a₀=b₀) (v : ({base with donors:=a₀}:DescentFallbackOperandBranch.Config).Data n)
    (own : Fin H→Fin G→Fin b₀→ℕ) (peers : Fin H→Fin base.oldDegree→Option (Fin H))
    (signs : Fin H→Fin G→Fin b₀→Fin (2*base.oldCap)→Option (DescentSharedCableNames.Stage.Live base.oldDegree base.oldCap))
    (ranks_ : Fin H→Fin (DescentSharedBookScan.width base.residual (2^n) base.oldDegree)→ℕ)
    (h : Fin H) (g : Fin G)
    (seen : ({base with donors:=b₀}:DescentFallbackOperandBranch.Config).packet
      ((congrArg (fun n₀ : ℕ=>({base with donors:=n₀}:DescentFallbackOperandBranch.Config)) eq) ▸ v)=
      DescentFallbackPeriod.inputs own peers signs ranks_ h g) :
    ({base with donors:=a₀}:DescentFallbackOperandBranch.Config).packet v=
      DescentFallbackPeriod.inputs (fun u hi lo=>own u hi (lo.cast eq)) peers
        (fun u hi lo=>signs u hi (lo.cast eq)) ranks_ h g :=by
  subst b₀
  exact seen

theorem fallback_printed_rows (x : (pub).Data (Z).n) (band : Fin (S.groupCount (i+1))) (block : Block k)
    (joined : band.val*2^k+block.val=(hiAt t).val) (earlier : 0< i) (sorted : SourceSorted W input.order)
    (packet : (adj).packet (relayPhysicalRow B x)=DescentFallbackPeriod.inputs (field:=field)
        snap.stencil snap.peers snap.marks (fun u j=>(ranks₀ u j).val) (pad (who t)) (hiAt t))
    (selfWord : ((adj).header (relayPhysicalRow B x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t))))
    (hosts M valueBits : ℕ)
    (read : ∀(j:Fin (adj).count)(axis : Fin 2),((adj).digit (relayPhysicalRow B x) j (axis.castLE (by decide))).val=
      (coords B hosts M valueBits).value B.frame.basis axis.castSucc block
        (finProdFinEquiv.symm j : Fin (2^(m-c))×Fin (2*(A).cap)).1 band) :
    FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain) B s t x:=by
  have types:=relay_socket_config (field:=field) (query:=query) (lanes:=lanes) («batches»:=batches)
    (split:=batches) (nodes:=nodes) (args:=args) B
  refine fallback_rows_at B grp padded snap s t x band block joined earlier sorted ?_ ?_ hosts M valueBits ?_
  · exact packet_from_cast cfg widthCast ((pub).basic x) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks₀ u j).val) (pad (who t)) (hiAt t) packet
  · exact (header_from_cast types ((pub).basic x) 3).trans selfWord
  · intro endpoint ax
    let target : Fin (adj).count:=finProdFinEquiv ((posOld s endpoint.val).1,(posOld s endpoint.val).2)
    have address : (row s endpoint.val).val=target.val:=by
      simp only [target,finProdFinEquiv_apply_val,Fin.val_cast]
    have value:=(digit_from_cast types ((pub).basic x) (row s endpoint.val) target address
      (ax.castLE (by decide))).trans (read target ax)
    simpa only [target,Equiv.symm_apply_apply] using value

section
variable (currentBatch : ℕ) (calibrated : currentBatch = B.reset.unit/p)
local notation "calibratedCfg" => flatConfig B field query lanes currentBatch batches nodes args
local notation "calibratedPub" => publicOperandConfig B field query lanes currentBatch batches nodes args grain
local notation "calibratedAdj" => ({(calibratedCfg) with
  oldDegree := (A).degree
  oldCap := (A).cap
  donors := 2^(m-(T).commonDepth)
  fineBits := k
  fieldBits := field
  residual := (Z).k-(T).commonDepth
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)

local notation:max "printedPhysical" row_:arg => relayPhysicalRow (field:=field) (query:=query) (lanes:=lanes)
  («batches»:=currentBatch) (split:=B.reset.unit/p) (nodes:=nodes) (args:=args) (grain:=grain) B row_
include calibrated in
theorem calibrated_fallback_printed_rows (x : (calibratedPub).Data (Z).n) (band : Fin (S.groupCount (i+1))) (block : Block k)
    (joined : band.val*2^k+block.val=(hiAt t).val) (earlier : 0< i) (sorted : SourceSorted W input.order)
    (packet : (calibratedAdj).packet (printedPhysical x)=DescentFallbackPeriod.inputs (field:=field)
        snap.stencil snap.peers snap.marks (fun u j=>(ranks₀ u j).val) (pad (who t)) (hiAt t))
    (selfWord : ((calibratedAdj).header (printedPhysical x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t))))
    (hosts M valueBits : ℕ)
    (read : ∀(j:Fin (calibratedAdj).count)(axis : Fin 2),((calibratedAdj).digit (printedPhysical x) j (axis.castLE (by decide))).val=
      (coords B hosts M valueBits).value B.frame.basis axis.castSucc block
        (finProdFinEquiv.symm j : Fin (2^(m-c))×Fin (2*(A).cap)).1 band) :
    FallbackRows (p:=p) (field:=field) (query:=query) (lanes:=lanes) (nodes:=nodes) (args:=args) (grain:=grain) B s t x := by
  subst currentBatch
  exact fallback_printed_rows B grp padded snap s t x band block joined earlier sorted packet selfWord hosts M valueBits read
end

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
