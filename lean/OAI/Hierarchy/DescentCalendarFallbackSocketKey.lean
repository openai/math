import OAI.Hierarchy.DescentFallbackSocketCases
import OAI.Hierarchy.DescentMeasuredTreeSocketReply
import OAI.Hierarchy.DescentMeasuredTreeRange

namespace OAI
/-! Original reset-tree gate keys at every measured row and every flattened p-word. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
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
set_option maxHeartbeats 500000
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
local notation:max "cellAt" l:arg e:arg => (⟨l,prefixAt (DescentFixedNamedContact.code (bk).codes (link (R).contact (R).owner s (.inr t))) (l).val e⟩ : Physical.Site (bk).height)
local notation:max "gateAt" q:arg => (Z).laneRecipe birth batches p hp unitFit (venue q)
local notation:max "header" x:arg => (cfg).header ((pub).basic x)
local notation:max "here" q:arg => (Z).localShape T ((Z).placed T ((Z).privateSiteAt T s (.inr t) q))

/-- For every live flattened argument of the original installed fallback
gate the issued lookup names a registered face and its actual p-word. -/
theorem fallback_socket_key (q₀ : Physical.Site (bk).height) (gate : (gateAt q₀).Node)
    (out : NodeOrder.All installedArchive) (origin : resetOrigin B hp whole a out=.inr (.inr ⟨venue q₀,gate⟩))
    (x : (pub).Data (Z).n)
    (packet : (cfg).packet ((pub).basic x)=DescentFallbackPeriod.inputs (n:=(Z).n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast widthCast)) snap.peers
      (fun u hi lo=>snap.marks u hi (lo.cast widthCast)) (fun u j=>(ranks₀ u j).val)
      (pad (who t)) (hiAt t))
    (hostRead : ((cfg).header ((pub).basic x) 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t))))
    (groupWord : ∀e : item s t,((cfg).digit ((pub).basic x) (row s e.val) 0).val=
      compress (groupDomain words B.frame.basis small (who t) (hiAt t)) ((A).pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item s t,((cfg).digit ((pub).basic x) (row s e.val) 1).val=((A).block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=((A).site input.vertex input.valid.coordinates u).val)
    (sorted : SourceSorted W input.order)
    (active : (header x 0).val≠0) (capRead : (header x 1).val=(A).cap)
    (shapeRead : (header x 2).val=(DescentDenseHostOrder.localRank (Z).graph r Ht (here q₀)).val)
    (slot : Fin nodes) (numbered : slot.val=(Z).nodeIndex birth batches p hp unitFit (venue q₀) gate)
    (arg : Fin args) :
    let sh₀:=(Z).laneShape birth batches p hp unitFit (venue q₀)
    let raw:=NodeOrder.followNames B.reblock pre_ out
    (arg.val<(sh₀.keys gate).length →
      ∃number word count mark, ∃socket : PublicSocket B (treeReceiver B (venue q₀)) batches word mark number,
        (pub).mixed (Z).graph slot.val arg.val x=some (number,word,count,mark) ∧
        keyCable installed raw arg.val=some (socket.face.val.1,word)) ∧
    ((sh₀.keys gate).length≤arg.val → (pub).mixed (Z).graph slot.val arg.val x=none) :=by
  dsimp only
  rcases q₀ with ⟨l,loc⟩
  obtain ⟨⟨e,atSite⟩,b,rfl⟩:=DescentChosenRouter.installedTreeGate_cases (R) (Z).graph (Z).positive (Z).pay
    (Z).circuit birth d batches p hp unitFit s t ⟨l,loc⟩ gate
  change prefixAt (DescentFixedNamedContact.code (bk).codes (link (R).contact (R).owner s (.inr t))) l.val e=loc at atSite
  subst loc
  let xs:=(cfg).rowsAt ((pub).basic x) s (token t) ((Z).observedRootAddress T t) (num t)
  have rootRows:=reached_root_rows B grp padded snap s t ((pub).basic x) packet hostRead groupWord fineWord indexed sorted e
  have raw:=tree_socket_words B hp unitFit s t e b xs rootRows l arg.val
  have nth:=DescentChosenRouter.installedTreeIndex (R) (Z).graph (Z).positive (Z).pay (Z).circuit birth
    d batches p hp unitFit s t (cellAt l e) ⟨e,rfl⟩ b
  have mixed:=GroupStage.observed_tree_reply_cast (A) S input.valid words input.order grp input.vertex padded
    (Z) (T) B.frame snap (effective:=(Z).k) (extent:=B.keyWidth) (zEq:=input.grain.symm) (wireEq:=input.edges.symm) (countEq:=B.count_eq) (pub) s t x packet hostRead
    groupWord fineWord indexed sorted capRead e b p hp l active shapeRead arg slot
    (by
      refine (numbered.trans nth).trans ?_
      rw [B.order_eq]
      let code := DescentFixedNamedContact.code (bk).codes (link (R).contact (R).owner s (.inr t))
      let X := DescentContactTree.Cell code l.val (prefixAt code l.val e)
      let ordinal := DescentOrderedWords.Contact.cellKey
        (DescentOrderedReset.itemKey (DescentOrderedReset.grains W B.count input.order)
          (R).contact (R).owner s (.inr t)) code l.val (prefixAt code l.val e)
      let target : X := ⟨e,rfl⟩
      exact congrArg (fun inst : Fintype X =>
        (@DescentOrderedWords.before X inst _ ordinal target).card*batches+b.val) (Subsingleton.elim _ _))
  dsimp only at mixed
  rw [←B.order_eq] at mixed
  have length:=(Z).tree_gate_words birth batches p hp unitFit s t (cellAt l e) ⟨e,rfl⟩ b
    ((Z).treeMultiple batches p unitFit s t (cellAt l e))
  constructor
  · intro live
    obtain ⟨number,word,count,mark,socket,ref,reply,keys,route⟩:=raw.1 (live.trans_eq length)
    refine ⟨number,word,count,mark,socket,mixed.trans reply,?_⟩
    exact (device_route_key B hp one positive whole wide a sh out _ _ origin arg.val ref keys).trans (congrArg some route)
  · intro cold
    exact mixed.trans (raw.2 (length.ge.trans cold))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
