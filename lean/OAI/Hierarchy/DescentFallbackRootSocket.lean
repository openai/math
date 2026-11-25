import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentClosedDeviceArgumentKeys
import OAI.Hierarchy.DescentFallbackRootLanePort
import OAI.Hierarchy.DescentOperandApertureOrder
import OAI.Hierarchy.DescentTreeOperandReply
import OAI.Hierarchy.DescentResetTrunkOperandPrefix

namespace OAI
/-! # The original stem selected by an exceptional root operand -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentFallbackOperandQuery DescentNextSignedWindow DescentResetWireTags DescentTreePrefixIntervals
open DescentRouterSlots DescentContactTree DescentSharedCableNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)



local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "rr" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation "Face" u:arg => Roster.Face A₁ ord₁ (blocks B) u




open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentOrderedWords DescentLaneGates
open DescentNamedContact DescentFallbackItemSelect
local notation "siteNames" => installedNames old (T).home (placement).input (T).hub same (Z).bank (Z).tables

/-- The stage parser refills its dimensions from its original public chart. -/
def stageConfig (field query lanes batches split nodes args grain : ℕ) : DescentResetPublicOperandBook.Config :=
  let sample:=publicOperandConfig B field query lanes batches split nodes args grain
  let chart := {sample.oldConfig.toShape with
    fieldBits := field
    residual := (Z).k-(T).commonDepth
    maxDepth := GroupStage.depthBound D n f g}
  let oldConfig := {sample.oldConfig with
    toShape := chart
    oldDegree := (A).degree
    oldCap := (A).cap
    donors := 2^(S.groupWidth k tail i+k-(T).commonDepth)
    fineBits := k}
  {sample with oldConfig := oldConfig}

/-- The stored reset key width establishes the exact donor exponent in both parsers. -/
theorem stage_config_eq (field query lanes batches split nodes args grain : ℕ) :
    stageConfig B field query lanes batches split nodes args grain=
      publicOperandConfig B field query lanes batches split nodes args grain :=by
  unfold stageConfig
  rw [←B.keyWidth]
  rfl

theorem stage_old_config_eq (field query lanes batches split nodes args grain : ℕ) :
    (stageConfig B field query lanes batches split nodes args grain).oldConfig=
      flatConfig B field query lanes batches split nodes args :=
  congrArg DescentResetPublicOperandBook.Config.oldConfig
    (stage_config_eq B field query lanes batches split nodes args grain)

/-- The actual receiver of a bank node after the final reset renaming. -/
def treeReceiver (v : (Z).bank.Site) : Host :=
  Stage.home A₁ (hop ((siteNames).symm (.inr v)))

/-- The selected face lands at the actual unrenamed installed site. -/
theorem treeReceiver_endpoint (v : (Z).bank.Site) (face : Face (treeReceiver B v)) :
    (if face.val.2 then (coarse).graph.dst face.val.1 else (coarse).graph.src face.val.1)=
      (siteNames).symm (.inr v) :=by
  apply same_site B
  cases sgn : face.val.2 <;> simpa only [sgn,Bool.false_eq_true,ite_false,ite_true,blocks,treeReceiver] using face.property.2

private theorem stem_at_bank (v : (Z).bank.Site) (socket : Attached (Z).bank v)
    (e : Fibre ((placement).input socket.val.1) socket.val.2) :
    (blocks B).dst (stemParent B (socket.val.1,e.val))=treeReceiver B v :=by
  change Stage.home A₁ (hop _)=Stage.home A₁ (hop _)
  apply congrArg (fun a : (coarse).graph.Site=>Stage.home A₁ (hop a))
  apply (siteNames).injective
  rw [Equiv.apply_symm_apply,(stem_nodes B socket.val.1 e.val).2.1,e.property]
  exact congrArg Sum.inr socket.property

/-- Each digit comes from the actual ordered exterior fibre. This calculation
also covers a word belonging to the grain after the one at which the lane began. -/
theorem root_route_word {p batch : ℕ} (hp : 0<p) (fit : (Z).unit=batch*p)
    (v : (Z).bank.Site) (socket : Attached (Z).bank v)
    (e : Fibre ((placement).input socket.val.1) socket.val.2) (word part : ℕ)
    (wordFit : (word+1)*p≤boundaryWidth (Z).bank v (.inr socket)) (small : part<batch)
    (serial : word=(DescentOrderedWords.before
      (DescentOrderedReset.fibreKey key ((placement).input socket.val.1) socket.val.2) e).card*batch+part) :
    deviceRoute B hp v ⟨.inr socket,word,wordFit⟩=(stemParent B (socket.val.1,e.val),part) :=by
  let ord:=DescentOrderedReset.fibreKey key ((placement).input socket.val.1) socket.val.2
  let widths:=fun _ : Fibre ((placement).input socket.val.1) socket.val.2=>(Z).unit
  let digit : Fin (widths e):=⟨part*p,by change part*p<(Z).unit;rw [fit];exact Nat.mul_lt_mul_of_pos_right small hp⟩
  let r : BlockRef p (boundaryWidth (Z).bank v):=⟨.inr socket,word,wordFit⟩
  let ref := (r.atBit ⟨0,hp⟩).2
  have pos : (DescentOrderedWords.address ord widths) ⟨e,digit⟩=ref:=by
    apply Fin.ext
    change DescentOrderedWords.offset ord widths e+part*p=word*p+0
    simp only [DescentOrderedWords.offset,ord,widths,Finset.sum_const,nsmul_eq_mul,fit,serial,Nat.add_zero]
    simp only [Nat.add_mul,Nat.mul_assoc,Nat.cast_id]
  have selected : (DescentOrderedWords.address ord widths).symm ref=⟨e,digit⟩:=
    (DescentOrderedWords.address ord widths).symm_apply_eq.mpr pos.symm
  change (stemParent B (socket.val.1,((DescentOrderedWords.address ord widths).symm ref).1.val),
    ((DescentOrderedWords.address ord widths).symm ref).2.val/p)=_
  rw [selected]
  change (_,part*p/p)=_
  rw [Nat.mul_div_cancel _ hp]

variable {field query lanes batches nodes args p : ℕ} (hp : 0<p) (fit : B.reset.unit=batches*p)
local notation "cfg" => flatConfig B field query lanes batches batches nodes args
local notation "placementItem" s:arg t:arg => DescentRouterSlots.Item (placement).contact (placement).owner s (.inr t)
local notation "code" s:arg t:arg => DescentFixedNamedContact.code ((placement).fallbackBook s t).codes
  (DescentRouterSlots.link (placement).contact (placement).owner s (.inr t))
local notation "loc" s:arg t:arg e:arg => (⟨(s,.inr t),⟨0,prefixAt (code s t) 0 e⟩⟩ : (Z).bank.Site)
local notation "portKey" s:arg r:arg => DescentOrderedReset.fibreKey key ((placement).input s) r
local notation "oldPos" s:arg j:arg => localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)
local notation "rootRows" xs:arg => DescentFallbackItemSelect.rows (cfg).maxDepth [] xs

/-- The rank column and the residual/signed columns read in the original
fallback packet. The rank is in the actual, uniformly wide input fibre. -/
structure RootRows (s : Bool) (r : (placement).Public) (xs : Fin (cfg).count→DescentFallbackItemSelect.Item) : Prop where
  row : ∀e : Fibre ((placement).input s) r, ∃j : ↥(rootRows xs),
    rank xs (rootRows xs) j.val=(DescentOrderedWords.before (portKey s r) e).card ∧
    (xs j.val).residual=(oldPos s e.val).1.val ∧ (xs j.val).signed=(oldPos s e.val).2.val


private theorem fibre_rank_onto {X : Type*} [Fintype X] {N : ℕ} (ord : X↪Fin N)
    (n : ℕ) (h : n<Fintype.card X) :
    ∃e : X,(DescentOrderedWords.before ord e).card=n :=by
  let s : Fin (∑_e : X,1):=⟨n,by simpa using h⟩
  obtain ⟨⟨e,j⟩,eq⟩:=(DescentOrderedWords.address ord (fun _=>1)).surjective s
  have val:=congrArg Fin.val eq
  change DescentOrderedWords.offset ord (fun _=>1) e+j.val=n at val
  exact ⟨e,by simpa [DescentOrderedWords.offset,Fin.eq_zero j] using val⟩

include fit in
/-- At a public bank pin, the response table and the ordered bank installer
pick the same original cable and the same word within that cable. -/
theorem root_socket_at (v : (Z).bank.Site) (sock : Attached (Z).bank v)
    (left right : Lane p (boundaryWidth (Z).bank v)) (atPin : left.port=.inr sock)
    (xs : Fin (cfg).count→DescentFallbackItemSelect.Item) (read : RootRows B sock.val.1 sock.val.2 xs)
    (depth leaf : ℕ) (ticket : DescentResetLocalRoster.code (cfg).residual×Option (Fin (2^(Z).n)))
    (index : Fin (left.count (fun a=>boundaryWidth (Z).bank v a/p))) :
    let units:=fun a=>boundaryWidth (Z).bank v a/p
    let covered:=laneBlock units ((Z).laneWidth_eq batches p fit v) hp left index
    let word:=left.bundleStart+index.val
    ∃number, ∃printed : PublicSocket B (treeReceiver B v) batches (word%batches) false number,
      (cfg).physicalReply sock.val.1 (A).cap depth [] ticket xs leaf left right index.val=
        some (number,word%batches,left.count units,false) ∧
      deviceRoute B hp v covered=(printed.face.val.1,word%batches) :=by
  intro units covered word
  have unitPos : 0 < (Z).unit := by
    rw [B.unit, ←B.next.grain]
    exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have pos : 0 < batches := Nat.pos_of_mul_pos_right (lt_of_lt_of_eq unitPos fit)
  have port_ : covered.port=.inr sock:=atPin
  have bits : (word+1)*p≤boundaryWidth (Z).bank v (.inr sock):=port_ ▸ covered.fits
  let ord : Fibre ((placement).input sock.val.1) sock.val.2 ↪ _ := portKey sock.val.1 sock.val.2
  have widthEq : boundaryWidth (Z).bank v (.inr sock) =
      Fintype.card (Fibre ((placement).input sock.val.1) sock.val.2) * (Z).unit := by
    change DescentRouterBank.publicWidth (placement).input (fun _ => (Z).unit) sock.val = _
    unfold DescentRouterBank.publicWidth DescentNamedContact.width
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
    let chart : Fintype (Fibre ((placement).input sock.val.1) sock.val.2) := inferInstance
    let native : Fintype (Fibre ((placement).input sock.val.1) sock.val.2) :=
      @Subtype.fintype (old).graph.Edge (fun a => (placement).input sock.val.1 a = sock.val.2)
        (fun a => Classical.propDecidable _) (old).graph.finiteEdge
    exact congrArg (fun x : ℕ => x * (Z).unit) (@Fintype.card_congr _ _ native chart (Equiv.refl _))
  have expanded := (congrArg (fun x : ℕ => Fintype.card (Fibre ((placement).input sock.val.1) sock.val.2) * x) fit).trans (Nat.mul_assoc _ _ _).symm
  have room : word<Fintype.card (Fibre ((placement).input sock.val.1) sock.val.2)*batches :=
    (Nat.mul_le_mul_right_iff hp).mp (bits.trans_eq (widthEq.trans expanded))
  obtain ⟨e,ranked⟩ := @fibre_rank_onto (Fibre ((placement).input sock.val.1) sock.val.2) _ _ ord (word/batches)
    ((Nat.div_lt_iff_lt_mul pos).2 room)
  obtain ⟨j,rankAt,res,signed⟩:=read.row e
  have sameRank (a b : Fintype (Fibre ((placement).input sock.val.1) sock.val.2)) :
      (@DescentOrderedWords.before _ a _ ord e).card = (@DescentOrderedWords.before _ b _ ord e).card := by
    rw [Subsingleton.elim a b]
  let number:=(cfg).stemAt sock.val.1 (A).cap (xs j.val)
  let face : Face (treeReceiver B v):=⟨(stemParent B (sock.val.1,e.val),true),
    by simpa only [stem_one] using Nat.zero_lt_one,stem_at_bank B v sock e⟩
  have sub : word%batches<batches:=Nat.mod_lt _ pos
  let printed : PublicSocket B (treeReceiver B v) batches (word%batches) false number:=
    ⟨face,flat_stem_position B sock.val.1 e.val face rfl rfl (xs j.val) res signed,
      by rw [Nat.div_eq_of_lt sub];exact face.property.1,Or.inr sub⟩
  refine ⟨number,printed,?_,?_⟩
  · have posn : (rankOrder xs (rootRows xs) j).val=word/batches:=
      (rankOrder_val xs _ j).trans (rankAt.trans ((sameRank _ _).trans ranked))
    have hi : word/batches<(rootRows xs).card:=posn ▸ (rankOrder xs (rootRows xs) j).isLt
    have selectedRow : (rankOrder xs (rootRows xs)).symm ⟨word/batches,hi⟩=j:=by
      apply (rankOrder xs _).injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext posn.symm
    simp only [DescentFallbackOperandBranch.Config.physicalReply, ite_eq_left index.isLt, ite_true]
    change (if h : word/batches < (rootRows xs).card then
      some ((cfg).stemAt sock.val.1 (A).cap (xs ((rankOrder xs (rootRows xs)).symm ⟨_,h⟩).val),
        word%batches,left.count units,false) else none) = _
    rw [dite_eq_left hi, selectedRow]
  · have ord_ : covered.block=word:=rfl
    have sameRef : covered=⟨.inr sock,word,bits⟩:=by
      have extRef (a b : BlockRef p (boundaryWidth (Z).bank v)) (h₁ : a.port=b.port) (h₂ : a.block=b.block) : a=b := by
        cases a; cases b; congr
      exact extRef _ _ port_ ord_
    have serial : word=(DescentOrderedWords.before ord e).card*batches+word%batches:=by
      rw [ranked,Nat.mul_comm (word/batches),Nat.div_add_mod]
    rw [sameRef]
    exact root_route_word B hp fit v sock e word _ bits sub
      (serial.trans (congrArg (fun a : ℕ => a*batches + word%batches) (sameRank _ _)))

include fit in
/-- The outgoing native word for the first operand of an actual installed tree
gate is a previous signed stem at this common bank host. -/
theorem tree_root_socket (s : Bool) (t : (Z).Fallback) (e : placementItem s t) (b : Fin batches)
    (xs : Fin (cfg).count→DescentFallbackItemSelect.Item)
    (read : RootRows B s ((placement).input s e.val) xs)
    (right : Lane p (boundaryWidth (Z).bank (loc s t e)))
    (leaf : ℕ) (index : Fin (((Z).rootLane key batches p hp fit s t e b).count
      (fun a=>boundaryWidth (Z).bank (loc s t e) a/p))) :
    let v:=loc s t e
    let left:=(Z).rootLane key batches p hp fit s t e b
    let word:=left.bundleStart+index.val
    let units:=fun a=>boundaryWidth (Z).bank v a/p
    let covered:=laneBlock units ((Z).laneWidth_eq batches p fit v) hp left index
    ∃number, ∃printed : PublicSocket B (treeReceiver B v) batches (word%batches) false number,
      (cfg).physicalReply s (A).cap ((placement).fallbackBook s t).height []
        ((Z).fallLabel T t,((T).code t).2.2) xs leaf left right index.val=
        some (number,word%batches,left.count units,false) ∧
      deviceRoute B hp v covered=(printed.face.val.1,word%batches) :=by
  obtain ⟨sock,port_,source,_,_⟩:=(Z).rootLane_socket key batches p hp fit s t e b
  have data : RootRows B sock.val.1 sock.val.2 xs:=by rw [source];exact read
  have answer:=root_socket_at B hp fit (loc s t e) sock ((Z).rootLane key batches p hp fit s t e b) right
    port_ xs data ((placement).fallbackBook s t).height leaf ((Z).fallLabel T t,((T).code t).2.2) index
  simpa only [source] using answer

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
