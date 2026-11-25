import OAI.Hierarchy.DescentRetainedResetCablePointer
import OAI.Hierarchy.DescentRegisteredOriginalOperandField
import OAI.Hierarchy.DescentIssuedCarriedIndex

namespace OAI
/-! # Four native retained header digits on the actual normalized cable -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
open DescentBundleHistory DescentKernelHistory DescentRetainedCableBlock DescentPrimitivePalette
open DescentRetainedResetPinPointer DescentResetTrunks DescentOperandPriorIncidence DescentLocalArchiveOrder
open Chronology Computability.BorderVNP.Crossing ThreeFlat.Routing
variable {p R : ℕ}
variable (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "fixed_" => ((Nat.div_mul_cancel whole).symm : (Z).unit=(Z).unit/p*p)
local notation "pre_" => reentryWorldShape split_ Z T birth _ hp fixed_ (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts pre_
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "books_" => closedBooks B hp one pos whole wide a sh
local notation "old_" => W.granular B.count (z*G.b) B.fit
local notation "per_" => (Z).unit/p
local notation "side_" v:max e:max => originFace v e
local notation "unit_" s:max e:max => carriedUnit B s e
local notation "parent_" s:max e:max => carriedParent B s e
local notation "emit_" s:max e:max => emit B (unit_ s e).val.1
local notation "cursor_" s:max e:max low:max => (unit_ s e).val.1.2.val*per_+low


open DescentOperandStateBanks DescentOperandCandidateLookup DescentIssuedFallbackPanel
open DescentSIMDLookup DescentResetOperandComponents DescentDatedAddressBook.ResetOutput
open DescentResetOperandSlices DescentNextSignedWindow.Native
local notation "A" => B.next.placement
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "prior" => input.placement
local notation "before" => input.order.trans Fin.valEmbedding
local notation "oldNames" => DescentPacking.PackedMatch.Local.Stage.cableNames k (groupRank
  ((Function.Embedding.refl (Fin (S.groupCount i))).trans Fin.valEmbedding) (input.vertex.trans Fin.valEmbedding))
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "hOld" v:max => Stage.home (prior) v
local notation "sub" v:max => subcell (c:=(T).commonDepth) digitsIn B.frame.basis (hOld v)
local notation "atSlot" v:max edge:max j:max => Stage.signed (prior) before S input.valid (hOld v).1 (hOld v).2 (originPort (prior) v edge j)
local notation "endOf" edge:max j:max => oldEndOf B (⟨(edge).val,j⟩ : Stage.Grain (prior))
local notation "land" edge:max => (T).home ((old_).graph.dst edge)
local notation "ptr" rank:max pin:max args:max x:max j:max => Reached.argumentPointer B.next next_ rank after_ hp pin args x j
local notation "sourcePtr" num:max pin:max args:max y:max j:max => Reached.argumentPointer input a.bit num sh hp pin args y j

/-- The ticket array is addressed at the old site's original signed donor and slot. -/
theorem original_incoming_slot {v : W.graph.Site} (edge : Incident W.graph v)
    (j : Fin ((prior).grainCount edge.val)) (incoming : side_ v edge=true) :
    incomingIndex B (endOf edge j)=finProdFinEquiv (sub v,atSlot v edge j):=by
  have numbers:=origin_local_address (prior) before S input.valid v (c:=(T).commonDepth)
    digitsIn B.frame.basis edge j
  rw [incoming] at numbers
  unfold incomingIndex
  rw [oldEndOf_read]
  exact congrArg finProdFinEquiv numbers

/-- Decode the actual fallback root bit produced by the named primary control word. -/
theorem original_hub_bit {width : ℕ} (t : (Z).Fallback) (h : Cell width)
    (small : 1<2^width) (published : h=if ((T).code t).2.2.isSome then 0 else 1) :
    decide (h.val=1)=(T).hub t:=by
  have spec:=(T).hubShape t
  have width_pos : 0<width := by
    by_contra! hz
    have h₀ : width=0 := by omega
    simp [h₀] at small
  cases e:((T).code t).2.2 with
  | none=>
    have yes:=(spec.mpr e)
    simp [published,e,yes,width_pos]
  | some i=>
    have no:(T).hub t=false:=by
      cases hh:(T).hub t with
      | false=>rfl
      | true=>have h₀:=spec.mp hh;rw [e] at h₀;contradiction
    simp [published,e,no]

include hp pos whole in
/-- Locate the actual old grain containing the original aligned p-word. -/
def originalCableGrain {v : W.graph.Site} (edge : Incident W.graph v) (chunk : ℕ)
    (full : (chunk+1)*p≤W.graph.width edge.val) : Fin ((prior).grainCount edge.val):=by
  refine ⟨chunk/per_,(Nat.div_lt_iff_lt_mul ?_).mpr ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd pos whole) hp
  · have scale : W.graph.width edge.val=((prior).grainCount edge.val*per_)*p := calc
      W.graph.width edge.val = B.count edge.val*(z*G.b) := B.fit edge.val
      _ = (prior).grainCount edge.val*(Z).unit := congrArg₂ Nat.mul (congrFun B.count_eq edge.val) B.unit.symm
      _ = ((prior).grainCount edge.val*per_)*p :=
        (congrArg ((prior).grainCount edge.val * ·) (Nat.div_mul_cancel whole).symm).trans (Nat.mul_assoc ..).symm
    rw [scale] at full
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right full hp)

/-- The marked bit in the published signed record splits exactly the old cursor of its actual
mother. The quotient reads the true chronological incoming offset, including a source loop. -/
private theorem registered_cursor (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input)
    (units : shape.units=per_) (d₀ : shape.Donor) (slot : shape.Slot) (s : Bool) (grain : (old_).graph.Edge)
    (chunk : ℕ) (head : (shape.header x 3).val=chunk)
    (ticket : s=true→shape.ticket x d₀ slot=earlierIncoming B grain) :
    let c:=shape.oldIndex x d₀ s slot
    (if (grainRecord B (fieldNames B) _ (unit_ s grain)).marked then c%shape.units else c)=
      if parent_ s grain∈(coarse).core then chunk%per_ else cursor_ s grain (chunk%per_):=by
  intro c
  have cursor : c=cursor_ s grain (chunk%per_):=by
    cases s <;> simp [c,DescentResetRetainedCableLaw.Shape.oldIndex,head,units,carriedUnit,ticket]
  have marked : (grainRecord B (fieldNames B) _ (unit_ s grain)).marked = decide ((parent_ s grain)∈(coarse).core) := by
    exact congrArg (@decide ((parent_ s grain)∈(coarse).core)) (Subsingleton.elim _ _)
  rw [marked,cursor,units]
  by_cases paid : (parent_ s grain)∈(coarse).core
  · simp only [paid,decide_true,ite_true,Nat.mul_add_mod_self_right,Nat.mod_mod]
  · simp only [paid,decide_false,Bool.false_eq_true,ite_false]

/-- On an actual retained node each of the four scalar output fields is the normalized
argument pointer's header. Only the four original header digits are read. -/
theorem registered_carried_header (num : Local a.bit) (rank : Local next_) (pin : P→ℕ)
    (oldArgs args : ℕ) (x : NodeOrder.All next_) (y : NodeOrder.All a.bit) (origin : resetOrigin B hp whole a x=.inl y)
    (arg : Fin (((sh.sites y.1).recipe hp).arity y.2)) (edge : Incident W.graph y.1) (chunk : ℕ)
    (full : (chunk+1)*p≤W.graph.width edge.val)
    (was : ((sh.sites y.1).recipe hp).operand y.2 arg=.inl ⟨.inl edge,chunk,full⟩)
    (shape : DescentResetRetainedCableLaw.Shape) (data : shape.Input)
    (degree : shape.degree=(prior).degree) (cap : shape.cap=(prior).cap) (donors : shape.donors=L)
    (units : shape.units=per_) (head : ∀f,(shape.header data f).val=(sourcePtr num pin oldArgs y arg.val).header f)
    (donor : (shape.donorCell data).val=(sub y.1).val+1)
    (rows : ∀j,HEq (shape.row data ((sub y.1).cast donors.symm) j) (DescentSignedCableCodec.encode
      (Stage.signedPanel (prior) before S input.valid oldNames (hOld y.1) (j.cast (congrArg (2*·) cap)))))
    (room : 2*totalLocal B<2^shape.queryBits)
    (ticket : let j:=originalCableGrain B hp pos whole edge chunk full
      side_ y.1 edge=true→shape.ticket data ((sub y.1).cast donors.symm)
        ((atSlot y.1 edge j).cast (congrArg (2*·) cap.symm))=earlierIncoming B (endOf edge j))
    (hub : let j:=originalCableGrain B hp pos whole edge chunk full
      side_ y.1 edge=true→decide ((shape.hubCell data).val=1)=(T).hub (land (endOf edge j)))
    (fieldRoom : shape.units*(A).cap≤2^shape.fieldBits)
    {labelBits H₀ G₀ candidates : ℕ} (earlier : Field→Cell shape.fieldBits) (alias_ : Cell labelBits)
    (oldHeader : ∀f:Fin 4,(earlier (f.castLE (by decide))).val=(sourcePtr num pin oldArgs y arg.val).header f)
    (signed coeff : ℕ) (width : max ((A).degree+1) ((A).cap+1)≤2^signed)
    (count : candidates=totalLocal B) (nativeRoom : 2*candidates<2^shape.queryBits)
    (location : Fin H₀→Fin G₀→Option Host) (query : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (place : location rh rg=some (Stage.home A (hop ((Z).oldOwner T y.1))))
    (issue : code nativeRoom (query rh rg)=shape.query data) (f : Fin 4)
    (fits : (ptr rank pin args x arg.val).header f<2^coeff) :
    let g : Field:=f.castLE (by decide)
    (((DescentResetRetainedPages.kept g (earlier 0) (earlier g) alias_).val+(shape.priceField g data).val:ℕ):Cell coeff).val+
      (selected query (fun j h g₀=>nativeCandidateField signed coeff g
        ((location h g₀).bind (fun v=>candidateRows B (fieldNames B) v (j.cast (congrArg (2*·) count))))) rh rg).val=
      (ptr rank pin args x arg.val).header f:=by
  intro g
  let j:=originalCableGrain B hp pos whole edge chunk full
  let grain:=endOf edge j
  let wing:=Stage.live (prior) before S input.valid oldNames (hOld y.1)
    (DescentTerminalPortChart.first (prior) y.1 edge (Nat.zero_lt_of_lt j.isLt))
  let oldPointer:=Pointer.cable wing.neighbor.val wing.wire.val chunk
  have original : sourcePtr num pin oldArgs y arg.val=oldPointer:=
    Reached.argumentPointer_cable input a.bit num sh hp pin oldArgs y.1 y.2 arg edge chunk full was
  have hd : ∀f,(shape.header data f).val=oldPointer.header f:=by intro f;rw [head,original]
  have positive : 0<shape.units:=by
    rw [units]
    exact Nat.div_pos (Nat.le_of_dvd pos whole) hp
  let earlier₀ : Field→Cell shape.fieldBits:=fun i=>if i.val<4 then earlier i else 0
  let span₀ : Span:=⟨0,0,0⟩
  have old : ∀i,(earlier₀ i).val=oldPointer.fields span₀ i:=by
    intro i
    by_cases live : i.val<4
    · have field : (earlier i).val=oldPointer.header ⟨i.val,live⟩:=
        (oldHeader ⟨i.val,live⟩).trans (congrArg (fun p=>Pointer.header p ⟨i.val,live⟩) original)
      simpa [earlier₀,Pointer.fields,live] using field
    · simp [earlier₀,Pointer.fields,live,span₀]
  have high : chunk/shape.units=j.val:=by rw [units];rfl
  have label : wing.neighbor.val*(prior).cap+wing.wire.val=
      (DescentTerminalPortChart.label (prior) before S input.valid oldNames y.1 edge (Nat.zero_lt_of_lt j.isLt)).val:=by
    change _=wing.wire.val+(prior).cap*wing.neighbor.val
    ac_rfl
  have small:= (carried_index_lt B shape data _ (side_ y.1 edge) _ grain positive ticket).trans_le fieldRoom
  have register:=posted_cable B hp one pos whole wide a sh rank pin args x y origin arg edge chunk full was grain.2 rfl
  let d₀:=(sub y.1).cast donors.symm
  let slot:=(atSlot y.1 edge j).cast (congrArg (2*·) cap.symm)
  have low:=registered_cursor B shape data units d₀ slot (side_ y.1 edge) grain chunk (hd 3) ticket
  let cur:=shape.oldIndex data d₀ (side_ y.1 edge) slot
  let u:=unit_ (side_ y.1 edge) grain
  let child:=Stage.live A (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B) _
      (GrainPorts.port A (B.next.order.trans Fin.valEmbedding) (blocks B) _ u)
  let target:=Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if (grainRecord B (fieldNames B) _ u).marked then cur%shape.units else cur)
  have measured : target=ptr rank pin args x arg.val:=by
    unfold target;rw [low];exact register.symm
  have eqHead : target.fields span₀ g=(ptr rank pin args x arg.val).header f:=by
    rw [measured];simp [Pointer.fields,g,f.isLt]
  have reported:=origin_operand_field B (fieldNames B) oldNames y.1 edge j shape data degree cap donors
    wing.neighbor.val wing.wire.val chunk hd donor rows wing.neighbor.isLt wing.wire.isLt high label room
    positive ticket hub small earlier₀ alias_ span₀ signed coeff old width g count nativeRoom location query rh rg
    place issue (eqHead.trans_lt fits)
  rw [←eqHead]
  simpa only [earlier₀,Fin.val_zero,g,Fin.val_castLE,show 0<4 by decide,f.isLt,ite_true] using reported

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
