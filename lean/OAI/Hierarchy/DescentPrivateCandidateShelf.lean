import OAI.Hierarchy.DescentResetTypedSlots
import OAI.Hierarchy.DescentRawPrivateImage
import OAI.Hierarchy.DescentRelativeClassChip
import OAI.Hierarchy.DescentResetPeerThreshold
import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentResetSourceClassRAM

namespace OAI
/-! # Filtering native private cable fields at one receiving site -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
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
local notation "rootDigits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) height
local notation "edgeSrc" => (blocks B).src
local notation "edgeDst" => (blocks B).dst

/-- Only this relative shape digit varies between the private endpoints and the
receiver, once their common block and original vertex are fixed. -/
def relativeShape (u : Host) : ℕ := ((Z).hostFields T vertexCode u.1.2).2.val

/-- One small packed query serves both public and private wires. The public
four-peer table is shared by all groups; only the original donor choice and
the residue of this candidate endpoint vary in a packed lane. -/
theorem actual_relative_class {b : ℕ} (u v : Host) (raw : Fin 5→DescentSIMDLookup.Cell b)
    (donor : ℕ) (peer : Fin (Fintype.card input.V*(pool).card)→Fin 4→Option (Fin (Fintype.card input.V*(pool).card)))
    (eligible : v∈DescentResetWindowResidentSources.sources B.next.placement u)
    (fieldRoom : 4<2^b)
    (roster : DescentSortedRoster.present peer ((Z).rawHostRank T vertexCode u.1.2)=
      (insert u.1.2 (B.next.placement.near u.1.2)).map ((Z).rawHostRank T vertexCode))
    (original : ((Z).hostFields T vertexCode v.1.2).1.val=donor)
    (relative : (raw 4).val=relativeShape B v)
    (digits : ∀j : Fin 4,(raw j.castSucc).val=DescentRelativeClassChip.threshold (pool).card donor
      ((DescentFallbackLeafScan.first peer ((Z).rawHostRank T vertexCode u.1.2) j).map Fin.val)) :
    (DescentRelativeClassChip.rank raw).val=localClass B u v := by
  let name:=(Z).rawHostRank T vertexCode
  have bounded : relativeShape B v<(pool).card:=((Z).hostFields T vertexCode v.1.2).2.isLt
  have code : (name v.1.2).val=relativeShape B v+(pool).card*donor := by
    exact (ResetInput.rawHostRank_read Z T vertexCode v.1.2).trans
      (congrArg (fun j => relativeShape B v+(pool).card*j) original)
  calc
    _=DescentSortedRoster.before peer (name u.1.2) (name v.1.2):=
      DescentRelativeClassChip.rank_read peer _ _ raw _ _ _ (Nat.zero_lt_of_lt bounded)
        bounded code fieldRoom relative digits
    _=_:=(DescentResetSourceClassRAM.local_class name _ _ peer _ roster).trans
      (class_host B u v eligible).symm

/-- Read the sorted peer threshold words issued by the native shared
preparer. The packed lane makes a bounded choice among four original donors. -/
theorem actual_threshold_class {b : ℕ} (u v : Host) (raw : Fin 5→DescentSIMDLookup.Cell b)
    (old : Fin (Fintype.card input.V)→Fin 4→Option (Fin (Fintype.card input.V)))
    (unsorted : Fin (Fintype.card input.V*(pool).card)→Fin 4→Option (Fin (Fintype.card input.V*(pool).card)))
    (d : Fin 4) (eligible : v∈DescentResetWindowResidentSources.sources B.next.placement u)
    (fieldRoom : 4<2^b)
    (roster : DescentSortedRoster.present (DescentSortedRoster.indexed unsorted) ((Z).rawHostRank T vertexCode u.1.2)=
      (insert u.1.2 (B.next.placement.near u.1.2)).map ((Z).rawHostRank T vertexCode))
    (original : DescentResetPeerThreshold.donorAt (pool).card old ((Z).rawHostRank T vertexCode u.1.2) d=
      some (((Z).hostFields T vertexCode v.1.2).1))
    (relative : (raw 4).val=relativeShape B v)
    (read : ∀j : Fin 4,(raw j.castSucc).val=DescentResetPeerThreshold.value (pool).card old
      (DescentSortedRoster.indexed unsorted) ((Z).rawHostRank T vertexCode u.1.2) d j) :
    (DescentRelativeClassChip.rank raw).val=localClass B u v := by
  refine actual_relative_class B u v raw _ _ eligible fieldRoom roster rfl relative ?_
  intro j
  rw [read,DescentResetPeerThreshold.value,original,DescentRelativeClassChip.first_indexed]
  rfl

theorem root_shape_injective {a b : Host} (roots : receiverRoot B a=receiverRoot B b)
    (shape : relativeShape B a=relativeShape B b) : a=b := by
  have coord := congrArg Prod.fst roots
  have blocks := congrArg (rootDigits) (congrArg Prod.snd roots)
  change rootDigits ((rootDigits).symm (a.1.1,a.2))=rootDigits ((rootDigits).symm (b.1.1,b.2)) at blocks
  simp only [Equiv.apply_symm_apply] at blocks
  have node : a.1.2=b.1.2 := ((Z).hostFields T vertexCode).injective
    (Prod.ext (congrArg vertexCode coord) (Fin.ext shape))
  obtain ⟨groupEq, blockEq⟩ := Prod.mk.inj blocks
  exact Prod.ext (Prod.ext groupEq node) blockEq

open DescentPackedPrivateMenu DescentPackedFallbackTree DescentPrivateTreeTemplate
open DescentRotorPrivateFields

/-- Every output digit vanishes at an unoccupied old-vertex/block/ticket. -/
theorem private_empty_root {H count : ℕ} (vertex : (Z).V↪Fin H) (unit : 0<(Z).unit)
    (side : Bool) (ticket : (Z).RootTicket T) (v : Fin H) (block : Block (T).commonDepth)
    (data : (Z).Fallback→Panel height count) (i : ℕ)
    (empty : ∀ g₀,(Z).rootLocation T vertex g₀≠(v,block,ticket)) :
    values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width side i
      ((Z).rootsOf T vertex unit side data ticket v block)=fun _=>0 := by
  have noneHere:=((Z).empty_at T vertex (v,block,ticket)).2 empty
  simp [ResetInput.rootsOf,noneHere,values]

/-- The real rotor table omits every cable slot at or above the selected
device's edge count, independently of its measured depth and multiplicity. -/
theorem private_rotor_pad {count : ℕ} (unit : 0<(Z).unit) (side : Bool) (g₀ : (placement).Good)
    (slot : ℕ) (pad : Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge≤ slot) :
    values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width side slot
      ((Z).rotorKey T unit count side g₀)=fun _=>0 := by
  simp [values,ResetInput.rotorKey,DescentPackedRotorPanel.fields,
    DescentRotorPrivateFields.edgeAt_padding _ _ pad]

/-- The true fallback tree height comes from the packed leaf panel. Padding
below the global height bound cannot create an edge at a shorter selected tree. -/
theorem private_tree_pad {count : ℕ} (side : Bool) (t : (Z).Fallback)
    (data : Panel height count) (slot : ℕ)
    (pad : Fintype.card (DescentPrivateTreeTemplate.Edge ((placement).fallbackBook side t).height)≤ slot) :
    values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width side slot
      ((Z).fallbackKey T side t data)=fun _=>0 := by
  let h₀:=((placement).fallbackBook side t).height
  have fits : h₀<2^(height+2) := ((T).bookHeight side t).trans_lt ((Nat.lt_two_pow_self (n:=height)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have miss : DescentPrivateTreeTemplate.edgeAt h₀ slot=none := by
    exact dite_eq_right (Nat.not_lt.mpr pad)
  have packedDepth : ((DescentSIMDLookup.encode (height+2) (count+1)).symm
      (DescentPackedFallbackTree.pack height h₀ data) 0).val=h₀ := by
    rw [DescentPackedFallbackTree.pack, Equiv.symm_apply_apply, Fin.cons_zero, Fin.val_cast_of_lt fits]
  have inactive : (DescentPackedFallbackTree.localShape (fun _ q=>DescentResetPaletteCode.heap q) slot
      (DescentPackedFallbackTree.pack height h₀ data)).active=0 := by
    unfold DescentPackedFallbackTree.localShape
    dsimp only
    rw [packedDepth]
    simp only [DescentPrivateTreeTemplate.lookup, miss]
  exact ite_eq_left inactive

/-- Reading the installed seven-word physical record ties the packed private
row to its literal incident host codes and the actual grain width. -/
theorem issued_relative (x : PrivateOccurrence B) (row : Fin 5→ℕ)
    (issued : (Z).expand T vertexCode x.1.2 row=(Z).actualRecord T vertexCode (privateWire B x))
    (unit : 0<(Z).unit) :
    row 0=1 ∧ row 1=relativeShape B ((blocks B).src (privateWire B x)) ∧
    row 2=relativeShape B ((blocks B).dst (privateWire B x)) ∧
    row 3=(blocks B).count (privateWire B x) ∧ row 4=1 := by
  let e:=privateWire B x
  have first:=congrFun issued (0 : Fin 7)
  have live : row 0≠0 := by
    intro dead
    simp [ResetInput.expand,ResetInput.actualRecord,dead] at first
  have source:=congrFun issued (1 : Fin 7)
  have target:=congrFun issued (2 : Fin 7)
  have work:=congrFun issued (5 : Fin 7)
  have marked:=congrFun (issued.trans ((Z).record_actual T vertexCode x.1.1 x.1.2 x.2)) (6 : Fin 7)
  have ends:=private_endpoint_roots B x
  simp only [ResetInput.expand,ite_eq_right live,ResetInput.actualRecord] at first source target work
  have relative {u : Host} (v : (coarse).graph.Site) (node : u.1.2=(Z).placed T v)
      (root : receiverRoot B u=((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2))
      {value : ℕ} (read : value+(pool).card*(vertexCode ((Z).rootVertex T x.1.2)).val=
        ((Z).rawHostRank T vertexCode ((Z).placed T v)).val) : value=relativeShape B u := by
    have eqPos:=congrArg Prod.fst root
    change position (Z).graph u.1.2.val=(Z).rootVertex T x.1.2 at eqPos
    rw [←node] at read
    have decoded := (ResetInput.rawHostRank_read Z T vertexCode u.1.2)
    replace read := read.trans decoded
    change value+_=relativeShape B u+(pool).card*(vertexCode (position (Z).graph u.1.2.val)).val at read
    rw [eqPos] at read
    exact Nat.add_right_cancel read
  have hs : ((blocks B).src e).1.2=(Z).placed T ((coarse).graph.src e) :=
    congrArg (fun a : Host=>a.1.2) (named_home B ((coarse).graph.src e))
  have ht : ((blocks B).dst e).1.2=(Z).placed T ((coarse).graph.dst e) :=
    congrArg (fun a : Host=>a.1.2) (named_home B ((coarse).graph.dst e))
  refine ⟨first,relative _ hs ends.1 source,relative _ ht ends.2 target,?_,?_⟩
  · apply Nat.eq_of_mul_eq_mul_left unit
    rw [Nat.mul_comm (Z).unit ((blocks B).count _)]
    exact work.trans (weight_width B e).symm
  · simpa [ResetInput.expand,live,ResetInput.privateRecord] using marked

theorem private_mask_iff (u : Host) (x : PrivateOccurrence B) (row : Fin 5→ℕ)
    (issued : (Z).expand T vertexCode x.1.2 row=(Z).actualRecord T vertexCode (privateWire B x))
    (unit : 0<(Z).unit) (selected : receiverRoot B u=((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2)) :
    (row 0=1 ∧ 0<row 3 ∧ (row 1=relativeShape B u ∨ row 2=relativeShape B u)) ↔
      DescentResetLocalRoster.active (blocks B) u (privateWire B x) := by
  obtain ⟨flag,source,target,amount,_⟩:=issued_relative B x row issued unit
  rw [source,target,amount]
  have endpoints:=private_endpoint_roots B x
  constructor
  · rintro ⟨_,pos,matchSrc|matchDst⟩
    · exact ⟨pos,Or.inl (root_shape_injective B (endpoints.1.trans selected.symm) matchSrc)⟩
    · exact ⟨pos,Or.inr (root_shape_injective B (endpoints.2.trans selected.symm) matchDst)⟩
  · rintro ⟨pos,src|dst⟩
    · exact ⟨flag,pos,Or.inl (congrArg (relativeShape B) src)⟩
    · exact ⟨flag,pos,Or.inr (congrArg (relativeShape B) dst)⟩


/-- It suffices to know the original root address, the side and the local
wire ticket. The actual candidate need not be incident on this receiver. -/
theorem same_private_ticket {a b : PrivateOccurrence B}
    (roots : ((Z).rootVertex T a.1.2,(Z).rootBlock T a.1.2)=((Z).rootVertex T b.1.2,(Z).rootBlock T b.1.2))
    (digits : privateTicket B a=privateTicket B b) : a=b := by
  rcases a with ⟨⟨s₁,g₁⟩,e₁⟩
  rcases b with ⟨⟨s₂,g₂⟩,e₂⟩
  have side : s₁=s₂:=congrArg Prod.fst digits
  have ticket : (Z).rootTicket T g₁=(Z).rootTicket T g₂:=congrArg (fun t=>t.2.1) digits
  have root : g₁=g₂:=((Z).rootLocation T vertexCode).injective
    (Prod.ext (congrArg vertexCode (congrArg Prod.fst roots)) (Prod.ext (congrArg Prod.snd roots) ticket))
  subst s₂
  subst g₂
  have edge : e₁=e₂:=(DescentResetCableSlots.privateWire placement height (T).bookHeight
    (Z).graph (Z).positive (Z).pay (Z).circuit d (s₁,g₁)).injective (congrArg (fun t=>t.2.2) digits)
  cases edge
  rfl

theorem private_selected_origin (u : Host) (p : PrivateOccurrence B)
    (selected : receiverRoot B u=((Z).rootVertex T p.1.2,(Z).rootBlock T p.1.2)) :
    let slot:=DescentResetLocalRoster.localPrivateId _ _ capacity (privateTicket B p)
    localOrigin B u (privateShelfIndex B slot)=
      if live : DescentResetLocalRoster.active (blocks B) u (privateWire B p) then some ⟨privateWire B p,live⟩ else none := by
  intro slot
  split
  next live=>exact (private_shelf_iff B u slot _).2 ⟨p,rfl,rfl⟩
  next no=>
    cases haveSlot : localOrigin B u (privateShelfIndex B slot) with
    | none=>rfl
    | some x=>
      obtain ⟨a,valEq,idEq⟩:=(private_shelf_iff B u slot x).1 haveSlot
      have live : DescentResetLocalRoster.active (blocks B) u (privateWire B a):=by rw [←valEq];exact x.property
      have sameRoot:=(private_owner B u a live.2).symm.trans selected
      have identical:=same_private_ticket B sameRoot ((DescentResetLocalRoster.localPrivateId _ _ capacity).injective idEq)
      exact (no (identical ▸ live)).elim

theorem private_absent_origin (u : Host) (side : Bool) (root : (Z).RootTicket T) (wire : Fin capacity)
    (absent : (Z).atRoot T vertexCode (vertexCode (receiverRoot B u).1,(receiverRoot B u).2,root)=none) :
    localOrigin B u (privateShelfIndex B (DescentResetLocalRoster.localPrivateId _ _ capacity (side,root,wire)))=none := by
  cases found : localOrigin B u (privateShelfIndex B (DescentResetLocalRoster.localPrivateId _ _ capacity (side,root,wire))) with
  | none=>rfl
  | some x=>
    obtain ⟨a,valEq,key⟩:=(private_shelf_iff B u _ x).1 found
    have seen : DescentResetLocalRoster.active (blocks B) u (privateWire B a):=by rw [←valEq];exact x.property
    have home:=(private_owner B u a seen.2).symm
    have ticket:=(DescentResetLocalRoster.localPrivateId _ _ capacity).injective key
    exact ((Z).empty_at T vertexCode _ |>.mp absent a.1.2
      (Prod.ext (congrArg vertexCode (congrArg Prod.fst home))
        (Prod.ext (congrArg Prod.snd home) (congrArg (fun k=>k.2.1) ticket)))).elim

def privateRawAt (v : Fin (Fintype.card input.V)) (block : Block (T).commonDepth)
    (s : Bool) (ticket : (Z).RootTicket T) (slot : Fin capacity) (p : PrivateOccurrence B) : Prop :=
  p.1.1=s ∧ (Z).rootLocation T vertexCode p.1.2=(v,block,ticket) ∧ (privateTicket B p).2.2=slot

private theorem padded_of_missing {E : Type*} [Fintype E] (rank : E↪Fin (Fintype.card E))
    {i : ℕ} (absent : ∀e,(rank e).val≠i) : Fintype.card E≤ i := by
  by_contra! hi
  have all : Function.Bijective rank :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨rank.injective,by simp⟩
  obtain ⟨e,seen⟩:=all.2 ⟨i,hi⟩
  exact absent e (congrArg Fin.val seen)

/-- The very same two original packed lookup receipts supply the private
topology before testing its width. Empty roots and all unused rotor/tree
indices return five zeros; an attained socket returns both true local shapes. -/
theorem private_raw_presence {count : ℕ} (unit : 0<(Z).unit) (s : Bool) (ticket : (Z).RootTicket T)
    (v : Fin (Fintype.card input.V)) (block : Block (T).commonDepth) (slot : Fin capacity)
    (panel : (Z).Fallback→Panel height count) (raw : Fin 5→ℕ)
    (numbers : raw=values (Z).graph ((Z).k-(T).commonDepth) height count (Z).layerBits C (Z).width s slot.val
      ((Z).rootsOf T vertexCode unit s panel ticket v block))
    (installed : ∀p : PrivateOccurrence B, privateRawAt B v block s ticket slot p →
      (Z).expand T vertexCode p.1.2 raw=(Z).actualRecord T vertexCode (privateWire B p)) :
    (raw 0=1 ↔ ∃p,privateRawAt B v block s ticket slot p) ∧
    ((∀p,¬privateRawAt B v block s ticket slot p) → raw=fun _=>0) ∧
    ∀p,privateRawAt B v block s ticket slot p →
      raw 1=relativeShape B ((blocks B).src (privateWire B p)) ∧
      raw 2=relativeShape B ((blocks B).dst (privateWire B p)) := by
  have absent (noneHere : ∀p,¬privateRawAt B v block s ticket slot p) : raw=fun _=>0 := by
    rw [numbers]
    by_cases rooted : ∃g,(Z).rootLocation T vertexCode g=(v,block,ticket)
    · obtain ⟨g,located⟩:=rooted
      have locatedAt : (Z).atRoot T vertexCode (v,block,ticket)=some g:=located ▸ (Z).root_at T vertexCode g
      unfold ResetInput.rootsOf
      rw [locatedAt]
      cases g with
      | inl good=>
        apply private_rotor_pad B unit s good
        apply padded_of_missing (DescentRosterOrder.compact (DescentResetWireTags.rotorWire (Z).graph))
        intro e key
        let equiv := DescentCommonPalette.rotorEdgeEquiv (Z).graph d
          (DescentChosenRouter.selectedRotorLayers placement (Z).graph (Z).positive (Z).pay (Z).circuit s good) C (Z).width (Z).unit
        apply noneHere ⟨(s,.inl good),equiv e⟩
        refine ⟨rfl, located, Fin.ext ?_⟩
        change ((DescentRosterOrder.compact (DescentResetWireTags.rotorWire (Z).graph)) (equiv.symm (equiv e))).val=slot.val
        rwa [Equiv.symm_apply_apply]
      | inr term=>
        apply private_tree_pad B s term (panel term)
        apply padded_of_missing (DescentRosterOrder.compact (DescentResetWireTags.treeWire ((placement).fallbackBook s term).height))
        intro e key
        exact noneHere ⟨(s,.inr term),e⟩ ⟨rfl,located,Fin.ext key⟩
    · exact private_empty_root B vertexCode unit s ticket v block panel slot.val (fun g h=>rooted ⟨g,h⟩)
  have reads (p) (hit : privateRawAt B v block s ticket slot p):=issued_relative B p raw (installed p hit) unit
  refine ⟨⟨?_,?_⟩,absent,fun p hit=>⟨(reads p hit).2.1,(reads p hit).2.2.1⟩⟩
  · intro occupied
    by_contra! no
    rw [absent no] at occupied
    contradiction
  · rintro ⟨p,hit⟩
    exact (reads p hit).1

theorem private_visible {b : ℕ} (u : Host) (x : PrivateOccurrence B)
    (row : Fin 5→ℕ) (raw : Fin 9→DescentSIMDLookup.Cell b)
    (issued : (Z).expand T vertexCode x.1.2 row=(Z).actualRecord T vertexCode (privateWire B x))
    (unit : 0<(Z).unit) (selected : receiverRoot B u=((Z).rootVertex T x.1.2,(Z).rootBlock T x.1.2))
    (flag : (raw 0).val=row 0) (source : (raw 1).val=row 1) (target : (raw 2).val=row 2)
    (here : (raw 3).val=relativeShape B u) (units : (raw 8).val=row 3) :
    DescentCandidateMaskRAM.visible raw ↔ DescentResetLocalRoster.active (blocks B) u (privateWire B x) := by
  have mark:=(issued_relative B x row issued unit).1
  have test:=private_mask_iff B u x row issued unit selected
  simpa [DescentCandidateMaskRAM.visible,flag,source,target,here,units,mark] using test

/-- A positive local row returns precisely the canonical seven fields at the
short private slot, including the earlier receiver's three relative ranks. -/
theorem private_at_slot {b : ℕ} (u : Host) (x : PrivateOccurrence B)
    (live : DescentResetLocalRoster.active (blocks B) u (privateWire B x))
    (raw : Fin 9→DescentSIMDLookup.Cell b) (present : DescentCandidateMaskRAM.visible raw)
    (src : (raw 4).val=localClass B u ((blocks B).src (privateWire B x)))
    (dst : (raw 5).val=localClass B u ((blocks B).dst (privateWire B x)))
    (self : (raw 6).val=localClass B u u)
    (missing : ((raw 7).val≠0) ↔ u∉Stage.near B.next.placement u)
    (mass : (raw 8).val=(blocks B).count (privateWire B x)) :
    let j:=localRoster B u ⟨privateWire B x,live⟩
    DescentCandidateMaskRAM.render raw=DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u j)) := by
  intro j
  have selected:=((local_read B u j ⟨privateWire B x,live⟩).2 rfl)
  have marked:=congrFun ((Z).record_actual T vertexCode x.1.1 x.1.2 x.2) (6 : Fin 7)
  change (if privateWire B x∈(coarse).core then 1 else 0)=1 at marked
  have core : privateWire B x∈(coarse).core := by
    by_contra no
    simp [no] at marked
  simp only [DescentCandidateMaskRAM.render,ite_eq_left present,selected,«meta»,src,dst,self,mass,
    propext missing,decide_eq_true core]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
