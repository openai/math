import OAI.Hierarchy.DescentFullRotorQuery
import OAI.Hierarchy.DescentInstalledRotorHeader
import OAI.Hierarchy.DescentSignedRosterWindows

namespace OAI
/-! # Directed rotor arguments and their native signed receiver addresses -/

namespace Hierarchy.DescentRotorOperandTicket
open DescentPhysicalSplit DescentRotor LinearAlgebra.SpectralBooks Computability.BorderVNP.Crossing
noncomputable section
variable {P : Type} [Fintype P] {D : ℕ} {bits : P→ℕ} (H : Network D P bits)

def endpoint (face : Bool) (e : Cable H) : Vertex H :=
  if face then (graph H).dst e else (graph H).src e

theorem root_face (v : H.Site) :
    endpoint H false (.inr ⟨v,0⟩)=⟨v,.inl false⟩ := rfl

theorem back_face (v : H.Site) (i : Fin (count H v)) :
    endpoint H true (.inr ⟨v,i.castSucc⟩)=⟨v,.inr i⟩ := by
  change (⟨v,Attachment.nextSite i.castSucc⟩ : Vertex H)=_
  simp [Attachment.nextSite]

theorem fore_face (v : H.Site) (i : Fin (count H v)) :
    endpoint H false (.inr ⟨v,i.succ⟩)=⟨v,.inr i⟩ := by
  change (⟨v,Attachment.prevSite i.succ⟩ : Vertex H)=_
  simp [Attachment.prevSite]

theorem path_face (v : H.Site) (i : Fin (count H v)) (j : Fin 2) :
    endpoint H (decide (j=0)) (.inr ⟨v,if j=0 then i.castSucc else i.succ⟩)=⟨v,.inr i⟩ := by
  by_cases h:j=0
  · simpa [h] using back_face H v i
  · simpa [h] using fore_face H v i

theorem supply_face (v : H.Site) (i : Fin (count H v)) (e : H.Edge) (dir : Bool)
    (selected : name H v i=.inr (e,dir)) : endpoint H dir (.inl e)=⟨v,.inr i⟩ := by
  have atTap:=tap_named H v i
  rw [selected] at atTap
  cases dir <;> exact atTap

end
end Hierarchy.DescentRotorOperandTicket

namespace Hierarchy.DescentSixParty.ResetInput
open DescentRotorPrivateFields DescentCommonHost DescentResetTrunks DescentResetAttachments DescentChosenRouter DescentRelativeContacts
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "Q" => DescentCommonPalette.rotor Z.graph

theorem rotor_endpoint (s : Bool) (g : Z.placement.Good) (e : (Q).Edge) (face : Bool) :
    (if face then (W).graph.dst (rotorWireAt Z T s g e) else (W).graph.src (rotorWireAt Z T s g e))=
      rotorSiteAt Z T s g (if face then (Q).dst e else (Q).src e) := by
  have raw:=rotorFields Z T s g e
  cases face
  · exact (Equiv.eq_symm_apply _).2 (congrArg RawFields.src raw)
  · exact (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst raw)

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentRotorOrientedQuery
open DescentFullRotorQuery
open DescentRotorOperandTicket DescentRotorCandidateIssue DescentResetHostSize DescentResetLocalRoster
open DescentSIMDLookup DescentPackedZip DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentPacking.PackedMatch.Local.Gather DescentSharedCableNames
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n h r H G M w field : ℕ} (board : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor board

def stride (Ht r Y oldCap : ℕ) := publicCount Ht r Y oldCap+bound board Ht r Y

theorem directed_bits (short : ℕ) : Packed.bits (2*short)≤Packed.bits short+1 := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  have room:=Nat.le_pow_clog (by decide : 1<2) (short+1)
  change 2*short+1≤2^(Nat.clog 2 (short+1)+1)
  rw [pow_succ]
  omega

def word (Ht packet f m address : ℕ) (s face : Bool) (key : Code r) (e : (Q).Edge) (x : Fin 3→Cell field) :
    Cell (Packed.bits (2*slots board Ht r (2^n) field)) :=
  let L:=stride board Ht r (2^n) (x 0).val
  let q:=query board Ht packet f m address s key e x
  if active : 0<q.val then
    if room : q.val≤L then
      Packed.token (some ⟨(if face then L else 0)+(q.val-1),by
        have size : L≤ slots board Ht r (2^n) field :=
          Nat.add_le_add_right (publicCount_mono _ _ _ (x 0).isLt.le) _
        cases face <;> simp <;> omega⟩)
    else 0
  else 0

theorem word_read (Ht packet f m address : ℕ) (s face : Bool) (key : Code r) (e : (Q).Edge)
    (x : Fin 3→Cell field) (t : ℕ) (ht : t<stride board Ht r (2^n) (x 0).val)
    (hit : (query board Ht packet f m address s key e x).val=t+1) :
    (word board Ht packet f m address s face key e x).val=
      (if face then stride board Ht r (2^n) (x 0).val else 0)+t+1 := by
  simp [word,hit,Nat.succ_le_of_lt ht,Packed.token]

theorem word_zero (Ht packet f m address : ℕ) (s face : Bool) (key : Code r) (e : (Q).Edge)
    (x : Fin 3→Cell field) (absent : query board Ht packet f m address s key e x=0) :
    word board Ht packet f m address s face key e x=0 := by simp [word,absent]

theorem issue (Ht packet f m address : ℕ) (s face : Bool) (key : Code r) (e : (Q).Edge)
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (2*slots board Ht r (2^n) field)) M H G w out.base)
    (rom : resident (word board Ht packet f m address s face key e ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>word board Ht packet f m address s face key e (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (word board Ht packet f m address s face key e) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentRotorOrientedQuery

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
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
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster DescentRotorOperandTicket
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n



theorem rotor_signed_stride :
    DescentRotorOrientedQuery.stride (Z).graph height r sz input.placement.cap=totalLocal B := by
  simp only [DescentRotorOrientedQuery.stride,DescentFullRotorQuery.publicCount,DescentRotorCandidateIssue.bound,
    totalLocal,privateCount,stemsCount,contactCount,B.keyWidth]
  omega

open DescentNextSignedWindow
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding

theorem issued_signed_query {p₀ field : ℕ} (proof : B.Recorded p₀) (u : Host) (s : Bool) (g₀ : (placement).Good)
    (e : (DescentCommonPalette.rotor (Z).graph).Edge) (m : ℕ) (x : Fin 3→DescentSIMDLookup.Cell field)
    (capRead : (x 0).val=input.placement.cap) (chosen : (x 1).val=((Z).goodLabel T g₀).val.1+1 ∧ (x 2).val%2=0)
    (face : Roster.Face A₁ ord₁ (blocks B) u) (isEdge : face.val.1=privateWire B (goodOccurrence B s g₀ e))
    (layer : Fin ((Z).circuit s g₀).layers) (batch : Fin m) :
    (DescentRotorOrientedQuery.word (Z).graph height (Z).width f m (layer.val*m+batch.val) s face.val.2 ((Z).goodLabel T g₀) e x).val=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 := by
  let v:=Roster.resident A₁ ord₁ (blocks B) u face
  have real : v.val=privateWire B (goodOccurrence B s g₀ e):=isEdge
  have active : DescentResetLocalRoster.active (blocks B) u (privateWire B (goodOccurrence B s g₀ e)):=real ▸ v.property
  have same : v=⟨privateWire B (goodOccurrence B s g₀ e),active⟩:=Subtype.ext real
  have lower:=(localRoster B u v).isLt
  have stride : DescentRotorOrientedQuery.stride (Z).graph height r sz (x 0).val=totalLocal B:=by
    rw [capRead,rotor_signed_stride]
  have ticketRead:=issued_local_query B proof u s g₀ e m x capRead chosen active layer batch
  rw [←same] at ticketRead
  rw [DescentRotorOrientedQuery.word_read _ _ _ _ _ _ _ _ _ _ _ _ (stride.symm ▸ lower) ticketRead,stride]
  change _=(finProdFinEquiv ((if face.val.2 then 1 else 0 : Fin 2),localRoster B u v)).val+1
  cases hface : face.val.2 <;> simp [finProdFinEquiv_apply_val,Nat.add_comm]


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
