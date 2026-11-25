import OAI.Hierarchy.DescentFallbackOperandQuery
import OAI.Hierarchy.DescentRotorOrientedQuery

namespace OAI
/-! # Operand words at the actual receiver of each reset fallback wire -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open DescentFallbackOperandQuery DescentNextSignedWindow DescentResetWireTags DescentTreePrefixIntervals
open scoped Classical Fin.CommRing
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



local notation "old" => W.granular B.count (z*G.b) B.fit
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
local notation "Face" u => Roster.Face A₁ ord₁ (blocks B) u

def operandShape (field out lanes : ℕ) : DescentFallbackOperandQuery.Shape :=
  ⟨rr,Y,height,capacity,field,out,lanes⟩

theorem fallback_stems {field out lanes : ℕ} :
    stemSlots (operandShape B field out lanes) (A).cap=stemsCount B := by
  simp only [stemSlots,operandShape,stemsCount,B.keyWidth]
theorem fallback_stride {field out lanes : ℕ} :
    total (operandShape B field out lanes) (A).cap=totalLocal B := by
  rw [total, fallback_stems]
  rfl

theorem fallback_contacts {field out lanes : ℕ} :
    contactSlots (operandShape B field out lanes)=contactCount B :=rfl

theorem directed_addr {u : Host} (f₀ : Face u) :
    directed (totalLocal B) f₀.val.2
      ((localRoster B u) (Roster.resident A₁ ord₁ (blocks B) u f₀)).val =
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) f₀).val+1 := by
  change directed (totalLocal B) f₀.val.2 _ =
    (finProdFinEquiv ((if f₀.val.2 then 1 else 0 : Fin 2),
      localRoster B u (Roster.resident A₁ ord₁ (blocks B) u f₀))).val+1
  cases side : f₀.val.2 <;> simp [directed,finProdFinEquiv_apply_val,Nat.add_comm]

def fallOccurrence (s : Bool) (t : (Z).Fallback)
    (e : DescentPrivateTreeTemplate.Edge ((placement).fallbackBook s t).height) : PrivateOccurrence B :=
  ⟨(s,.inr t),e⟩

theorem fall_slot (s : Bool) (t : (Z).Fallback)
    (e : DescentPrivateTreeTemplate.Edge ((placement).fallbackBook s t).height) :
    (privateTicket B (fallOccurrence B s t e)).2.2.val =
      (DescentPrivateTreeTemplate.order _ e).val := rfl

/-- The inputs are the preceding old cap, terminal label and original item's leaf.
    The current gate rank is evaluated by the finite public tree dictionary. -/
theorem tree_operand_read {field out lanes : ℕ} (u : Host) (s : Bool) (t : (Z).Fallback)
    (d₀ : Fin ((placement).fallbackBook s t).height)
    (leaf : DescentTreePrefixIntervals.Bits ((placement).fallbackBook s t).height) (f₀ : Face u)
    (edge : f₀.val.1=privateWire B (fallOccurrence B s t
      ⟨d₀,DescentTreePrefixIntervals.cut (by omega : d₀.val+1≤_) leaf⟩))
    (x : Fin 7→Cell field) (present : (x 0).val≠0) (cap : (x 1).val=(A).cap)
    (depth : (x 2).val=((Z).fallLabel T t).val.1) (offset : (x 3).val=((Z).fallLabel T t).val.2)
    (tag : (x 4).val=optionRow ((T).code t).2.2+1) (path : (x 5).val=lex _ leaf) :
    number (operandShape B field out lanes) (.tree s f₀.val.2 ((placement).fallbackBook s t).height d₀.val) x =
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) f₀).val+1 := by
  let p:=fallOccurrence B s t ⟨d₀,DescentTreePrefixIntervals.cut (by omega : d₀.val+1≤_) leaf⟩
  let v:=Roster.resident A₁ ord₁ (blocks B) u f₀
  have active : DescentResetLocalRoster.active (blocks B) u (privateWire B p):=edge ▸ v.property
  have same : v=⟨privateWire B p,active⟩:=Subtype.ext edge
  have code:=private_number B u p active
  rw [←same,localPrivateId_val] at code
  rw [←directed_addr B]
  change _=directed _ _ (localRoster B u v).val
  rw [code]
  simp only [DescentFallbackOperandQuery.number,ite_eq_right present,cap,depth,offset,tag,path]
  rw [fallback_stride,fallback_stems,fallback_contacts]
  dsimp only [operandShape]
  rw [fallback_root ((Z).fallLabel T t) ((T).code t).2.2,pathRank_read]
  rfl

/-- Both the false and the true old stem are received at the bank endpoint. -/
theorem stem_operand_read {field out lanes : ℕ} (u : Host) (s : Bool) (j : (old).graph.Edge) (f₀ : Face u)
    (edge : f₀.val.1=stemParent B (s,j)) (target : f₀.val.2=true)
    (x : Fin 7→Cell field) (present : (x 0).val≠0) (cap : (x 1).val=(A).cap)
    (lo : (x 2).val=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).1.val)
    (slot : (x 3).val=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).2.val) :
    number (operandShape B field out lanes) (.stem s) x =
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) f₀).val+1 := by
  let v:=Roster.resident A₁ ord₁ (blocks B) u f₀
  have active : DescentResetLocalRoster.active (blocks B) u (stemParent B (s,j)):=edge ▸ v.property
  have same : v=⟨stemParent B (s,j),active⟩:=Subtype.ext edge
  have code:=stem_number B u s j active
  rw [←same] at code
  rw [←directed_addr B]
  change _=directed _ f₀.val.2 (localRoster B u v).val
  rw [code,target]
  simp only [DescentFallbackOperandQuery.number,ite_eq_right present,cap,lo,slot]
  rw [fallback_stride]
  congr 1
  simp only [operandShape,finProdFinEquiv_apply_val,B.keyWidth]
  ac_rfl

private theorem packed_contact_digit {u : Host} (j : (placement).Contact)
    (incident : DescentResetLocalRoster.active (blocks B) u (contactParent B j)) :
    let s := contactSide B ⟨j,incident.2⟩
    let root := rootId rr Y ((Z).rootTicket T ((placement).owner s j))
    let port := DescentResetCableSlots.sum (Function.Embedding.refl (Fin Y))
      (Function.Embedding.refl (Fin (2^height))) (contactSocket B s j)
    (contactDigit B u ⟨j,incident⟩).val =
      (finTwoEquiv.symm s).val*(rootSlots rr Y*(Y+2^height)) + root.val*(Y+2^height)+port.val := by
  dsimp only
  let side := contactSide B ⟨j,incident.2⟩
  let root := rootId rr Y ((Z).rootTicket T ((placement).owner side j))
  let port := DescentResetCableSlots.sum (Function.Embedding.refl (Fin Y))
    (Function.Embedding.refl (Fin (2^height))) (contactSocket B side j)
  change (finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv (root,port))).val=_
  simp only [finProdFinEquiv_apply_val]
  dsimp only [root,port,side]
  ac_rfl

private theorem socket_value {a b : ℕ} (z : Fin a ⊕ Fin b) :
    (DescentResetCableSlots.sum (Function.Embedding.refl (Fin a))
        (Function.Embedding.refl (Fin b)) z).val = (finSumFinEquiv z).val := by
  cases z <;> rfl

/-- Socket numbering uses the owner selected by the true contact chart.  Both
    orientations of a loop consequently have the same underlying unsigned number. -/
theorem contact_operand_read {field out lanes : ℕ} (u : Host) (j : (placement).Contact) (f₀ : Face u)
    (edge : f₀.val.1=contactParent B j)
    (x : Fin 7→Cell field) (present : (x 0).val≠0) (cap : (x 1).val=(A).cap)
    (incident : DescentResetLocalRoster.active (blocks B) u (contactParent B j))
    (side : (x 6).val%2=(finTwoEquiv.symm (contactSide B ⟨j,incident.2⟩)).val)
    (root : rootNumber rr Y (x 2).val (x 3).val (x 4).val =
      (rootId rr Y ((Z).rootTicket T ((placement).owner (contactSide B ⟨j,incident.2⟩) j))).val)
    (socket : (x 5).val=(finSumFinEquiv (contactSocket B (contactSide B ⟨j,incident.2⟩) j)).val) :
    number (operandShape B field out lanes) (.contact f₀.val.2) x =
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) f₀).val+1 := by
  let v:=Roster.resident A₁ ord₁ (blocks B) u f₀
  have same : v=⟨contactParent B j,incident⟩:=Subtype.ext edge
  have code:=contact_number B u j incident
  rw [←same] at code
  rw [←directed_addr B]
  change _=directed _ _ (localRoster B u v).val
  rw [code]
  simp only [DescentFallbackOperandQuery.number,ite_eq_right present,cap,side,socket]
  rw [fallback_stride,fallback_stems,packed_contact_digit B j incident]
  dsimp only [operandShape,sockets]
  rw [root,socket_value]

theorem actual_tree_number {u : Host} (s : Bool) (t : (Z).Fallback)
    (d₀ : Fin ((placement).fallbackBook s t).height)
    (leaf : DescentTreePrefixIntervals.Bits ((placement).fallbackBook s t).height) (face : Face u)
    (edge : face.val.1=privateWire B (fallOccurrence B s t
      ⟨d₀,DescentTreePrefixIntervals.cut (by omega : d₀.val+1≤_) leaf⟩)) :
    let plan:=operandShape B 0 0 0
    let root:=(rootId rr Y (.inr ((Z).fallLabel T t,((T).code t).2.2))).val
    let id:=pathRank ((placement).fallbackBook s t).height d₀.val (lex _ leaf)
    directed (totalLocal B) face.val.2 (stemsCount B+1+contactCount B+
      ((finTwoEquiv.symm s).val*(rootSlots rr Y*plan.privateSlots)+root*plan.privateSlots+id))=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  let p:=fallOccurrence B s t ⟨d₀,DescentTreePrefixIntervals.cut (by omega : d₀.val+1≤_) leaf⟩
  let v:=Roster.resident A₁ ord₁ (blocks B) u face
  have active : DescentResetLocalRoster.active (blocks B) u (privateWire B p):=edge ▸ v.property
  have same : v=⟨privateWire B p,active⟩:=Subtype.ext edge
  have read:=private_number B u p active
  rw [←same,localPrivateId_val] at read
  rw [←directed_addr B]
  change _=directed _ _ (localRoster B u v).val
  rw [read]
  simp only [pathRank_read]
  rfl

theorem actual_stem_number {u : Host} (s : Bool) (j : (old).graph.Edge) (face : Face u)
    (edge : face.val.1=stemParent B (s,j)) (target : face.val.2=true) :
    let loc:=localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)
    directed (totalLocal B) true ((finTwoEquiv.symm s).val*(2^rr*(2*(A).cap))+
      loc.1.val*(2*(A).cap)+loc.2.val)=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  let v:=Roster.resident A₁ ord₁ (blocks B) u face
  have active : DescentResetLocalRoster.active (blocks B) u (stemParent B (s,j)):=edge ▸ v.property
  have same : v=⟨stemParent B (s,j),active⟩:=Subtype.ext edge
  have read:=stem_number B u s j active
  rw [←same] at read
  rw [←directed_addr B]
  change _=directed _ _ (localRoster B u v).val
  rw [read,target]
  congr 1
  simp only [finProdFinEquiv_apply_val,B.keyWidth]
  ac_rfl

/-- The two bank endpoints of every direct contact occupy opposite labeled rows. -/
private def bankSide {V U J : Type} : DescentCommonHost.Node V U J→Bool
  | .trunk s _=>s
  | .good s _ _=>s
  | .fall s _ _=>s

private theorem side_at_bank (s : Bool) (root : (placement).Site) (node : (dev (sel s root)).Site) :
    bankSide (((Z).placed T ((Z).privateSiteAt T s root node)).val)=s :=by
  change bankSide ((Z).commonName T ((Z).privateSiteAt T s root node))=s
  have siteName : (Z).commonName T ((Z).privateSiteAt T s root node) =
      bankNode (placement) (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d ⟨(s,root),node⟩ :=
    congrArg (rawName (placement) (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d)
      (((Z).resetNames T).apply_symm_apply (.inr ⟨(s,root),node⟩))
  rw [siteName]
  cases root <;> rfl

theorem contact_polarity (j : (placement).Contact) (s : Bool) :
    let e:=contactParent B j
    bankSide ((if s then (blocks B).dst e else (blocks B).src e).1.2.val)=s :=by
  let e:=contactParent B j
  let same:=funext (fun a=>((Z).allWidths a).symm)
  have readFields:=sourceFields_read _ (T).home (placement).input (T).hub same (Z).bank (Z).tables e
  have key : installedWireNames _ (T).home (placement).input (T).hub same (Z).bank (Z).tables e=
      .inr (.inr (.inl j)):=Equiv.apply_symm_apply _ _
  rw [key] at readFields
  cases s
  · let n:=((Z).bank.src (.inl j)).2
    have actual : (coarse).graph.src e=(Z).privateSiteAt T false ((placement).owner false j) n :=
      (Equiv.eq_symm_apply _).2 (congrArg RawFields.src readFields)
    apply (congrArg (fun st : Host => bankSide st.1.2.val) (named_home B ((coarse).graph.src e))).trans
    change bankSide (((Z).placed T ((coarse).graph.src e)).val) = false
    rw [actual]
    exact side_at_bank B _ _ _
  · let n:=((Z).bank.dst (.inl j)).2
    have actual : (coarse).graph.dst e=(Z).privateSiteAt T true ((placement).owner true j) n :=
      (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst readFields)
    apply (congrArg (fun st : Host => bankSide st.1.2.val) (named_home B ((coarse).graph.dst e))).trans
    change bankSide (((Z).placed T ((coarse).graph.dst e)).val) = true
    rw [actual]
    exact side_at_bank B _ _ _

theorem contact_no_loop (j : (placement).Contact) :
    (blocks B).src (contactParent B j)≠(blocks B).dst (contactParent B j) :=by
  intro eqn
  have l : bankSide (((blocks B).src (contactParent B j)).1.2.val)=false:=contact_polarity B j false
  have r : bankSide (((blocks B).dst (contactParent B j)).1.2.val)=true:=contact_polarity B j true
  rw [eqn,r] at l
  contradiction

/-- Consequently the installed contact uses the queried face's own root and socket,
including on the right bank. -/
theorem contact_side_face {u : Host} (j : (placement).Contact) (face : Face u)
    (edge : face.val.1=contactParent B j)
    (incident : DescentResetLocalRoster.active (blocks B) u (contactParent B j)) :
    contactSide B ⟨j,incident.2⟩=face.val.2 :=by
  have endAt:=face.property.2
  rw [edge] at endAt
  change decide ((blocks B).src (contactParent B j)≠u)=_
  cases dir:face.val.2
  · simp [dir] at endAt
    simp [endAt]
  · simp [dir] at endAt
    exact decide_eq_true (fun eqn=>(contact_no_loop B j) (eqn.trans endAt.symm))

theorem actual_contact_number {u : Host} (j : (placement).Contact) (face : Face u)
    (edge : face.val.1=contactParent B j) :
    let s:=face.val.2
    let plan:=operandShape B 0 0 0
    let root:=rootId rr Y ((Z).rootTicket T ((placement).owner s j))
    let port:=DescentResetCableSlots.sum (Function.Embedding.refl (Fin Y))
      (Function.Embedding.refl (Fin (2^height))) (contactSocket B s j)
    directed (totalLocal B) s (stemsCount B+1+
      ((finTwoEquiv.symm s).val*(rootSlots rr Y*sockets plan)+root.val*sockets plan+port.val))=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  let v:=Roster.resident A₁ ord₁ (blocks B) u face
  have incident : DescentResetLocalRoster.active (blocks B) u (contactParent B j):=edge ▸ v.property
  have same : v=⟨contactParent B j,incident⟩:=Subtype.ext edge
  have reads:=contact_number B u j incident
  rw [←same] at reads
  rw [←directed_addr B]
  change _=directed _ _ (localRoster B u v).val
  rw [reads]
  have dir:=contact_side_face B j face edge incident
  rw [packed_contact_digit B j incident,dir]
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
