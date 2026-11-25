import OAI.Hierarchy.DescentResetActorClassRAM
import OAI.Hierarchy.DescentResetActorCalendar
import OAI.Hierarchy.DescentResetActorOperands
import OAI.Hierarchy.DescentResetHubRectangle

namespace OAI
/-! # From the fixed role roster and the attained inverse to the actor at the current checkpoint -/
namespace Hierarchy.DescentResetActorClass
open DescentCommonHost DescentContacts DescentHostDirectory DescentSIMDLookup DescentDenseHostOrder DescentDatedAddressBook.ActorSetup
noncomputable section
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)
open scoped Classical
set_option quotPrecheck false
local notation "Q" => (DescentCommonPalette.rotor board).Site

/-- Dormant rotor termini have no funded nodes. The two public trunk wings distinguish
the endpoint carrying a predecessor from its relay. -/
def classOf {V F : Type} : Node V (V×F) Q→Cell 3
  | .trunk false _=>1
  | .trunk true _=>2
  | .good _ _ ⟨_,.inl false⟩=>3
  | .good _ _ ⟨_,.inl true⟩=>0
  | .good _ _ ⟨_,.inr _⟩=>4
  | .fall _ _ _=>5

def catalogue (oldHosts residual height : ℕ) (r : Fin (oldHosts*(roster board residual height).card)) : Cell 3:=
  classOf board (shapeAt board residual height (finProdFinEquiv.symm r).2)

theorem classOf_shape {V : Type} (v : Node V (V×Endpoint (2^n)) Q) :
    classOf board (shape board v)=classOf board v:=by
  cases v with
  | trunk s name=>cases s <;>rfl
  | good s base cell=>rcases cell with ⟨v,(_|_)|i⟩ <;>rfl
  | fall=>rfl

def indexBits (n r : ℕ) :=Nat.clog 2 (6+2*(2^r*2^n))

def rootIndex (n r : ℕ) (s : Bool) (low : ℕ) (v : Fin (2^n)) : Cell (indexBits n r):=
  let id:=finProdFinEquiv ((finTwoEquiv.symm s,finProdFinEquiv (⟨low%2^r,Nat.mod_lt _ (Nat.two_pow_pos r)⟩,v)) :
    Fin 2×Fin (2^r*2^n))
  ⟨6+id.val,(Nat.add_lt_add_left id.isLt 6).trans_le (Nat.le_pow_clog (by decide) _)⟩

theorem rootIndex_val (n r : ℕ) (s : Bool) (low : ℕ) (v : Fin (2^n)) (fit : low<2^r) :
    (rootIndex n r s low v).val=6+((finTwoEquiv.symm s).val*2^r+low)*2^n+v.val:=by
  simp only [rootIndex,finProdFinEquiv_apply_val,Nat.mod_eq_of_lt fit]
  ring

private theorem low_mem {r : ℕ} (key : ℕ×ℕ) (member : key∈codes r) : key.2<2^r:=by
  induction r with
  | zero=>
    have h : key=(0,0):=by simpa [codes] using member
    simp [h]
  | succ r ih=>
    rcases Finset.mem_union.mp member with old|fresh
    · exact (ih old).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
    · obtain ⟨j,inRange,eq_⟩:=Finset.mem_image.mp fresh
      have val : j=key.2:=congrArg Prod.snd eq_
      exact val ▸ Finset.mem_range.mp inRange

theorem good_label_bound (r height : ℕ) (s : Bool) (low : ℕ) (v : Q)
    (exists_ : Node.good s ((),low) v∈roster board r height) : low<2^r:=by
  obtain ⟨⟨side,u,code,tag⟩,_,hit⟩:=Finset.mem_image.mp exists_
  rcases tag with a|actor|endPt
  · simp [render] at hit
  · let label : Node Unit (Unit×Endpoint (2^n)) Q→ℕ
      | .good _ base _=>base.2
      | _=>0
    have id : code.val.2=low:=congrArg label hit
    exact id ▸ low_mem code.val code.property
  · rcases endPt with ⟨tag,cell⟩
    simp [render] at hit

def indexed {V F : Type} (r : ℕ) : Node V (V×F) Q→Cell (indexBits n r)
  | .trunk false _=>1
  | .trunk true _=>2
  | .good s (_,base) ⟨v,.inl false⟩=>rootIndex n r s base v
  | .good _ _ ⟨_,.inl true⟩=>0
  | .good _ _ ⟨_,.inr _⟩=>4
  | .fall _ _ _=>5

def indexBook (oldHosts r height : ℕ) (key : Fin (oldHosts*(roster board r height).card)) :=
  indexed board r (shapeAt board r height (finProdFinEquiv.symm key).2)

theorem indexBook_cast {n' h' : ℕ} (other : NonlinearExpanders.Graph n' h')
    (dim : n=n') (depth : h=h') (same : HEq board other) (hosts height r r' : ℕ)
    (low : r=r') (size : hosts*(roster board r height).card=hosts*(roster other r' height).card)
    (u : Fin (hosts*(roster board r height).card)) :
    (indexBook other hosts r' height (u.cast size)).val=(indexBook board hosts r height u).val:=by
  subst n';subst h';subst r';cases eq_of_heq same;rfl

theorem indexed_shape {V : Type} (r : ℕ) (v : Node V (V×Endpoint (2^n)) Q) :
    indexed board r (shape board v)=indexed board r v:=by
  cases v with
  | trunk s name =>cases s <;>rfl
  | good s base cell =>rcases base with ⟨u,z⟩;rcases cell with ⟨v,(_|_)|i⟩ <;> rfl
  | fall =>rfl

end
end Hierarchy.DescentResetActorClass

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetAttachments
open DescentDenseHostOrder DescentPackedZip DescentSIMDLookup DescentResetActorClass DescentDatedAddressBook.ActorSetup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "residual" => ((Z).k-(T).commonDepth)
local notation "pool" => DescentDenseHostOrder.roster (Z).graph residual height
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
variable {oldHosts hosts groups lanes bw : ℕ} (previous : Fintype.card input.V≤oldHosts)
local notation "rawRank" => (Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous))
local notation "used" => Fintype.card B.next.V
local notation "measured" => catalogue (Z).graph oldHosts residual height
local notation "atlas" => (⟨oldHosts*(pool).card,hosts,groups,lanes⟩ : DescentResetActorClass.Shape)

theorem native_class_at (v : B.next.V) : measured (rawRank v)=classOf (Z).graph v.val:=by
  change classOf (Z).graph (shapeAt (Z).graph residual height
    (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v))).2)=_
  rw [Equiv.symm_apply_apply]
  have exactShape : shapeAt (Z).graph residual height ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v).2=
      shape (Z).graph v.val:=congrArg Subtype.val ((shapeIndex (Z).graph residual height).symm_apply_apply ((Z).localShape T v))
  rw [exactShape,classOf_shape]

/-- Source and destination racks are the actual sparse physical name and its compact
successor from the paid directory, with padding tested before the indirect lookup. -/
theorem checkpoint_class (base : ℕ) (cnt inv : Bank) (m : Memory bw) (cf : cnt.Fits bw base) (sf : inv.Fits bw base)
    (count : m cnt.base=(used:Word bw))
    (stored : ∀v : B.next.V,m (inv.base+((Z).denseHostRank T ((vertex).trans (Fin.castLEEmb previous)) v).val)=((rawRank v).val:Word bw))
    (size : used ≤ inv.size) (fits : used<2^bw) (hostFits : hosts≤2^bw) (room : (atlas).endAddress base<2^bw) :
    ((atlas).expr base cnt inv).Fits bw ((atlas).endAddress base) ∧
    Source ((atlas).expr base cnt inv) (fun (a : Fin hosts) (_ : Fin groups)=>(paidActorAt B a).elim 0 (fun v=>classOf (Z).graph v.val))
      lanes ((atlas).image base measured m):=by
  let name (j : Fin used):=rawRank ((denseOrder B).symm j)
  have table (j : Fin used) : m (inv.base+j.val)=((name j).val:Word bw):=
    paid_actor_inverse B previous m inv.base stored j
  obtain ⟨good,words⟩:=(atlas).received base measured name cnt inv m cf sf count table size fits hostFits room
  refine ⟨good,?_⟩
  have reality : DescentResetDenseOperand.dense (H:=hosts) name ((atlas).values measured)=
      (fun (a : Fin hosts) (_ : Fin groups)=>(paidActorAt B a).elim 0 (fun v=>classOf (Z).graph v.val)):=by
    funext a g
    by_cases live : a.val<used
    · simpa [DescentResetDenseOperand.dense,paidActorAt,live,name,DescentResetActorClass.Shape.values] using
        native_class_at B previous ((denseOrder B).symm ⟨a.val,live⟩)
    · simp [DescentResetDenseOperand.dense,paidActorAt,live]
  exact reality ▸ words

/-- At a physical good root this same sparse slot returns its complete static selector,
including side, residue and rotor vertex. No additional scan or cohort-wide division. -/
theorem native_index_at (v : B.next.V) :
    indexBook (Z).graph oldHosts residual height (rawRank v)=indexed (Z).graph residual v.val:=by
  change indexed (Z).graph residual (shapeAt (Z).graph residual height
    (finProdFinEquiv.symm (finProdFinEquiv ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v))).2)=_
  rw [Equiv.symm_apply_apply]
  have actual : shapeAt (Z).graph residual height ((Z).hostFields T ((vertex).trans (Fin.castLEEmb previous)) v).2=
      shape (Z).graph v.val:=congrArg Subtype.val ((shapeIndex (Z).graph residual height).symm_apply_apply ((Z).localShape T v))
  rw [actual,indexed_shape]

/-- The fixed table selected by the reset calendar is the very same classifier
at every physical compact-directory key, through the actual graph certificate. -/
theorem calendar_index_at (v : B.next.V) :
    (indexBook ctl.board oldHosts k height ((rawRank v).cast
      (congrArg (oldHosts*·) B.public_hub_slots))).val=(indexed (Z).graph residual v.val).val:=by
  have low : residual=k:=by rw [B.commonDepth,B.keyWidth];omega
  exact (indexBook_cast (Z).graph ctl.board B.dimension rfl B.graph oldHosts height residual k low
    (congrArg (oldHosts*·) B.public_hub_slots) (rawRank v)).trans (congrArg Fin.val (native_index_at B previous v))

theorem checkpoint_index (base : ℕ) (cnt inv : Bank) (m : Memory bw) (cf : cnt.Fits bw base) (sf : inv.Fits bw base)
    (count : m cnt.base=(used:Word bw))
    (stored : ∀v : B.next.V,m (inv.base+((Z).denseHostRank T ((vertex).trans (Fin.castLEEmb previous)) v).val)=((rawRank v).val:Word bw))
    (size : used ≤ inv.size) (fits : used<2^bw) (hostFits : hosts≤2^bw) (room : (atlas).endAddress base<2^bw) :
    ((atlas).expr base cnt inv).Fits bw ((atlas).endAddress base) ∧
    Source ((atlas).expr base cnt inv) (fun (a : Fin hosts) (_ : Fin groups)=>(paidActorAt B a).elim 0 (fun v=>indexed (Z).graph residual v.val))
      lanes ((atlas).image base (indexBook (Z).graph oldHosts residual height) m):=by
  let name (j : Fin used):=rawRank ((denseOrder B).symm j)
  have table (j : Fin used) : m (inv.base+j.val)=((name j).val:Word bw):=
    paid_actor_inverse B previous m inv.base stored j
  obtain ⟨good,words⟩:=(atlas).received base (indexBook (Z).graph oldHosts residual height) name cnt inv m cf sf count table size fits hostFits room
  refine ⟨good,?_⟩
  have reality : DescentResetDenseOperand.dense (H:=hosts) name ((atlas).values (indexBook (Z).graph oldHosts residual height))=
      (fun (a : Fin hosts) (_ : Fin groups)=>(paidActorAt B a).elim 0 (fun v=>indexed (Z).graph residual v.val)):=by
    funext a g
    by_cases live : a.val<used
    · simpa [DescentResetDenseOperand.dense,paidActorAt,live,name,DescentResetActorClass.Shape.values] using
        native_index_at B previous ((denseOrder B).symm ⟨a.val,live⟩)
    · simp [DescentResetDenseOperand.dense,paidActorAt,live]
  exact reality ▸ words


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
