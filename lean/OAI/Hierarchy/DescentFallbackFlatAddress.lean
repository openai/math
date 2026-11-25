import OAI.Hierarchy.DescentResetTrunkRelay
import OAI.Hierarchy.DescentFallbackFlatRead
import OAI.Hierarchy.DescentContactReceiver

namespace OAI
/-! # The numeric lookup of the ordered fallback tree names a real signed face -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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
local notation "Face" u => Roster.Face A₁ ord₁ (blocks B) u


open DescentFallbackItemSelect DescentFallbackOperandBranch
def flatConfig (field query lanes batches split nodes args : ℕ) : DescentFallbackOperandBranch.Config :=
  {toShape:=operandShape B field query lanes,oldDegree:=(A).degree,oldCap:=(A).cap,donors:=2^rr,
   fineBits:=k,batches:=batches,split:=split,nodes:=nodes,args:=args}
variable {field query lanes batches split nodes args : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args

def oldOfGrain (e : Grain A) : (old).graph.Edge :=
  (Equiv.sigmaCongrRight fun e=>finCongr (congrFun B.count_eq e)).symm e

@[simp] theorem oldOfGrain_read (e : Grain A) : beforeStem B (oldOfGrain B e)=e :=
  (Equiv.sigmaCongrRight fun e=>finCongr (congrFun B.count_eq e)).apply_symm_apply _

theorem flat_stem_position {u : Host} (s : Bool) (j : (old).graph.Edge) (face : Face u)
    (edge : face.val.1=stemParent B (s,j)) (target : face.val.2=true) (it : Item)
    (res : it.residual=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).1.val)
    (signed : it.signed=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s (beforeStem B j)).2.val) :
    (cfg).stemAt s (A).cap it=(Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  simp only [DescentFallbackOperandBranch.Config.stemAt,flatConfig,fallback_stride,res,signed]
  simpa only [operandShape] using actual_stem_number B s j face edge target

/-- The original item determines its own genuine destination-oriented signed face. -/
def socketFace (s : Bool) (e : Grain A) :
    Face ((blocks B).dst (stemParent B (s,oldOfGrain B e))) :=
  ⟨(stemParent B (s,oldOfGrain B e),true),by simpa only [stem_one] using Nat.zero_lt_one,rfl⟩

theorem observed_socket_address (s : Bool) (e : Grain A) (it : Item)
    (res : it.residual=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s e).1.val)
    (signed : it.signed=(localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis s e).2.val) :
    let where_ := (blocks B).dst (stemParent B (s,oldOfGrain B e))
    (cfg).stemAt s (A).cap it=(Roster.addr A₁ ord₁ (blocks B) where_ (localRoster B where_) (socketFace B s e)).val+1 :=by
  apply flat_stem_position B s (oldOfGrain B e) (socketFace B s e) rfl rfl
  · simpa only [oldOfGrain_read] using res
  · simpa only [oldOfGrain_read] using signed

theorem flat_tree_position {u : Host} (s : Bool) (t : (Z).Fallback)
    (d₀ : Fin ((placement).fallbackBook s t).height)
    (leaf : DescentTreePrefixIntervals.Bits ((placement).fallbackBook s t).height) (face : Face u)
    (edge : face.val.1=privateWire B (fallOccurrence B s t
      ⟨d₀,DescentTreePrefixIntervals.cut (by omega : d₀.val+1≤_) leaf⟩)) :
    (cfg).treeAt s face.val.2 (A).cap ((placement).fallbackBook s t).height d₀.val
      (start height leaf) ((Z).fallLabel T t,((T).code t).2.2)=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  have visible : start height leaf/2^(height-((placement).fallbackBook s t).height)=lex _ leaf :=
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  simp only [DescentFallbackOperandBranch.Config.treeAt,flatConfig,fallback_stride,fallback_stems,fallback_contacts]
  have numbered := actual_tree_number B s t d₀ leaf face edge
  simp only [operandShape,visible] at numbered ⊢
  exact numbered

theorem flat_contact_position {u : Host} (s : Bool) (j) (face : Face u)
    (edge : face.val.1=contactParent B (.inr j)) (faceAt : face.val.2=s) :
    let t:=fallEnd placement s j
    let b:=(placement).fallbackBook s t
    let leaf:=b.codes (fallLeg placement s j)
    (cfg).contactAt s (A).cap b.height (start height leaf) ((Z).fallLabel T t,((T).code t).2.2)=
      (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  let t:=fallEnd placement s j
  let leaf:=((placement).fallbackBook s t).codes (fallLeg placement s j)
  have socket := fallback_contact_socket B s j
  have counted:=actual_contact_number B (.inr j) face edge
  dsimp only at counted ⊢
  rw [faceAt] at counted
  change directed (totalLocal B) s (stemsCount B+1+((finTwoEquiv.symm s).val*
    (rootSlots rr Y*sockets (operandShape B 0 0 0))+(rootId rr Y ((Z).rootTicket T ((placement).owner s (.inr j)))).val*
      sockets (operandShape B 0 0 0)+(DescentContactReceiver.socketId Y height (contactSocket B s (.inr j))).val))=_ at counted
  rw [socket] at counted
  simp only [DescentFallbackOperandBranch.Config.contactAt,flatConfig,fallback_stems,fallback_stride]
  dsimp only [operandShape,sockets] at counted ⊢
  exact counted

/-- The queried public rotor pin on either side names its own reserved contact and socket. -/
theorem flat_rotor_contact_position {u : Host} (s : Bool) (j) (face : Face u)
    (edge : face.val.1=contactParent B (.inl j)) (faceAt : face.val.2=s) :
    let sh:=operandShape B field query lanes
    let rotorKey:=(Z).goodLabel T ((placement).ends s j.1)
    let socket:=((placement).outputName (T).commonDepth s j).2
    directed (total sh (A).cap) s (stemSlots sh (A).cap+1+((finTwoEquiv.symm s).val*
      (rootSlots rr Y*sockets sh)+(rootId rr Y (.inl rotorKey)).val*sockets sh+socket.val))=
        (Roster.addr A₁ ord₁ (blocks B) u (localRoster B u) face).val+1 :=by
  have counted:=actual_contact_number B (.inl j) face edge
  dsimp only at counted ⊢
  rw [faceAt] at counted
  change directed (totalLocal B) s (stemsCount B+1+((finTwoEquiv.symm s).val*
    (rootSlots rr Y*sockets (operandShape B 0 0 0))+(rootId rr Y ((Z).rootTicket T ((placement).owner s (.inl j)))).val*
    sockets (operandShape B 0 0 0)+(DescentContactReceiver.socketId Y height (contactSocket B s (.inl j))).val))=_ at counted
  rw [good_contact_socket B] at counted
  simp only [fallback_stems,fallback_stride]
  dsimp only [operandShape,sockets] at counted ⊢
  exact counted

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
