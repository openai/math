import OAI.Hierarchy.DescentResetStemClosedWindow
import OAI.Hierarchy.DescentScalarBookReshape
import OAI.Hierarchy.DescentOperandStemSlot

namespace OAI
/-! # Projecting genuine old reset-window keys to each new group and block -/
namespace Hierarchy.DescentResetStemProjectIndex
open DescentSIMDLookup DescentPackedZip DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section

variable {H G X N Q b M w : ℕ}

def index (size : N=G*X) (g : Fin G) (x : Fin X) : Fin N :=
  Fin.cast size.symm (finProdFinEquiv (g,x))

theorem index_val (size : N=G*X) (g : Fin G) (x : Fin X) :
    (index size g x).val=g.val*X+x.val := by
  change x.val+X*g.val=g.val*X+x.val
  ac_rfl

/-- The linearized high index has its old group first and its new block second. -/
def slice (size : N=G*X) (keys : Fin H→Fin N→Cell b) (x : Fin X) (v : Fin H) (g : Fin G) : Cell b :=
  keys v (index size g x)

def flat (size : N=G*X) (keys : Fin Q→Fin H→Fin N→Cell b) (q : Fin Q) (v : Fin H)
    (j : Fin (G*X)) : Cell b := keys q v (Fin.cast size.symm j)

theorem book_slice (size : N=G*X) (keys : Fin Q→Fin H→Fin N→Cell b) (q : Fin Q)
    (x : Fin X) (v : Fin H) (g : Fin G) :
    DescentScalarBookReshape.book (flat size keys) x (finProdFinEquiv (v,q)) g=
      slice size (keys q) x v g := by
  simp only [DescentScalarBookReshape.book,Equiv.symm_apply_apply,flat,slice,index]

theorem flat_read (size : N=G*X) (keys : Fin Q→Fin H→Fin N→Cell b) (q : Fin Q)
    (bank : Bank) (m : Memory w) (read : Reads bank (keys q) (M*X) m) :
    Reads bank (flat size keys q) (M*X) m := by
  subst N
  exact read

/-- A producer may supply the original window as an evaluated expression. Recasting
its group cardinality leaves its native packed-row data and row addresses unchanged. -/
theorem flat_source (size : N=G*X) (keys : Fin Q→Fin H→Fin N→Cell b) (q : Fin Q)
    (e : Expr) (m : Memory w) (observed : Source e (keys q) M m) :
    Source e (flat size keys q) M m := by
  subst N
  exact observed

/-- After the overlap stage chooses pitch `M*X`, existing words are already the
nested encoding that the scalar projector consumes. The final partial row is padded. -/
theorem grouped (size : N=G*X) (keys : Fin Q→Fin H→Fin N→Cell b) (q : Fin Q)
    (old : Bank) (m : Memory w) (hm : 0<M) (hx : 0<X)
    (read : Reads old (keys q) (M*X) m) :
    Reads old (fun v g=>encode b X (fun x=>slice size (keys q) x v g)) M m := by
  exact regroup_read hm hx old.base m (flat size keys q) (flat_read size keys q old m read)

/-- Signed low-window ticket number. It is independent of which new high-group
block is reading the old window. -/
def candidate (radix cap : ℕ) (s : Bool) (lo : Fin radix) (z : Fin (2*cap)) : Fin (2*(radix*(2*cap))) :=
  finProdFinEquiv (finTwoEquiv.symm s,finProdFinEquiv (lo,z))

theorem candidate_read {r cap t : ℕ} (s : Bool) (lo : Fin r) (slot : Fin (2*cap)) (v : Cell t)
    (read : v.val=slot.val+1) :
    (DescentOperandStemSlot.reshaped r cap s lo v).val=(candidate r cap s lo slot).val+1 :=
  DescentOperandStemSlot.reshape_at r cap s lo slot v read

def side {r cap : ℕ} (q : Fin (2*(r*(2*cap)))) : Bool := finTwoEquiv (finProdFinEquiv.symm q).1
def oldSlot {r cap : ℕ} (q : Fin (2*(r*(2*cap)))) : Fin r×Fin (2*cap) :=
  finProdFinEquiv.symm (finProdFinEquiv.symm q).2

@[simp] theorem side_candidate {r cap : ℕ} (s : Bool) (lo : Fin r) (z : Fin (2*cap)) :
    side (candidate r cap s lo z)=s := by simp [side,candidate]

@[simp] theorem oldSlot_candidate {r cap : ℕ} (s : Bool) (lo : Fin r) (z : Fin (2*cap)) :
    oldSlot (candidate r cap s lo z)=(lo,z) := by simp [oldSlot,candidate]

end
end Hierarchy.DescentResetStemProjectIndex

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
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


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "R" => blocks B
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "shapeId" => (Z).codeHost T vertexCode
local notation "lab" => DescentRelativeContacts.shortName c
local notation "End" => (old).graph.Edge

local notation "center" => receiverRoot B
local notation "actor" => fun u => B.frame.host.symm (center u).1
local notation "rack" => fun u => (center u).2
local notation "site" s j => endSite A s (beforeStem B j)

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-c
local notation "use" => useRotor placement.b placement.depth placement.L placement.keys placement.hub placement.old
local notation "label" s j => lab ((T).code ((T).home (ends (old).graph s j)))


open DescentGroupPeerOrder DescentGL DescentTreePrefixIntervals DescentPacking.PackedMatch.Local.Stage
open DescentSharedBookScan
local notation "OldHost" => Stage.Host (Fin (S.groupCount i)) input.V k
local notation "beforeRank" => input.vertex.trans Fin.valEmbedding
local notation "groupKey" => Fin.valEmbedding (n:=S.groupCount i)
local notation "here" => donor digitsIn B.frame.basis fits
local notation "oldNames" => cableNames k (groupRank groupKey beforeRank)
local notation "oldRoster" => hostRoster A beforeRank
local notation "signs" => signedPanel A before S input.valid oldNames

open DescentResetStemProjectIndex DescentPackedZip DescentPackedColony DescentFallbackPeriod
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

theorem stem_project_size : 2^c=groups*(2^k) := by
  rw [B.commonDepth,S.group_cut B.age,pow_add,S.group_power ctl.base ctl.radix]

/-- The physical division used by the projector reconstructs the exact original
high coordinate for every real receiver. No ordering choice about its host is made. -/
theorem stem_project_rack (u : Host) : index (stem_project_size B) u.1.1 u.2=(receiverRoot B u).2 := by
  apply Fin.ext
  rfl

theorem stem_projected_key_at {H Q b : ℕ} (keys : Fin Q→Fin H→Block c→Cell b)
    (j : Fin Q) (u : Host) (actorId : input.V↪Fin H) :
    flat (stem_project_size B) keys j (actorId (actor u)) (finProdFinEquiv (u.1.1,u.2))=
      keys j (actorId (actor u)) (rack u) := by
  change keys j _ (index (stem_project_size B) u.1.1 u.2)=_
  rw [stem_project_rack]

local notation "L" => 2^(m-c)
variable {field : ℕ}
local notation "parse" => DescentResetStemKey.parse (A).degree (A).cap field

variable (value : Stage.Host (Fin (S.groupCount i)) input.V k→ℕ)
    (room : ∀u,value u+1<2^field) (signBits : DescentSignedCableCodec.width input.placement.degree input.placement.cap≤field)
    (onWire : ∀s (e : Grain input.placement),value (home input.placement (endSite input.placement s e))=signedStemWord B s (home input.placement (endSite input.placement s e)))

include room signBits onWire in
theorem stem_projected_window_source {H t M wordBits Q : ℕ} (actorId : input.V↪Fin H)
    (values : Fin H→Block c→Fin L→Cell t) (roster : Fin H→Fin (A).degree→Option (Fin H))
    (chips : Fin H→Block c→Fin L→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (own : ∀v b lo,(values (actorId v) b lo).val=value (here v b lo))
    (chart : ∀v j,roster (actorId v) j=(oldRoster v j).map actorId)
    (raw : ∀v b lo z,chips (actorId v) b lo z=signs (here v b lo) z)
    (ports : DescentPackedColony.Ports (A).degree) (bank : DescentFallbackPeriod.Projected.Column L (A).cap→Bank) (base : ℕ) (mem : Memory wordBits)
    (banks : ∀a,(bank a).Fits wordBits base) (span : ∀a,H*chunks (2^c) M≤(bank a).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H (2^c) M wordBits base)
    (neighbors : Mounted ports roster mem (2^c) M)
    (localWords : ∀lo,Reads (bank (.inl (0,lo))) (fun v b=>((values v b lo).val:Cell field)) M mem)
    (tagged : ∀lo,Reads (bank (.inl (1,lo))) (fun v b=>((values v b lo).val+1:Cell field)) M mem)
    (signed : ∀z lo,Reads (bank (.inr (z,lo)))
      (fun v b=>((DescentSignedCableCodec.encode (chips v b lo z)).val:Cell field)) M mem)
    (space : base+DescentResetStemKey.words (A).degree field M<2^wordBits)
    (sg : Fin Q→Bool) (slots : Fin Q→Slot) :
    let op:=fun j=>DescentResetStemKey.expr (parse) M base (sg j)
      (DescentResetStemKey.readers ports bank H (slots j).1 (slots j).2)
    let mid:=DescentResetStemKey.memory (parse) M base mem
    ∃ keys : Fin Q→Fin H→Block c→Cell (field+2),
      (∀j,(op j).Fits wordBits (base+DescentResetStemKey.words (A).degree field M) ∧ Source (op j) (keys j) M mid) ∧
      ∀j,∀u:Host,
        (DescentScalarBookReshape.book (flat (stem_project_size B) keys) u.2
          (finProdFinEquiv (actorId (actor u),j)) u.1.1).val=
            DescentResetStemKey.code ((oldStemAt B u (sg j) (slots j)).map (stemTicket B (sg j))) := by
  intro op mid
  have authentic (j : Fin Q):=stem_key_window_source B value room signBits onWire actorId values roster chips
    own chart raw ports bank base mem banks span peer neighbors localWords tagged signed space (sg j) (slots j)
  let keys:=fun j=>(authentic j).choose
  refine ⟨keys,fun j=>⟨(authentic j).choose_spec.1,(authentic j).choose_spec.2.1⟩,?_⟩
  intro j u
  rw [book_slice,slice,stem_project_rack]
  exact (authentic j).choose_spec.2.2 u

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
