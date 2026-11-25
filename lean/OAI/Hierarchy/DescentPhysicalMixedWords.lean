import OAI.Hierarchy.DescentPhysicalPrivatePanelCapture

namespace OAI
/-! # Both physical candidate sectors use one compact directory and the same three attained ranks -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip DescentResetDenseOperand DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "V₀" => a.successor
local notation "b₀" => a.rebased floor
local notation "K" => (V₀).contactShape
local notation "Q" => (V₀).privateShape
local notation "D" => u.masked
local notation "J" => (V₀).jointEnd b₀
local notation "T" => (V₀).trunkEnd b₀
local notation "active" => Fin (D).hosts→Fin (D).groups→Cell (D).field
local notation "sparse" => Fin (D).sparseHosts→Fin (D).groups→Cell (D).field

/-- Three private and four direct-contact values come from their own RAM issuers.
The four sorted site codes and four self fields are shared across all slots. -/
structure CandidateChannels where
  contact : Fin (K).blocks→Fin (K).sockets→Fin 4→sparse
  privateFields : Fin (Q).blocks→Fin (Q).keys→Fin 3→sparse
  peer : Fin 4→active
  aux : Fin 4→active

variable {u} (C : u.CandidateChannels) {N : ℕ} (names : Fin N→Fin u.masked.sparseHosts)
local notation "shift₀" => Nat.clog 2 ((V₀).front.peer.oldDegree+2)
local notation "rad₀" => 2^shift₀
local notation "pull" => dense (H:=(D).hosts) names

structure ChannelReads (m : Memory w) : Prop where
  contact : ∀x q j,Source ((K).fieldExpr T x q j) (C.contact x q j) (D).lanes m
  privateFields : ∀x q j,Source ((Q).operand J q j x) (C.privateFields x q j) (D).lanes m
  peer : ∀j,Source ((V₀).peerJoint b₀ j) (C.peer j) (D).lanes m
  aux : ∀j,Source ((V₀).peerAux b₀ j) (C.aux j) (D).lanes m

structure DirectoryReads (m : Memory w) : Prop where
  count : m (D).count.base=(N:Word w)
  inverse : ∀i,m ((D).inverse.base+(i:Fin N).val)=((names i).val:Word w)
  countLow : (D).count.base<(D).first
  inverseLow : (D).inverse.base+N≤(D).first
  usedWidth : N<2^w
  hostsWidth : (D).hosts≤2^w
  capacity : N≤(D).inverse.size

namespace CandidateChannels
def joint (x : Fin (Q).blocks) (q : Fin (Q).keys) (j : Fin 3) : active :=
  if j.val<2 then fun h g => ((rad₀*(pull (C.privateFields x q j) h g).val+(C.aux 0 h g).val:ℕ):Cell (D).field)
  else C.aux 1

def endpoint (job : ℕ) (role : Fin 3) : active :=
  match (V₀).jobAt job with
  | none=>fun _ _ => 0
  | some (.inl (x,q))=>pull (C.contact x q ⟨role.val+1,by omega⟩)
  | some (.inr (x,q))=>C.joint names x q role

def work (job : ℕ) : active :=
  match (V₀).jobAt job with
  | none=>fun _ _ => 0
  | some (.inl (x,q))=>pull (C.contact x q 0)
  | some (.inr (x,q))=>pull (C.privateFields x q 2)

def rankValues (i : ℕ) (h : Fin (D).hosts) (g : Fin (D).groups) (j : Fin 5) : Cell (D).field :=
  Fin.lastCases (C.endpoint names (i/3) ⟨i%3,Nat.mod_lt _ (by decide)⟩ h g) (fun k=>C.peer k h g) j

def maskValues (job : ℕ) (h : Fin (D).hosts) (g : Fin (D).groups) (j : Fin 9) : Cell (D).field :=
  let role i:=C.endpoint names job i h g
  let rank (i : Fin 3):=DescentResetJoinedRank.rank (C.rankValues names (3*job+i.val) h g)
  let missing:=if ((V₀).jobAt job).isSome then C.aux 2 h g else 0
  let width:=C.work names job h g
  ![width,role 0,role 1,role 2,rank 0,rank 1,rank 2,missing,width] j

theorem ranks_at (job : ℕ) (i : Fin 3) (h g) :
    C.maskValues names job h g ⟨4+i.val,by omega⟩ =
      DescentResetJoinedRank.rank (C.rankValues names (3*job+i.val) h g):=by
  fin_cases i <;> rfl

end CandidateChannels

private theorem zero_channel (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin (D).hosts) (_ : Fin (D).groups)=>(0:Cell (D).field)) (D).lanes m:=by
  intro p
  change 0=(((finFunctionFinEquiv (fun i : Fin (D).lanes=>
    if _ : p.2.val*(D).lanes+i.val<(D).groups then (0:Cell (D).field) else 0)).val:ℕ):Word w)
  simp

attribute [local irreducible] DescentPackedZip.Source

set_option maxHeartbeats 420000 in
/-- Publish every mixed job in one actual register image. The emitter takes only
the original four contact columns, three private columns, and the shared
peer/auxiliary columns. All three rank values in the result are computed. -/
theorem mixed_words (ok : u.Ready) (m : Memory w) (loaded : ChannelReads C m)
    (dir : DirectoryReads (u:=u) names m)
    (wordRoom : ∀x q (i : Fin 3),i.val<2 → ∀h g,rad₀*(pull (C.privateFields x q i) h g).val+
      (C.aux 0 h g).val<2^(D).field)
    (lanes : 0<(D).lanes) (rankFit : (D).lanes*max ((D).field*5) (D).field≤w/2)
    (maskFit : (D).lanes*max ((D).field*9) ((D).field*7)≤w/2) :
    ∀n<(D).jobs,Source (.lookup ((D).output n) .row)
      (fun h g=>DescentCandidateMaskRAM.render (C.maskValues names n h g)) (D).lanes ((D).image m) := by
  let seen:=(D).relay.mounted m
  have early := (V₀).receipt_order b₀
  have roof:=ok.privates
  have prior:=early.1.trans early.2
  have liftFit {bank : Bank} (r : bank.Fits w ((V₀).massEnd b₀)) : bank.Fits w (D).first:=
    ⟨r.1,r.2.1,r.2.2.trans prior⟩
  have safe:=(D).relay.book_fits _ _ (liftFit ok.joints.measured.count) (liftFit ok.joints.measured.inverse)
    ((D).ordered.2.trans_lt ok.masked)
  have contactFit x q f:=ProtocolRAMGeneratedWrite.fits_mono _ prior
    ((K).fields_fit T (prior.trans_lt roof) x q f)
  have contact (x q f) : Source ((D).relay.load (D).count (D).inverse ((K).fieldExpr T x q f))
      (pull (C.contact x q f)) (D).lanes seen:=
    (D).sparse_source _ m names _ (contactFit x q f) (loaded.contact x q f) safe dir.count dir.inverse
      dir.countLow dir.inverseLow dir.usedWidth dir.hostsWidth dir.capacity ok.masked
  have auxFit (j : Fin 4) := ProtocolRAMGeneratedWrite.fits_mono _ early.2
    ((V₀).aux_fits b₀ (early.2.trans_lt roof) j)
  have aux j:= (D).compact_source _ m _ (auxFit j) (loaded.aux j) ok.masked
  have peers j := (D).compact_source _ m _ (ProtocolRAMGeneratedWrite.fits_mono _ early.2
    ((V₀).peerJoint_fits b₀ u.earlier ok.joints (early.2.trans_lt roof) j)) (loaded.peer j) ok.masked
  have privateRead (x q f) :=(D).sparse_source _ m names _ ((Q).output_fits J q f x roof)
    (loaded.privateFields x q f) safe dir.count dir.inverse dir.countLow dir.inverseLow
    dir.usedWidth dir.hostsWidth dir.capacity ok.masked
  have linked (x q i) : Source (((V₀).privateJoint b₀ x q i).load (D).relay (D).count (D).inverse)
      (C.joint names x q i) (D).lanes seen:=by
    by_cases cases_i:i.val<2
    · have observed:=(D).private_endpoint_source shift₀ _ _ m names _ _ ((Q).output_fits J q i x roof) (auxFit 0)
        (loaded.privateFields x q i) (loaded.aux 0) safe dir.count dir.inverse dir.countLow dir.inverseLow
        dir.usedWidth dir.hostsWidth dir.capacity ok.masked (wordRoom x q i cases_i)
      have valueEq : (C.joint names x q i)=(fun h g=>DescentContactEndpointFields.endpoint shift₀
          (pull (C.privateFields x q i) h g) (C.aux 0 h g) (wordRoom x q i cases_i h g)):=by
        funext h g
        apply Fin.ext
        simp only [CandidateChannels.joint,ite_eq_left cases_i,DescentContactEndpointFields.endpoint,
          Fin.val_cast_of_lt (wordRoom x q i cases_i h g)]
      rw [valueEq]
      simpa only [ResetOutput.privateJoint,ite_eq_left cases_i] using observed
    · simpa only [ResetOutput.privateJoint,CandidateChannels.joint,ite_eq_right cases_i,Operand.load] using aux 1
  have found n : Source (((V₀).actualTarget b₀ n).load (D).relay (D).count (D).inverse)
      (C.endpoint names (n/3) ⟨n%3,Nat.mod_lt _ (by decide)⟩) (D).lanes seen:=by
    cases equation:(V₀).jobAt (n/3) with
    | none=>simpa only [ResetOutput.actualTarget,CandidateChannels.endpoint,equation,Operand.load] using
        (zero_channel (u:=u) seen)
    | some e=>
      rcases e with ⟨x,q⟩|⟨x,q⟩
      · simpa only [ResetOutput.actualTarget,CandidateChannels.endpoint,equation,
          DescentContactOutputShape.Shape.candidate,Operand.load] using contact x q ⟨n%3+1,by omega⟩
      · simpa only [ResetOutput.actualTarget,CandidateChannels.endpoint,equation] using linked x q ⟨n%3,Nat.mod_lt _ (by decide)⟩
  apply (D).mixed.words seen (u.genuine_mask_previous ok.joints ok.masked) ok.masked lanes rankFit maskFit
    (C.rankValues names) (C.maskValues names)
  · intro n _ i
    change Source ((u.jointRank n i).load (D).relay (D).count (D).inverse)
      (fun h g => C.rankValues names n h g i) (D).lanes seen
    refine Fin.lastCases ?_ (fun j=>?_) i
    · have rank : (fun h g => C.rankValues names n h g (Fin.last 4)) =
          C.endpoint names (n/3) ⟨n%3,Nat.mod_lt _ (by decide)⟩ := by
        funext h g
        exact Fin.lastCases_last ..
      rw [rank]
      simpa only [jointRank,Fin.lastCases_last] using found n
    · have rank : (fun h g => C.rankValues names n h g j.castSucc) = C.peer j := by
        funext h g
        exact Fin.lastCases_castSucc ..
      rw [rank]
      simpa only [jointRank,Fin.lastCases_castSucc,Operand.load,seen] using peers j
  · intro n _ i plain
    change Source (((V₀).actualRaw b₀ n i).load (D).relay (D).count (D).inverse)
      (fun h g => C.maskValues names n h g i) (D).lanes seen
    cases equation:(V₀).jobAt n with
    | none=>
      fin_cases i <;> first | exact (plain (by decide)).elim |
        simpa [seen,ResetOutput.actualRaw,CandidateChannels.maskValues,CandidateChannels.endpoint,
          CandidateChannels.work,equation,Operand.load] using (zero_channel (u:=u) seen)
    | some pair=>
      rcases pair with ⟨x,q⟩|⟨x,q⟩
      · fin_cases i <;> first | exact (plain (by decide)).elim |
          simpa [seen,ResetOutput.actualRaw,DescentContactOutputShape.Shape.raw,
            DescentContactOutputShape.Shape.candidate,CandidateChannels.maskValues,CandidateChannels.endpoint,
            CandidateChannels.work,equation,Operand.load] using contact x q _ |
          simpa [seen,ResetOutput.actualRaw,DescentContactOutputShape.Shape.raw,
            CandidateChannels.maskValues,equation,Operand.load] using aux 2
      · fin_cases i <;> first | exact (plain (by decide)).elim |
          simpa [seen,ResetOutput.actualRaw,ResetOutput.privateRaw,CandidateChannels.work,
            CandidateChannels.maskValues,equation,Operand.load] using privateRead x q 2 |
          simpa [seen,ResetOutput.actualRaw,ResetOutput.privateRaw,CandidateChannels.endpoint,
            CandidateChannels.maskValues,equation] using linked x q 0 |
          simpa [seen,ResetOutput.actualRaw,ResetOutput.privateRaw,CandidateChannels.endpoint,
            CandidateChannels.maskValues,equation] using linked x q 1 |
          simpa [seen,ResetOutput.actualRaw,ResetOutput.privateRaw,CandidateChannels.endpoint,
            CandidateChannels.maskValues,equation] using linked x q 2 |
          simpa [seen,ResetOutput.actualRaw,ResetOutput.privateRaw,CandidateChannels.maskValues,
            equation,Operand.load] using aux 2
  · exact fun n _ i h g=>C.ranks_at names n i h g


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
