import OAI.Hierarchy.DescentPhysicalMixedWords

namespace OAI
/-! # All candidate channels from their original root, contact and peer scans -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSixParty.Chronology DescentSIMDLookup DescentResetLocalRoster
open DescentResetDenseOperand ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "V₀" => a.successor
local notation "b₀" => a.rebased floor
local notation "F₀" => (V₀).front
local notation "P₀" => (F₀).peer
local notation "S₀" => (V₀).issuedScene b₀ u.earlier
local notation "E₀" => (V₀).actorEnd b₀
local notation "C₀" => (F₀).contactLayout E₀
local notation "Q₀" => (V₀).privateShape
local notation "K₀" => (V₀).contactShape
local notation "D₀" => u.masked
local notation "regs₀" => (V₀).jointRegisters b₀ u.earlier
local notation "T₀" => (V₀).trunkEnd b₀
local notation "M₀" => (V₀).massEnd b₀
local notation "J₀" => (V₀).jointEnd b₀
local notation "don₀" => (F₀).donorStart E₀
local notation "scene₀" m => ((F₀).trunkScene E₀ S₀ u.sceneFits).image m

/-- The geometric data here are the predecessor's mounted private pages,
original contact donor registers, and the actual two sparse neighbor rosters. -/
structure MeasuredChannels (N : ℕ) where
  rootWords : Bool→Root (Q₀).residual (Q₀).ports→Fin (C₀).hosts→Fin (C₀).groups→Cell (Q₀).panels
  contactValues : Fin (K₀).sockets→Fin 4→Fin (K₀).sparseHosts→Fin (K₀).donor.groups→Cell (K₀).metaBits
  names : Fin N→Fin (P₀).hosts
  now : Fin (P₀).hosts→Fin 4→Option (Fin (P₀).hosts)
  prior : Fin (P₀).oldHosts→Fin (P₀).oldDegree→Option (Fin (P₀).oldHosts)
  near : Fin (P₀).hosts→Fin 3→Option (Fin (P₀).hosts)
  slots : (D₀).sparseHosts=(K₀).sparseHosts
  hosts : (Q₀).oldHosts*(Q₀).shapes=(C₀).hosts*(C₀).shapes
  groups : (Q₀).groups*(Q₀).blocks=(C₀).groups
  coarse : (K₀).donor.groups=(K₀).groups*(K₀).blocks
  lanes : (Q₀).oldBatch=(C₀).batch

variable {u} {N : ℕ} (R : u.MeasuredChannels N)
def MeasuredChannels.capturedChannels : u.CandidateChannels where
  contact x q j v g := R.contactValues q j (v.cast R.slots) ((finProdFinEquiv (g,x)).cast R.coarse.symm)
  privateFields x q j h g := (Q₀).measured C₀ R.rootWords q j (h.cast R.hosts) ((finProdFinEquiv (g,x)).cast R.groups)
  peer j h _ := ⟨DescentResetPeerJointRAM.value (P₀).oldHosts (P₀).shapes (P₀).oldDegree R.prior N R.names R.now h j %
      2^(D₀).field,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  aux j h _ := ⟨DescentResetPeerJointPacked.Aux.value (P₀).shapes R.names R.prior R.near h j %
      2^(D₀).field,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

variable (u) in
def contactResult (m : Memory w) :=(K₀).issuedImage don₀ T₀ (S₀).donor (scene₀ m)
local notation "pre₀" m => (F₀).preScalar E₀ S₀ u.sceneFits m
local notation "fitCut" => (F₀).peers E₀
local notation "trueCells" => R.capturedChannels

local notation "prCut" => (P₀).endAddress fitCut

theorem contactResult_frame (ok : u.Ready) (m : Memory w) (z : ℕ) (inside : z<prCut) :
    u.contactResult m z=(pre₀ m) z:=by
  have order:=(F₀).front_order E₀
  have before : prCut≤(F₀).mixed E₀:=(Nat.le_add_right _ (F₀).newHosts).trans (order.1.trans order.2.1)
  have mixed : (F₀).mixed E₀≤T₀:=(DescentResetTrunkCompactProgram.grow ..).trans (Nat.le_add_right ..)
  have contact:=(K₀).actual don₀ T₀ (S₀).donor u.sceneFits.donor ok.donors ok.mass
    ok.projectionLanes ok.projectionBlocks (scene₀ m)
  have trunk:=(F₀).trunkScene_before E₀ S₀ u.sceneFits m ok.trunk z (inside.trans_le before)
  exact (contact.2.2 z (.inl (inside.trans_le (before.trans mixed)))).trans
    (trunk.trans (((F₀).retained_cuts E₀ S₀ u.sceneFits m).2.1 z inside))

private theorem cell_offset {i H j D : ℕ} (left:i<H) (right:j<D) : i*D+j<H*D:=
  (Nat.add_lt_add_left right _).trans_le (by
    rw [←Nat.succ_mul]
    exact Nat.mul_le_mul_right D left)

/-- The original capture of the actor directory, the four sorted new sockets,
the old neighbors, and three raw sockets remains readable after the contact scan. -/
theorem retained_registers (ok : u.Ready) (m : Memory w)
    (roster : DescentResetPeerJointRAM.Reads regs₀ N R.names R.now R.prior (pre₀ m))
    (three : ∀h i,(pre₀ m) (((V₀).initialPeers b₀).base+(i:Fin 3).val*(P₀).hosts+(h:Fin (P₀).hosts).val)=
      (((R.near h i).elim (P₀).hosts Fin.val : ℕ) : Word w)) :
    DescentResetPeerJointRAM.Reads regs₀ N R.names R.now R.prior (u.contactResult m) ∧
    ∀h i,u.contactResult m (((V₀).initialPeers b₀).base+(i:Fin 3).val*(P₀).hosts+(h:Fin (P₀).hosts).val)=
      (((R.near h i).elim (P₀).hosts Fin.val : ℕ) : Word w) :=by
  have limits:=(P₀).ordered fitCut
  have oldFits:=u.sceneFits.peers.old.oldFits
  have whereOld:=limits.1.trans (limits.2.1.trans (limits.2.2.1.trans limits.2.2.2))
  have four:=(DescentResetSelfPortsRAM.roster_fits ((P₀).three fitCut) (P₀).hosts (P₀).groups (P₀).lanes
    ((limits.2.2.1.trans limits.2.2.2).trans_lt u.sceneFits.peers.total))
  have countFit:=u.sceneFits.count
  have keep:=u.contactResult_frame ok m
  refine ⟨⟨(keep _ ((Nat.lt_add_of_pos_right countFit.1).trans_le countFit.2.2)).trans roster.count,
    ?_,roster.inverseSize,?_,?_⟩,?_⟩
  · intro v
    exact (keep _ ((Nat.add_lt_add_left (v.isLt.trans_le roster.inverseSize) _).trans_le
      u.sceneFits.inverse.2.2)).trans (roster.inverse v)
  · intro v j
    exact (keep _ ((Nat.add_lt_add_left ((cell_offset v.isLt j.isLt).trans_le four.2) _).trans_le
      (four.1.2.2.trans (limits.2.2.1.trans limits.2.2.2)))).trans (roster.current v j)
  · intro v i
    exact (keep _ ((Nat.add_lt_add_left ((cell_offset v.isLt i.isLt).trans_le u.sceneFits.peers.old.oldSize) _).trans_le
      (oldFits.2.2.trans whereOld))).trans (roster.prior v i)
  · intro h i
    have raw : ((V₀).initialPeers b₀).base+3*(P₀).hosts=(P₀).three fitCut:=rfl
    have bound:=Nat.add_lt_add_left (cell_offset i.isLt h.isLt) ((V₀).initialPeers b₀).base
    rw [raw,←Nat.add_assoc] at bound
    exact (keep _ (bound.trans_le (limits.2.1.trans (limits.2.2.1.trans limits.2.2.2)))).trans (three h i)

/-- Positive observations are requested only on the original physical inputs of the
independent programs. No observations on the mixed candidate output are required. -/
structure CaptureRoom (m : Memory w) : Prop where
  early : ∀s t,(u.earlier.pages s t).Fits w fitCut
  pages : ∀s t,Source (.lookup (u.earlier.pages s t) .row) (R.rootWords s t) (Q₀).oldBatch (pre₀ m)
  donors : ∀q f,Source ((K₀).fieldsAt don₀ T₀ (S₀).donor q f) (R.contactValues q f) (K₀).donor.batch
    ((K₀).held don₀ T₀ (S₀).donor (scene₀ m))
  roster : DescentResetPeerJointRAM.Reads regs₀ N R.names R.now R.prior (u.contactResult m)
  three : ∀h i,u.contactResult m (((V₀).initialPeers b₀).base+(i:Fin 3).val*(P₀).hosts+(h:Fin (P₀).hosts).val)=
      (((R.near h i).elim (P₀).hosts Fin.val : ℕ) : Word w)
  distinct : ∀a i j z,R.prior a i=some z→R.prior a j=some z→i=j
  used : N≤(D₀).hosts
  shapes : 0<(P₀).shapes
  keys : (P₀).shapes*DescentResetPeerJointRAM.radix (P₀).oldDegree≤2^(D₀).field
  previousSelf : 2*((P₀).oldDegree+1)≤2^(D₀).field
  batches : 0<(K₀).donor.batch ∧ 0<(Q₀).oldBatch

private theorem capture_source_reindex {H H' G b M w : ℕ} {e : Expr} {mem : Memory w}
    {vals : Fin H'→Fin G→Cell b} (eqn:H=H') (r:Source e vals M mem) :
    Source e (fun v i=>vals (v.cast eqn) i) M mem:=by subst H';exact r

theorem actual_channels (ok : u.Ready) (m : Memory w) (captured : CaptureRoom R m) :
    ChannelReads trueCells (u.privateResult m) :=by
  let low:=(V₀).receipt_order b₀
  let mid:=u.privateStart m
  have stored:= (V₀).joint_sources b₀ u.earlier R.names R.now R.prior R.near (u.contactResult m)
    captured.used ok.joints captured.roster captured.three captured.distinct captured.shapes captured.keys
    captured.previousSelf ok.packed
  have privateFits:=(V₀).private_inputs_fit b₀ u.earlier ok.pages ok.privates
  have d:=(V₀).private_any b₀ u.earlier mid ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  have preserve {bits H G M} (e : Expr) (values : Fin H→Fin G→Cell bits) (fit : e.Fits w J₀)
      (r : Source e values M mid) : Source e values M (u.privateResult m) :=by
    intro p
    exact (eval_below e _ mid _ fit (fun a ha=>d.2 a (.inl ha))).trans (r p)
  constructor
  · intro x q f
    have r:=(K₀).actual_field don₀ T₀ (S₀).donor u.sceneFits.donor ok.donors ok.mass
      ok.projectionLanes ok.projectionBlocks (scene₀ m) captured.batches.1 R.coarse R.contactValues captured.donors q f x
    have joint:=(V₀).joint_any b₀ u.earlier (u.contactResult m) ok.joints ok.packed
    apply preserve _ _ (ProtocolRAMGeneratedWrite.fits_mono _ low.1 r.1)
    have lifted:=capture_source_reindex R.slots r.2
    intro p
    exact (eval_below _ _ (u.contactResult m) mid r.1 (fun i hi=>joint.2 i (.inl hi))).trans (lifted p)
  · intro x q f
    exact u.captured_private_pages ok m R.rootWords captured.early captured.pages captured.batches.2 R.lanes
      R.hosts R.groups q f x
  · intro j
    apply preserve _ _ ((V₀).peerJoint_fits b₀ u.earlier ok.joints ok.packed j)
    have reduced (h : Fin (V₀).sheets.hosts) :
        DescentResetPeerJointRAM.value (P₀).oldHosts (P₀).shapes (P₀).oldDegree R.prior N R.names R.now h j %
          2^(V₀).sheets.metaBits = _ := Nat.mod_eq_of_lt
            (DescentResetPeerJointRAM.value_lt R.prior R.names R.now h j captured.distinct captured.shapes captured.keys)
    simpa only [mid,privateStart,contactResult,masked,MeasuredChannels.capturedChannels,reduced] using stored.1 j
  · intro j
    apply preserve _ _ ((V₀).aux_fits b₀ ok.packed j)
    have reduced (h : Fin (V₀).sheets.hosts) :
        DescentResetPeerJointPacked.Aux.value (P₀).shapes R.names R.prior R.near h j %
          2^(V₀).sheets.metaBits = _ := Nat.mod_eq_of_lt
            (DescentResetPeerJointPacked.Aux.value_lt (P₀).shapes R.names R.prior R.near h j
              captured.distinct captured.shapes captured.keys captured.previousSelf)
    simpa only [mid,privateStart,contactResult,masked,MeasuredChannels.capturedChannels,reduced] using stored.2 j

theorem actual_directory (ok : u.Ready) (m : Memory w) (captured : CaptureRoom R m) :
    DirectoryReads (u:=u) R.names (u.privateResult m):=by
  have early:=(V₀).receipt_order b₀
  have extent:=early.1.trans early.2
  let massImage:=u.contactResult m
  have join:=(V₀).joint_any b₀ u.earlier massImage ok.joints ok.packed
  have privateFits:=(V₀).private_inputs_fit b₀ u.earlier ok.pages ok.privates
  have tail:=(V₀).private_any b₀ u.earlier (u.privateStart m) ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  have keep z (inside:z<M₀) : u.privateResult m z=massImage z:=
    (tail.2 z (.inl (inside.trans_le early.1))).trans (join.2 z (.inl inside))
  have countFit:=ok.joints.measured.count
  have getCount : (D₀).count.base<M₀:=(Nat.lt_add_of_pos_right countFit.1).trans_le countFit.2.2
  have invSize : N≤(D₀).inverse.size:=captured.roster.inverseSize
  have indices : (D₀).inverse.base+N≤M₀:=(Nat.add_le_add_left invSize _).trans ok.joints.measured.inverse.2.2
  exact ⟨(keep _ getCount).trans captured.roster.count,
    fun i=>(keep _ ((Nat.add_lt_add_left i.isLt _).trans_le indices)).trans (captured.roster.inverse i),
    getCount.trans_le extent,indices.trans extent,captured.used.trans_lt ok.joints.measured.newWidth,
    ok.joints.measured.newWidth.le,invSize⟩

private theorem earlier_halo {H P O D N : ℕ} (width : ℕ) (name : Fin N→Fin P)
    (prior : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P)) (v : Fin H) :
    DescentResetPeerJointPacked.Aux.value width name prior near v 0 < DescentResetPeerJointRAM.radix D :=by
  have rad : D+2≤DescentResetPeerJointRAM.radix D:=Nat.le_pow_clog (by decide) _
  have bound (r : Fin O) : DescentClosedHaloChip.weight (prior r) r r≤D:=by
    unfold DescentClosedHaloChip.weight
    simp only [lt_self_iff_false,ite_false,Nat.zero_add]
    calc
      _ ≤ ∑ _ : Fin D,1:=Finset.sum_le_sum (fun i _=>by split <;> omega)
      _ = D:=by simp
  simp only [DescentResetPeerJointPacked.Aux.value,Fin.val_zero,show (0:ℕ)≠3 by decide,
    show (0:ℕ)≠2 by decide,ite_false,ite_true]
  split
  next live=>
    split
    next located=>
      let r : Fin O:=⟨(name ⟨v.val,live⟩).val/width,located⟩
      change DescentClosedHaloChip.value (prior r) r r 0<_
      simp only [DescentClosedHaloChip.value,eq_self,true_or,ite_true]
      have:=bound r
      omega
    next outside=>omega
  next ghost=>omega

/-- The old root digit occupies the low radix at any original old degree.
At a genuine current actor only the actual two relative shape bounds are needed. -/
theorem private_word_room (m : Memory w) (captured : CaptureRoom R m)
    (small : ∀x q (i : Fin 3),i.val<2 → ∀(h : Fin N) g,
      ((trueCells).privateFields x q i (R.names h) g).val<(P₀).shapes)
    (x q) (role : Fin 3) (two : role.val<2) (v : Fin (D₀).hosts) (g : Fin (D₀).groups) :
    DescentResetPeerJointRAM.radix (P₀).oldDegree *
        (dense (H:=(D₀).hosts) R.names ((trueCells).privateFields x q role) v g).val+
          ((trueCells).aux 0 v g).val<2^(D₀).field :=by
  let rad:=DescentResetPeerJointRAM.radix (P₀).oldDegree
  have lo : ((trueCells).aux 0 v g).val<rad:=
    (Nat.mod_le ..).trans_lt (earlier_halo (P₀).shapes R.names R.prior R.near v)
  have hi : (dense (H:=(D₀).hosts) R.names ((trueCells).privateFields x q role) v g).val<(P₀).shapes:=by
    by_cases used:v.val<N
    · simpa only [dense,dite_eq_left used] using small x q role two ⟨v.val,used⟩ g
    · simpa only [dense,dite_eq_right used,Fin.val_zero] using captured.shapes
  have bound:=Nat.mul_le_mul_right rad hi
  rw [Nat.succ_mul] at bound
  rw [Nat.mul_comm]
  exact (Nat.add_lt_add_left lo _).trans_le (bound.trans captured.keys)

/-- Compute the actual seven-field word for every mixed candidate in one positive run
on the memory generated by the original root, measured peer and contact issuers. -/
theorem published_channels (ok : u.Ready) (m : Memory w) (captured : CaptureRoom R m)
    (shapes : ∀x q (i : Fin 3),i.val<2 → ∀(h : Fin N) g,
      ((trueCells).privateFields x q i (R.names h) g).val<(P₀).shapes)
    (lanes : 0<(D₀).lanes) (rankFit : (D₀).lanes*max ((D₀).field*5) (D₀).field≤w/2)
    (maskFit : (D₀).lanes*max ((D₀).field*9) ((D₀).field*7)≤w/2) :
    ∀n<(D₀).jobs,Source (.lookup ((D₀).output n) .row)
      (fun h g=>DescentCandidateMaskRAM.render ((trueCells).maskValues R.names n h g))
      (D₀).lanes ((D₀).image (u.privateResult m)) :=
  mixed_words trueCells R.names ok (u.privateResult m) (actual_channels R ok m captured)
    (actual_directory R ok m captured) (private_word_room R m captured shapes) lanes rankFit maskFit


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
