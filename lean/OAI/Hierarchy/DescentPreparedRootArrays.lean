import OAI.Hierarchy.DescentRecordedRootArrays

namespace OAI
/-! # Physical reads for the original fallback snapshot at the attained receiver -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentGL DescentColonies DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentRelativeContacts DescentGroupPeerOrder
open DescentStageEdgeReceipt DescentSharedBookScan DescentRosterOrder DescentFallbackShapeTable
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail H field p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (pad : Fintype.card input.V ≤ H)
set_option quotPrecheck false
set_option hygiene false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "full" => (A).wire*((A).z*G.b)*(A).cap
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "key" => Fin.valEmbedding (n:=S.groupCount i)
local notation "names" => cableNames k (groupRank key ((id_).trans Fin.valEmbedding))
local notation "signed_" => signedPanel A (input.order.trans Fin.valEmbedding) S input.valid names
local notation "naturalPitch" => B.frame.enough.trans (Nat.sub_le ..)
variable {nbits t : ℕ} (recorder : B.Recorded p) (wider : t < field)
  (level : m-cc < 2^nbits) (one : 1 < 2^nbits) (capacity : 2^(m-cc)*full < 2^nbits)
  (codes : 2*rows (m-cc) (2^(Z).n) ≤ 2^t) (active : 0 < full)
  (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*(A).degree))
variable (peers : Fin H→Fin (A).degree→Option (Fin H))
  (actual : ∀v j,peers (id_ v) j=(hostRoster A ((id_).trans Fin.valEmbedding) v j).map id_)

include recorder wider level one capacity codes active quotaPos degreePos actual in
theorem arrays_at {u : ℕ} (dim : u=m) (μ : Layout u) (won : HEq μ B.frame.basis)
    (small : cc ≤ u)
    (values : Fin H→Block cc→Block (u-cc)→Cell t)
    (ports : Fin H→Block cc→Block (u-cc)→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (sample : ∀v hi lo,values (id_ v) hi lo=ClosedReset.Recorded.realPanel (reset:=B) dim μ nbits t v hi lo)
    (signed : ∀v hi lo j,ports (id_ v) hi lo j=signed_ (donor ((Equiv.cast (congrArg Block dim)).trans digits)
      μ small v hi lo) j) :
    ∃x : OriginalArrays B pad field,x.peers=peers ∧ x.word=originalWord B nbits t ∧
      (∀v hi lo,x.stencil v hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo)=(values v hi lo).val) ∧
      ∀v hi lo j,x.marks v hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo) j=ports v hi lo j := by
  subst u
  obtain rfl:=eq_of_heq won
  have st:∀v hi lo j,ports (id_ v) hi lo j=signed_ (donor digits B.frame.basis naturalPitch v hi lo) j := by
    simpa only [Equiv.cast_refl,Equiv.refl_trans] using signed
  let x:=original_arrays B pad values ports peers actual sample st wider recorder level one capacity codes active quotaPos degreePos
  exact ⟨x,rfl,rfl,fun _ _ _=>rfl,fun _ _ _ _=>rfl⟩

open DescentPackedColony DescentGLPacked.BankImage.SignedFields
variable {hw a b K R M : ℕ}
local notation "L" => 2^(a+b-cc)
local notation "groups" => Equiv.refl (Fin (S.groupCount i))
local notation "depth" => GroupStage.depthBound D n f g
variable (rc : Receiver (A).degree (A).cap (2^k) (Z).n (a+b-cc) cc H (S.groupCount i) K R M a b t field depth hw)
    (book : RootBook (Z).n (a+b-cc) (A).degree L (A).cap field) (space : rc.PreparedFits book)
    (mem : Memory hw)
local notation "out" => bankAt rc.stencil rc.tapped t (A).degree rc.signedEnd H (2^cc) M
local notation "middle" => rc.preparedMid book space mem

include recorder level one capacity codes active quotaPos degreePos in
/-- Use the literal numeric shape and flag column exposed by the recorded
receiver input, including every padded packed word supplied by its publisher. -/
theorem published_roots (dim : a+b=m) (μ : DescentGL.Layout (a+b)) (won : HEq μ B.frame.basis)
    (prior : PackedFlow.Padded.Published (h:=a) (l:=b) M t rc.stencil.base id_
      (fun v hi lo=>
        let y:=join naturalPitch hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo)
        ((2*Stencil.shapeCode (a+b-cc) (2^(Z).n) (fieldsRelative cc
          (ClosedReset.Recorded.originalCell (reset:=B) v ((rearrange B.frame.basis).symm y)))+
          (((A).hub v) || decide ((B.frame.host v,group ((Z).placement.b (B.frame.host v)) y)∈(Z).placement.keys)).toNat:ℕ):Cell t))
      mem) :
    PackedFlow.Padded.Published (h:=a) (l:=b) M t rc.stencil.base id_
      (ClosedReset.Recorded.realPanel (reset:=B) dim μ nbits t) mem := by
  obtain ⟨all,words,old⟩:=prior
  refine ⟨all,words,?_⟩
  intro v hi lo
  have eqn:=recorder.stencil_cell dim μ won (by simpa only [dim] using level) one (by simpa only [dim] using capacity) (by simpa only [dim] using codes)
    active quotaPos degreePos v hi lo
  dsimp only at eqn
  simp only [Equiv.apply_symm_apply] at eqn
  rw [old]
  exact (congrArg (fun z : ℕ => (z : Cell t)) eqn.symm).trans (Fin.cast_val_eq_self _)

private theorem block_cast_val {a b : ℕ} (e : a = b) (v : Block a) :
    ((Equiv.cast (congrArg Block e)) v).val = v.val := by
  subst b
  rfl

include recorder wider level one capacity codes active quotaPos degreePos actual in
/-- The same two measured old arrays both supply the snapshot and remain readable
as untagged, tagged and unsigned codec words in the receiver's prepared memory. -/
theorem prepared_arrays (dim : a+b=m) (μ : DescentGL.Layout (a+b)) (won : HEq μ B.frame.basis)
    (size : 2^(a+b)=S.groupCount i*2^k) (pack : 2^b=M*2^k) (small : cc ≤ a+b) (repack : M*L=2^b)
    (old : ∀j x,Reads (rc.old j x) (fun h gp=>DescentSignedCableCodec.encode
      (Prepare.signed A (input.order.trans Fin.valEmbedding) S input.valid (groups).toEmbedding id_ x j h gp)) (R*M) mem)
    (saved : mem rc.saved.base=((DescentExterior.matrixCode μ).val:Word hw))
    (low : rc.saved.Fits hw rc.origin) (table : rc.stencil.Fits hw rc.origin)
    (span : H*chunks (2^cc) M≤rc.stencil.size)
    (published : PackedFlow.Padded.Published (h:=a) (l:=b) M t rc.stencil.base id_
      (ClosedReset.Recorded.realPanel (reset:=B) dim μ nbits t) mem) :
    ∃x : OriginalArrays B pad field,x.peers=peers ∧ x.word=originalWord B nbits t ∧
      (∀v hi lo,x.stencil v hi lo < 2^t) ∧
      (∀v hi lo,x.stencil (id_ v) hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo)=
        (ClosedReset.Recorded.realPanel (reset:=B) dim μ nbits t v hi lo).val) ∧
      (∀lo,Reads (out (.inl (0,lo))) (fun v hi=>
        (x.stencil v hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo):Cell field)) M middle) ∧
      (∀lo,Reads (out (.inl (1,lo))) (fun v hi=>
        ((x.stencil v hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo)+1:ℕ):Cell field)) M middle) ∧
      ∀j lo,Reads (out (.inr (j,lo))) (fun v hi=>
        ((DescentSignedCableCodec.encode (x.marks v hi (Fin.cast (congrArg (fun z=>2^(z-cc)) dim) lo) j)).val:Cell field)) M middle := by
  have axis : PackedFlow.digits groups size=(Equiv.cast (congrArg Block dim)).trans digits := by
    apply Equiv.ext
    intro u
    apply congrArg ((@finProdFinEquiv (S.groupCount i) (2^k)).symm)
    exact Fin.ext (block_cast_val dim u).symm
  obtain ⟨vals,ports,own,tag,raw,stamp,cables⟩:=prepared_mid_window_read A (input.order.trans Fin.valEmbedding) S
    input.valid groups id_ rc book space μ size pack small repack mem old saved low table span _ published
  rw [axis] at cables
  obtain ⟨x,grid,sourceWord,atShape,atWire⟩:=arrays_at B pad recorder wider level one capacity codes active quotaPos
    degreePos peers actual dim μ won small vals ports stamp cables
  refine ⟨x,grid,sourceWord,?_,?_,?_,?_,?_⟩
  · intro v hi lo
    let eqn:=congrArg (fun z=>2^(z-cc)) dim
    have found:=atShape v hi (Fin.cast eqn.symm lo)
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq] at found
    rw [found]
    exact (vals v hi (Fin.cast eqn.symm lo)).isLt
  · intro v hi lo
    rw [atShape,stamp]
  · intro lo; simpa only [atShape] using own lo
  · intro lo; simpa only [atShape, Nat.cast_add, Nat.cast_one] using tag lo
  · intro j lo; simpa only [atWire] using raw j lo

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
