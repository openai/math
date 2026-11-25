import OAI.Hierarchy.DescentCalendarSenderProbes
import OAI.Hierarchy.DescentPreparedRootArrays
import OAI.Hierarchy.DescentPreparedMatrixFrame
import OAI.Hierarchy.DescentIssuedMatrixPacket
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # The sender matrix and signed probes from the same issued root packet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "m" => S.groupWidth k tail i+k
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "peer" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((id_).trans Fin.valEmbedding))
variable {M field bw N K R hm lb tiny p nbits t : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm lb tiny field dep bw)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B pad rc book mem) (src : RootSources deg (2^r) cap)
local notation "paid" => Recorded.paddedValue (b:=field) cc r peer (Recorded.oldDepth B) (Recorded.oldWidth B)
local notation "middle" => rc.preparedMid book space mem
local notation "done" => rc.preparedImage book space mem
local notation "rank_" => fun v j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=deg)
  (book.common rc.projectionEnd H) (2^dep) (dep+2) middle v j).val
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth

private theorem order_cast {u v c : ℕ} (eqn : u=v) (μ : DescentGL.Layout u) (ν : DescentGL.Layout v) (same : HEq μ ν)
    (hu : c ≤ u) (hv : c ≤ v) (g : Block c) (x y : Block (u-c)) :
    Receiver.matrixBefore μ hu g x y=GroupStage.previousDigit ν hv g
      (x.cast (congrArg (fun t=>2^(t-c)) eqn)) (y.cast (congrArg (fun t=>2^(t-c)) eqn)) := by
  subst v
  cases eq_of_heq same
  rfl

/-- All original fields needed to run the dated peer query. The matrix is
read on completion of the roots and the remaining fields are the original
inputs of that very matrix, including the words in padded rows. -/
structure RootPacket (x : OriginalArrays B pad field) (nbits t : ℕ) : Prop where
  word : x.word=originalWord B nbits t
  short : ∀v hi lo,x.stencil v hi lo < 2^t
  matrix : ∀j,Source (src.matrixRow H j) (fun v hi=>calendar_sender_matrix B M field rc book space mem hdr x v hi j) M done
  mounted : Mounted src.peers x.peers middle J M
  sites : ∀a,Reads (src.here a) (fun v hi=>(x.stencil v hi (a.cast axis):Cell field)) M middle
  tagged : ∀a,Reads (src.tagged a) (fun v hi=>((x.stencil v hi (a.cast axis)+1:ℕ):Cell field)) M middle
  signed : ∀s a,Reads (src.signed a s) (fun v hi=>((DescentSignedCableCodec.encode (originalCable B x v hi a s)).val:Cell field)) M middle
  routes : x.peers=peer

/-- Use the arrays returned by the native matrix publisher for all physical
rows, including padded hosts. They supply both the root observation and the
actual signed and reservation operands read by the later contact program. -/
theorem calendar_matrix_origins (recorded : B.Recorded p) (wider : t < field)
    (level : m-cc < 2^nbits) (one : 1 < 2^nbits) (mass : 2^(m-cc)*full < 2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows (m-cc) (2^(Z).n) ≤ 2^t)
    (positive : 0 < full) (quotaPositive : 0 < quota S.rounds) (degreePositive : 0 < 32*Nat.clog 2 (2*deg))
    (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis) (small : cc ≤ (Z).k)
    (values : Fin H→Block cc→Block r→Cell t)
    (marks : Fin H→Block cc→Block r→Fin (2*cap)→Option (Live deg cap))
    (sample : ∀v hi j,values (id_ v) hi j=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi j)
    (cables : ∀v hi j s,marks (id_ v) hi j s=signedPanel A (input.order.trans Fin.valEmbedding) S input.valid
      names (donor ((Equiv.cast (congrArg Block B.keyWidth)).trans digits) μ small v hi j) s)
    (area : src.OperandRoom H J M bw (rc.headerEnd book))
    (markSize : ∀a s,H*chunks J M ≤ (src.signed a s).size)
    (rows : ∀j,Source (src.matrixRow H j) (fun v hi=>RootSources.paddedRow
      (fun u b a=>(values u b a).val) peer marks rank_ (fun _=>Receiver.matrixBefore μ small) paid v hi j) M middle)
    (signed : ∀s a,Reads (src.signed a s) (fun v hi=>DescentResetOppositePayload.widened deg cap field (marks v hi a s))
      M middle) (mounted : Mounted src.peers peer middle J M) :
    ∃x : OriginalArrays B pad field,x.word=originalWord B nbits t ∧ x.peers=peer ∧
      (∀v hi (a : Block r),x.stencil v hi (a.cast axis)=(values v hi a).val) ∧
      (∀v hi (a : Block r) s,x.marks v hi (a.cast axis) s=marks v hi a s) ∧
      (∀j,Source (src.matrixRow H j) (fun v hi=>calendar_sender_matrix B M field rc book space mem hdr x v hi j) M done) ∧
      (∀a s,Reads (src.signed a s) (fun v hi=>DescentResetOppositePayload.widened deg cap field (originalCable B x v hi a s))
        M done) ∧ Mounted src.peers x.peers done J M := by
  have old (v : input.V) (j : Fin deg) :
      peer (id_ v) j=(hostRoster A ((id_).trans Fin.valEmbedding) v j).map id_ :=
    Recorded.peer_at (input:=input) v j
  obtain ⟨x,routes,word,shape,sign⟩:=arrays_at B pad recorded wider level one mass codes positive quotaPositive
    degreePositive peer old B.keyWidth μ won small values marks sample cables
  have comparison (hi a b) := order_cast B.keyWidth μ B.frame.basis won small
    (B.frame.enough.trans (Nat.sub_le ..)) hi a b
  have marked : (fun (u : Fin H) (hi : Block cc) (a : Block r) => x.marks u hi (a.cast axis)) = marks := by
    funext u hi a s
    exact sign u hi a s
  have occupied:=rc.final_matrix_rows book space mem src area _ rows
  refine ⟨x,word,routes,shape,sign,?_,?_,?_⟩
  · intro j
    rw [calendar_sender_matrix_eq]
    simpa only [routes,shape,marked,←comparison] using occupied j
  · intro a s
    refine Chooser.reads_before (src.signed a s) _ middle done ?_ (rc.before_header book space mem)
      (area.ports a s) (markSize a s)
    simpa only [originalCable,sign] using signed s a
  · rw [routes]
    exact Chooser.mounted_before src.peers (src.tagged 0) peer middle done mounted
      (rc.before_header book space mem) (area.remoteShape 0)

theorem calendar_matrix_packet (recorded : B.Recorded p) (wider : t < field)
    (level : m-cc < 2^nbits) (one : 1 < 2^nbits) (mass : 2^(m-cc)*full < 2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows (m-cc) (2^(Z).n) ≤ 2^t)
    (positive : 0 < full) (quotaPositive : 0 < quota S.rounds) (degreePositive : 0 < 32*Nat.clog 2 (2*deg))
    (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis) (small : cc ≤ (Z).k)
    (values : Fin H→Block cc→Block r→Cell t)
    (marks : Fin H→Block cc→Block r→Fin (2*cap)→Option (Live deg cap))
    (sample : ∀v hi j,values (id_ v) hi j=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi j)
    (cables : ∀v hi j s,marks (id_ v) hi j s=signedPanel A (input.order.trans Fin.valEmbedding) S input.valid
      names (donor ((Equiv.cast (congrArg Block B.keyWidth)).trans digits) μ small v hi j) s)
    (area : src.OperandRoom H J M bw (rc.headerEnd book))
    (markSize : ∀a s,H*chunks J M ≤ (src.signed a s).size)
    (rows : ∀j,Source (src.matrixRow H j) (fun v hi=>RootSources.paddedRow
      (fun u b a=>(values u b a).val) peer marks rank_ (fun _=>Receiver.matrixBefore μ small) paid v hi j) M middle)
    (signed : ∀s a,Reads (src.signed a s) (fun v hi=>DescentResetOppositePayload.widened deg cap field (marks v hi a s))
      M middle) (mounted : Mounted src.peers peer middle J M)
    (localWords : ∀a,Reads (src.here a) (fun v hi=>((values v hi a).val:Cell field)) M middle)
    (tagged : ∀a,Reads (src.tagged a) (fun v hi=>((values v hi a).val+1:Cell field)) M middle) :
    ∃x : OriginalArrays B pad field,RootPacket B rc book space mem hdr src x nbits t := by
  obtain ⟨x,word,routes,shape,sign,matrix,_,_⟩:=calendar_matrix_origins B rc book space mem hdr src recorded
    wider level one mass codes positive quotaPositive degreePositive μ won small values marks sample cables area
    markSize rows signed mounted
  refine ⟨x,word,?_,matrix,?_,?_,?_,?_,routes⟩
  · intro v hi lo
    let a:=lo.cast (axis).symm
    have value := shape v hi a
    simp only [a,Fin.cast_cast,Fin.cast_refl, id_eq] at value
    rw [value]
    exact (values v hi a).isLt
  · simpa only [routes] using mounted
  · intro a
    simpa only [shape] using localWords a
  · intro a
    simpa only [shape,Nat.cast_add,Nat.cast_one] using tagged a
  · intro s a
    simpa only [originalCable,sign,DescentResetOppositePayload.widened] using signed s a


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
