import OAI.Hierarchy.DescentDatedSignedFields
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # Form one full-cube source column per old signed port

The preceding graph stores a packed word per old local block and signed slot.
The gather interleaves these old block columns inside each group.  Changing the
logical row type from a group to a full cube does not move any words in RAM.
-/
namespace Hierarchy.DescentGLPacked.BankImage.SignedFields
open DescentSIMDLookup DescentPackedZip DescentColonies
open DescentPacking.PackedMatch.Local DescentSixParty
open DescentStageEdgeReceipt DescentGroupPeerOrder ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {G H N b M rows lanes w : ℕ}

theorem flatten_source (size : rows=G*N) (width : lanes=M*N)
    (positive : 0<M) (nonempty : 0<N) (term : Expr)
    (X : Fin H→Fin G→Fin N→Cell b) (mem : Memory w)
    (source : Source term (fun v g=>encode b N (X v g)) M mem) :
    Source term (fun v z=>
      let q:=finProdFinEquiv.symm (Fin.cast size z)
      X v q.1 q.2) lanes mem := by
  subst rows
  subst lanes
  let Y (v : Fin H) (z : Fin (G*N)) := X v (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
  have grouped : groupedRows Y=fun v g=>encode b N (X v g) := by
    funext v g
    apply congrArg (encode b N)
    funext i
    change X v (finProdFinEquiv.symm (finProdFinEquiv (g,i))).1
      (finProdFinEquiv.symm (finProdFinEquiv (g,i))).2 = X v g i
    rw [Equiv.symm_apply_apply]
  intro p
  let q : Row H G M := (p.1,Fin.cast (chunks_group G M N positive nonempty) p.2)
  have same : (row H G M q).val=(row H (G*N) (M*N) p).val := by
    change p.2.val+chunks G M*p.1.val=p.2.val+chunks (G*N) (M*N)*p.1.val
    exact congrArg (fun n : ℕ => p.2.val + n * p.1.val) (chunks_group G M N positive nonempty).symm
  have dataEq:=data_group nonempty Y q p rfl rfl
  rw [grouped] at dataEq
  exact (congrArg (fun j : ℕ => term.eval mem (j:Word w)) same.symm).trans
    ((source q).trans (congrArg (fun j : ℕ=>(j:Word w)) dataEq.symm))

theorem signed_source (size : rows=G*N) (width : lanes=M*N) (positive : 0<M) (nonempty : 0<N)
    (tbl : Fin N→Tables) (old : Fin N→Expr) (origin : ℕ)
    (bounds : Gather.Bounds (d:=b) (M:=M) (w:=w) tbl old origin)
    (X : Fin H→Fin G→Fin N→Cell b) (mem : Memory w)
    (fixed : ∀j,DescentPackedZip.Static (tbl j) (Gather.setField (d:=b) j) M mem)
    (read : ∀j,Source (old j) (fun v g=>X v g j) M mem) :
    (Gather.assembly tbl old).Fits w origin ∧ Source (Gather.assembly tbl old) (fun v z=>
      let q:=finProdFinEquiv.symm (Fin.cast size z)
      X v q.1 q.2) lanes mem := by
  refine ⟨Gather.fits tbl old origin bounds _,flatten_source size width positive nonempty _ X mem ?_⟩
  have all:=Gather.collected tbl old origin bounds mem fixed X read (List.finRange N)
  simpa only [Gather.assembly,List.mem_finRange,ite_true] using all

section Stage
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i h l cap : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {gate : PoweredGadget F} {q ε : ℝ} (A : GroupStage W gate q ε J V k)
  (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J≃Fin G) (host : V↪Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => host.trans Fin.valEmbedding
local notation "names" => Stage.cableNames k (groupRank rs vs)
local notation "sign" => DescentSharedCableNames.Stage.signedPanel A native S ready names
local notation "b" => DescentSignedCableCodec.width A.degree A.cap

def oldWord (size : 2^(h+l)=G*2^k) (j : Fin (2*A.cap)) (v : Fin H) (z : Block (h+l)) : Cell b :=
  let a:=finProdFinEquiv.symm (Fin.cast size z)
  DescentSignedCableCodec.encode (Stage.Prepare.signed A native S ready groups.toEmbedding host a.2 j v a.1)

theorem oldWord_at (size : 2^(h+l)=G*2^k) (j : Fin (2*A.cap)) (v : V) (z : Block (h+l)) :
    let a:=finProdFinEquiv.symm (Fin.cast size z)
    oldWord A native S ready groups host size j (host v) z=
      DescentSignedCableCodec.encode (sign ((groups.symm a.1,v),a.2) j) := by
  let a:=finProdFinEquiv.symm (Fin.cast size z)
  have live : ∃p : J×V,groups.toEmbedding p.1=a.1 ∧ host p.2=host v :=
    ⟨(groups.symm a.1,v),groups.apply_symm_apply _,rfl⟩
  have point : live.choose=(groups.symm a.1,v) :=
    Prod.ext (groups.injective (live.choose_spec.1.trans (groups.apply_symm_apply _).symm))
      (host.injective live.choose_spec.2)
  change DescentSignedCableCodec.encode (Stage.Prepare.spreadField groups.toEmbedding host none
    (fun p=>sign (p,a.2) j) (host v) a.1)=DescentSignedCableCodec.encode (sign ((groups.symm a.1,v),a.2) j)
  rw [Stage.Prepare.spreadField,dite_eq_left live,point]

set_option maxHeartbeats 600000 in
theorem previous_ports (size : 2^(h+l)=G*2^k) (width : 2^l=M*2^k) (pos : 0<M)
    (j : Fin (2*A.cap)) (tbl : Fin (2^k)→Tables) (old : Fin (2^k)→Expr) (origin : ℕ)
    (room : Gather.Bounds (d:=b) (M:=M) (w:=w) tbl old origin) (mem : Memory w)
    (static : ∀x,DescentPackedZip.Static (tbl x) (Gather.setField (d:=b) x) M mem)
    (stored : ∀x,Source (old x) (fun v g=>DescentSignedCableCodec.encode
       (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) M mem) :
    (Gather.assembly tbl old).Fits w origin ∧ Source (Gather.assembly tbl old)
      (oldWord A native S ready groups host size j) (2^l) mem :=
  signed_source size width pos (Nat.two_pow_pos k) tbl old origin room
    (fun v g x => DescentSignedCableCodec.encode
      (Stage.Prepare.signed A native S ready groups.toEmbedding host x j v g)) mem static stored

end Stage
end
end Hierarchy.DescentGLPacked.BankImage.SignedFields

end OAI
