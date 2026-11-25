import OAI.Hierarchy.DescentPackedCanvasPriming
import OAI.Hierarchy.DescentGLPackedBlocks

namespace OAI
/-! # True packed site and peer traffic registers from one old signed graph image -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentStageEdgeReceipt DescentPackedColony DescentPackedWalsh
open DescentWalshPhysical ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i u l H HP R D M short b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (name : V≃Fin H) (ph : H≤HP) (pd : A.degree≤D)
local notation "m" => u+l
local notation "Q" => A.wire*(A.z*G.b)
local notation "rank" => name.toEmbedding.trans (Fin.castLEEmb ph)

structure Originals (xy : Block m≃J×Block k) (base peer pitch : ℕ) (out : Memory w) : Prop where
  load : DescentGLPacked.Dense (h:=u) (l:=l) base
    (fun (v:Fin HP) z=>(Padded.load A name xy v z:Cell b)) out
  flow (j:Fin D) : DescentGLPacked.Dense (h:=u) (l:=l) (peer+j.val*pitch)
    (fun (v:Fin HP) z=>(Padded.flow A name xy j v z:Cell b)) out

theorem Originals.keep (xy : Block m≃J×Block k) (base peer pitch : ℕ) (old mid : Memory w)
    (source : Originals (b:=b) (HP:=HP) (D:=D) A name xy base peer pitch old)
    (preserve : ∀z, (base≤z ∧ z<base+HP*2^u) ∨ (peer≤z ∧ z<peer+D*pitch)→mid z=old z)
    (space : HP*2^u≤pitch) : Originals (b:=b) (HP:=HP) (D:=D) A name xy base peer pitch mid := by
  have length : chunks (2^m) (2^l)=2^u:=by
    have eq:=chunks_group (2^u) 1 (2^l) (by decide) (Nat.two_pow_pos _)
    simpa [pow_add,chunks,ThreeFlat.Routing.poolBatchCount] using eq
  constructor
  · intro p;have lt:=(DescentSIMDLookup.row HP (2^m) (2^l) p).isLt.trans_le (Nat.mul_le_mul_left HP length.le)
    exact (preserve _ (.inl ⟨Nat.le_add_right ..,by omega⟩)).trans (source.load p)
  · intro j p
    have lt:=(DescentSIMDLookup.row HP (2^m) (2^l) p).isLt.trans_le (Nat.mul_le_mul_left HP length.le)
    have tail:=Nat.mul_le_mul_right pitch j.isLt;rw [Nat.succ_mul] at tail
    exact (preserve _ (.inr ⟨by omega,by omega⟩)).trans (source.flow j p)

theorem Originals.walsh (xy : Block m≃J×Block k) (base peer pitch : ℕ) (mem : Memory w)
    (old : Originals (b:=b) (HP:=HP) (D:=D) A name xy base peer pitch mem) :
    Installed (H:=HP) base (fun v=>shaped (fun z=>(Padded.load A name xy v (address m ((coordinates _).symm z)):Cell b))) mem ∧
    ∀j:Fin D,Installed (H:=HP) (peer+j.val*pitch) (fun v=>shaped
      (fun z=>(Padded.flow A name xy j v (address m ((coordinates _).symm z)):Cell b))) mem :=
  ⟨DescentPackedResetSource.installed (h:=u) (l:=l) (b:=b) base mem
      (fun (v:Fin HP) z=>(Padded.load A name xy v z:Cell b)) old.load,
    fun j=>DescentPackedResetSource.installed (h:=u) (l:=l) (b:=b) (peer+j.val*pitch) mem
      (fun (v:Fin HP) z=>(Padded.flow A name xy j v z:Cell b)) (old.flow j)⟩

include pd in
theorem original_sources (L : DescentPackedFlowPublication.Layout D (2^k) (2*A.cap))
    (room : DescentPackedFlowPublication.Room L HP R M short b w) (size : 2^m=R*2^k)
    (lanes : 2^l=M*2^k) (hm : 0<M) (ok : A.degree<2^short) (base : ℕ) (mem : Memory w)
    (gap : L.middle+D*L.pitch≤base)
    (old : ∀s,Reads (L.tokens s) (fun (v:Fin HP) g=>Padded.tokens A native S ready groups name short v g s) M mem)
    (rom : ∀(j : Fin D) x,DescentPackedZip.Static (L.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) Q j.val x) M mem)
    (links : Mounted L.peers (Padded.roster A name ph) mem R M)
    (idx : DescentPackedFlowReturn.Header L.header L.middle mem D HP R M)
    (table : DescentPackedZip.Static L.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem)
    (census : ∀p : Row HP R M,mem (base+(DescentSIMDLookup.row HP R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>(A.censusValue rank groups false v g x:Cell b))) p).val:Word w)) :
    ∃out : Memory w,(DescentPackedFlowPublication.procedure L HP R M w).Exec mem out
      (DescentPackedFlowPublication.duration L HP R M) ∧
      Originals (HP:=HP) (D:=D) (b:=b) A name (digits groups size) base L.middle L.pitch out ∧
      ∀a,(a<L.first ∨ L.middle+D*L.pitch≤a)→ out a=mem a := by
  obtain ⟨out,ran,pair,lo,hi⟩:=Padded.walsh_inputs A native S ready groups name ph pd L room size lanes hm ok
    mem old rom links idx table
  have site:=Padded.walsh_load A S ready groups name ph size lanes hm base out
    (fun p=>(hi _ (gap.trans (Nat.le_add_right ..))).trans (census p))
  exact ⟨out,ran,⟨DescentPackedResetSource.original _ _ _ site,fun j=>DescentPackedResetSource.original _ _ _ (pair j)⟩,
    fun a h=>h.elim (lo a) (hi a)⟩

theorem mounted_resident (H b root lim : ℕ) (axes : List (Axis u l)) (initial old mid : Memory w)
    (stamped : ∀a<lim,old a=mounted H b root axes initial a)
    (kept : ∀a,root≤a→a<root+axes.length*span H u l b→mid a=old a) :
    ∀a<lim,mid a=mounted H b root axes mid a := by
  intro a small
  by_cases fromRoot : root≤a
  · cases j : axes[(a-root)/span H u l b]? with
    | none=>simp [mounted,fromRoot,j]
    | some g=>
      have within : (a-root)/span H u l b<axes.length:=by
        by_contra! far;rw [List.getElem?_eq_none_iff.mpr far] at j;contradiction
      have positive : 0<span H u l b:=by unfold span;positivity
      have abs:= (Nat.div_lt_iff_lt_mul positive).mp within
      have same:=kept a fromRoot (by omega)
      simpa only [mounted,ite_eq_left fromRoot,j] using same.trans (stamped a small)
  · simp [mounted,fromRoot]

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
