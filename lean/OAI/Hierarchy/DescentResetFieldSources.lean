import OAI.Hierarchy.DescentPackedFlowWalsh
import OAI.Hierarchy.DescentResetOriginalPlanes
import OAI.Hierarchy.DescentResetFlowColumns

namespace OAI
/-! # The original packed old-census and signed-cable fields of a measured reset -/
namespace Hierarchy.DescentPackedResetSource
open DescentColonies DescentGL DescentPackedWalsh DescentSIMDLookup Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l H b w : ℕ}

theorem dense_of_installed (base : ℕ) (mem : Memory w) (X : Fin H→Block (h+l)→Cell b)
    (words : Installed base (fun v=>shaped (fun z=>X v (address (h+l) ((DescentWalshPhysical.coordinates _).symm z)))) mem) :
    DescentGLPacked.Dense (h:=h) (l:=l) base X mem := by
  rintro ⟨v,t⟩
  let p := (ordinal h).symm (Fin.cast (DescentGLPacked.chunk_count h l) t)
  have ord : (ordinal h p).val=t.val := by simp [p]
  have coord : (DescentSIMDLookup.row H (2^(h+l)) (2^l) (v,t)).val=(DescentPackedWalsh.row v p).val := by
    change t.val+chunks (2^(h+l)) (2^l)*v.val=(ordinal h p).val+2^h*v.val
    exact congrArg₂ Nat.add ord.symm
      (congrArg (fun n : ℕ => n*v.val) (DescentGLPacked.chunk_count h l))
  rw [coord,words]
  apply congrArg (fun r : Cell (b*2^l)=>(r.val:Word w))
  apply congrArg (encode b (2^l))
  funext j
  have range : t.val<2^h := t.isLt.trans_le (DescentGLPacked.chunk_count h l).le
  have live : t.val*2^l+j.val<2^(h+l) := by
    calc _ < t.val*2^l+2^l:=Nat.add_lt_add_left j.isLt _
         _ = (t.val+1)*2^l:=(Nat.succ_mul ..).symm
         _ ≤ 2^h*2^l:=Nat.mul_le_mul_right _ range
         _ = 2^(h+l):=(pow_add 2 h l).symm
  change X v (address _ ((DescentWalshPhysical.coordinates _).symm (addr p ((ordinal l).symm j))))=
    (if ok : t.val*2^l+j.val<2^(h+l) then X v ⟨_,ok⟩ else 0)
  rw [dite_eq_left live]
  apply congrArg (X v)
  apply Fin.ext
  simp only [flat_coordinate,Equiv.apply_symm_apply,ord]

end
end Hierarchy.DescentPackedResetSource

namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentGL DescentSIMDLookup DescentPackedColony DescentPackedWalsh Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i h l H R M short b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => hosts.toEmbedding.trans Fin.valEmbedding
local notation "Q" => A.wire*(A.z*G.b)
local notation "coords" => DescentWalshPhysical.coordinates

set_option maxHeartbeats 1000000 in
theorem stencil_sources (L : DescentPackedFlowPublication.Layout A.degree (2^k) (2*A.cap))
    (room : DescentPackedFlowPublication.Room L H R M short b w)
    (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M) (ok : A.degree<2^short)
    (mem : Memory w)
    (old : ∀s,Reads (L.tokens s) (fun v g=>chips A native S ready rs vs short (groups.symm g) (hosts.symm v) s) M mem)
    (rom : ∀(j : Fin A.degree) x,DescentPackedZip.Static (L.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) Q j.val x) M mem)
    (roster : Mounted L.peers (next A hosts) mem R M)
    (idx : DescentPackedFlowReturn.Header L.header L.middle mem A.degree H R M)
    (loadBase : ℕ) (before : loadBase+H*2^h≤L.first)
    (counts : ∀p : Row H R M,mem (loadBase+(DescentSIMDLookup.row H R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>(A.censusValue hosts.toEmbedding groups false v g x:Cell b))) p).val:Word w))
    (table : DescentPackedZip.Static L.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem) :
    let D:=digits groups size
    ∃dst : Memory w,(DescentPackedFlowPublication.procedure L H R M w).Exec mem dst
      (DescentPackedFlowPublication.duration L H R M) ∧
      DescentGLPacked.Dense (h:=h) (l:=l) loadBase
        (fun v x=>(A.resetLoad D (hosts.symm v) x:Cell b)) dst ∧
      (∀j : Fin A.degree,DescentGLPacked.Dense (h:=h) (l:=l) (L.middle+j.val*L.pitch)
        (fun v x=>(raw A hosts D j v x:Cell b)) dst) ∧
      (∀a<L.first,dst a=mem a) ∧ ∀a,L.middle+A.degree*L.pitch≤a→dst a=mem a := by
  intro D
  obtain ⟨dst,run,pairs,low,high⟩:=walsh_inputs_framed A native S ready groups hosts L room size lanes hm ok mem old rom roster idx table
  have loads:=DescentPackedResetSource.dense_of_installed (h:=h) (l:=l) loadBase mem
    (fun v x=>(A.resetLoad D (hosts.symm v) x:Cell b))
    (walsh_load A S ready groups hosts size lanes hm loadBase mem counts)
  refine ⟨dst,run,?_,fun j=>DescentPackedResetSource.dense_of_installed (h:=h) (l:=l) _ dst
    (fun v x=>(raw A hosts D j v x:Cell b)) (pairs j),low,high⟩
  intro p
  have rowBound := lt_of_lt_of_eq ((DescentSIMDLookup.row H _ _ p).isLt)
    (congrArg (H * ·) (DescentGLPacked.chunk_count h l))
  exact (low _ (by omega)).trans (loads p)

/-- Field order is determined by the public degree and reset bit count.
It does not use any of the values in the previous graph. -/
def fieldBanks (δ h l : ℕ) (counts : ProtocolRAM.Bank) (pair : Fin δ→ProtocolRAM.Bank) (planes : ℕ) :
    Fin ((1+δ)+(h+l))→ProtocolRAM.Bank := fun n=>
  match finSumFinEquiv.symm n with
  | .inl ch=>Sum.elim (fun _=>counts) pair (finSumFinEquiv.symm ch)
  | .inr d=>DescentGLPacked.BankImage.Original.bank planes h d

def fieldValues (size : 2^(h+l)=R*2^k) (pos : 0<b) :
    Fin ((1+A.degree)+(h+l))→Fin H→Block (h+l)→Cell b := fun n=>
  match finSumFinEquiv.symm n with
  | .inl ch=>
    Sum.elim (fun _ v x=>(A.resetLoad (digits groups size) (hosts.symm v) x:Cell b))
      (fun j v x=>(raw A hosts (digits groups size) j v x:Cell b)) (finSumFinEquiv.symm ch)
  | .inr d=>fun _ x=>DescentGLPacked.BankImage.Original.bit pos d x

theorem source_fields (size : 2^(h+l)=R*2^k) (pos : 0<b) (counts : ProtocolRAM.Bank)
    (pair : Fin A.degree→ProtocolRAM.Bank) (planes out : ℕ) (mem : Memory w) (range : H*2^h≤2^w)
    (fit : ∀B,B=counts ∨ (∃j,B=pair j)→B.Fits w out ∧ H*2^h≤B.size)
    (wc : DescentGLPacked.Dense (h:=h) (l:=l) counts.base (fun v x=>(A.resetLoad (digits groups size) (hosts.symm v) x:Cell b)) mem)
    (pf : ∀j,DescentGLPacked.Dense (h:=h) (l:=l) (pair j).base (fun v x=>(raw A hosts (digits groups size) j v x:Cell b)) mem)
    (header : ∀d t,mem ((DescentGLPacked.BankImage.Original.bank planes h d).base+t.val)=
      (DescentGLPacked.BankImage.Original.packed (h:=h) (l:=l) pos d t:Word w)) :
    ∀i,DescentPackedZip.Source (.lookup (fieldBanks A.degree h l counts pair planes i) .row)
      (fieldValues A groups hosts size pos i) (2^l) mem := by
  intro i
  obtain ⟨(ch|d),rfl⟩:=finSumFinEquiv.surjective i
  · obtain ⟨(tag|j),rfl⟩:=finSumFinEquiv.surjective ch
    · simp only [fieldBanks,fieldValues,Equiv.symm_apply_apply,Sum.elim_inl]
      have room:=fit counts (.inl rfl)
      exact DescentPackedZip.source_column counts out room.1 mem _ (by simpa only [DescentGLPacked.chunk_count] using room.2) wc
    · simp only [fieldBanks,fieldValues,Equiv.symm_apply_apply,Sum.elim_inr]
      have room:=fit (pair j) (.inr ⟨j,rfl⟩)
      exact DescentPackedZip.source_column (pair j) out room.1 mem _ (by simpa only [DescentGLPacked.chunk_count] using room.2) (pf j)
  · simp only [fieldBanks,fieldValues,Equiv.symm_apply_apply]
    exact DescentGLPacked.BankImage.Original.source planes pos d mem range (header d)

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
