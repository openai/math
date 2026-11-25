import OAI.Hierarchy.DescentResetFieldSources
import OAI.Hierarchy.DescentResetFieldReturn

namespace OAI
/-! # One measured reset for all original channels and coordinate planes -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGLPacked DescentGLPacked.BankImage DescentGL DescentGLNielsen DescentColonies DescentSIMDLookup
open DescentStageEdgeReceipt DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D h l k H R M short b w N cap : ℕ}

def channelTerm {D : ℕ} (bank : Fin D→Bank) (j : ℕ) : Expr :=
  if live:j<D then .lookup (bank ⟨j,live⟩) .row else .lit 0

namespace Channels

def values (loads : Fin H→Block (h+l)→Cell b) (pairs : Fin D→Fin H→Block (h+l)→Cell b) (pos : 0<b) :
    Fin ((1+D)+(h+l))→Fin H→Block (h+l)→Cell b := fun n v x=>
  match finSumFinEquiv.symm n with
  | .inl ch=>Sum.elim (fun _=>loads v x) (fun j=>pairs j v x) (finSumFinEquiv.symm ch)
  | .inr d=>Original.bit pos d x

theorem source (loads : Fin H→Block (h+l)→Cell b) (pairs : Fin D→Fin H→Block (h+l)→Cell b) (pos : 0<b)
    (counts : Bank) (pair : Fin D→Bank) (planes out : ℕ) (mem : Memory w) (range : H*2^h≤2^w)
    (fit : ∀B,B=counts ∨ (∃j,B=pair j)→B.Fits w out ∧ H*2^h≤B.size)
    (wc : Dense (h:=h) (l:=l) counts.base loads mem)
    (pf : ∀j,Dense (h:=h) (l:=l) (pair j).base (pairs j) mem)
    (header : ∀d t,mem ((Original.bank planes h d).base+t.val)=(Original.packed (h:=h) (l:=l) pos d t:Word w)) :
    ∀i,DescentPackedZip.Source (.lookup (fieldBanks D h l counts pair planes i) .row)
      (values loads pairs pos i) (2^l) mem := by
  intro i
  obtain ⟨(ch|d),rfl⟩:=finSumFinEquiv.surjective i
  · obtain ⟨(tag|j),rfl⟩:=finSumFinEquiv.surjective ch
    · unfold values
      simp only [fieldBanks,Equiv.symm_apply_apply,Sum.elim_inl]
      have room:=fit counts (.inl rfl)
      exact DescentPackedZip.source_column counts out room.1 mem _ (by simpa only [DescentGLPacked.chunk_count] using room.2) wc
    · unfold values
      simp only [fieldBanks,Equiv.symm_apply_apply,Sum.elim_inr]
      have room:=fit (pair j) (.inr ⟨j,rfl⟩)
      exact DescentPackedZip.source_column (pair j) out room.1 mem _ (by simpa only [DescentGLPacked.chunk_count] using room.2) (pf j)
  · unfold values
    simp only [fieldBanks,Equiv.symm_apply_apply]
    exact DescentGLPacked.BankImage.Original.source planes pos d mem range (header d)

local notation "channels" => (1+D)+(h+l)

theorem after_data (C : BankImage.Chart) (valid : Size C (channels*H) h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l)↪Fin N)
    (key : Expr) (μ : DescentGL.Layout (h+l)) (keyRoom : DescentGLControlCode.fits T key w C.input.base)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size) (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (mem : Memory w) (static : DescentGLControlCode.installed T name mem)
    (choice : ∀s : Fin (DescentGLControlCode.Count (h+l)),key.eval mem (s.val:Word w)=((name μ).val:Word w))
    (counts : Bank) (pair : Fin D→Bank) (loads : Fin H→Block (h+l)→Cell b) (pairs : Fin D→Fin H→Block (h+l)→Cell b)
    (wc : Dense (h:=h) (l:=l) counts.base loads mem) (pf : ∀j,Dense (h:=h) (l:=l) (pair j).base (pairs j) mem)
    (countRoom : counts.Fits w C.input.base ∧ H*2^h≤counts.size)
    (pairRoom : ∀i,(pair i).Fits w C.input.base ∧ H*2^h≤(pair i).size)
    (plane : ℕ) (positive : 0<b) (planeRoom : ∀d : Fin (h+l),(Original.bank plane h d).Fits w C.input.base)
    (fixed : ∀j z,mem ((Original.bank plane h j).base+z.val)=(Original.packed (h:=h) (l:=l) positive j z:Word w))
    (gap : C.input.base+C.input.size≤C.flags)
    (statGL : ∀s : Slot (h+l),∀i : Fin C.page,mem (addr C (s,i))=literal (channels*H) h l b w s i.val) :
    let banks:=fieldBanks D h l counts pair plane
    let rows:=H*2^h
    let n:=(schedule (h+l)).length
    let gs:=DescentPackedFlowBatch.passes C.input.base rows rows (channelTerm banks) 0 channels
    let basis:=steps (C.chosen (h+l)) (channels*H) (2^h) 0 n
    let network:=(program w gs).seq ((scan w C.flags n (T.expr key)).seq (program w basis))
    ∃dst,network.Exec mem dst (clock gs+((4+n*(2*(T.expr key).work+4))+clock basis)) ∧ CheapCode network ∧
      (∀d,Dense (h:=h) (l:=l) (slice (((C.chosen (h+l)).bank n).base) H (2^h) d)
        (fun v x=>values loads pairs positive d v ((rearrange μ).symm x)) dst) ∧
      ∀a,a<C.input.base ∨ C.heap (h+l)+n*C.page≤a→dst a=mem a := by
  let banks:=fieldBanks D h l counts pair plane
  have actual:=source loads pairs positive counts pair plane C.input.base mem (countRoom.2.trans countRoom.1.2.1.le)
    (fun B hB=>by rcases hB with rfl|⟨j,rfl⟩;exact countRoom;exact pairRoom j) wc pf fixed
  have fits (j : ℕ) (live : j<channels) : (channelTerm banks j).Fits w C.input.base := by
    let i : Fin channels:=⟨j,live⟩
    suffices f:(banks i).Fits w C.input.base by simp only [channelTerm,dite_eq_left live,Expr.Fits];exact ⟨f,trivial⟩
    obtain ⟨(a|d),eq⟩:=finSumFinEquiv.surjective i
    · obtain ⟨(s|t),rfl⟩:=finSumFinEquiv.surjective a
      · simpa [banks,fieldBanks,←eq] using countRoom.1
      · simpa [banks,fieldBanks,←eq] using (pairRoom t).1
    · simpa [banks,fieldBanks,←eq] using planeRoom d
  exact gather_and_reset C valid T name key μ (values loads pairs positive)
    (channelTerm banks) mem fits keyRoom off area static choice
    (fun d=>by simpa only [channelTerm,dite_eq_left d.isLt] using actual d) gap statGL

theorem execute (L : DescentPackedFlowPublication.Layout D (2^k) cap)
    (room : DescentPackedFlowPublication.Room L H R M short b w)
    (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M)
    (mem mid : Memory w) (counts : Bank)
    (loads : Fin H→Block (h+l)→Cell b) (pairs : Fin D→Fin H→Block (h+l)→Cell b)
    (issued : (DescentPackedFlowPublication.procedure L H R M w).Exec mem mid (DescentPackedFlowPublication.duration L H R M))
    (wc : Dense (h:=h) (l:=l) counts.base loads mid)
    (pf : ∀j : Fin D,Dense (h:=h) (l:=l) (L.middle+j.val*L.pitch) (pairs j) mid)
    (low : ∀a<L.first,mid a=mem a) (high : ∀a,L.middle+D*L.pitch≤a→mid a=mem a)
    (C : BankImage.Chart) (valid : Size C (channels*H) h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l)↪Fin N)
    (key : Expr) (μ : DescentGL.Layout (h+l)) (keyRoom : DescentGLControlCode.fits T key w L.first)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size) (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (static : DescentGLControlCode.installed T name mem)
    (choice : ∀s : Fin (DescentGLControlCode.Count (h+l)),key.eval mem (s.val:Word w)=((name μ).val:Word w))
    (plane : ℕ) (positive : 0<b) (planeEnd : plane+(h+l)*2^h≤L.first)
    (fixed : ∀j z,mem ((Original.bank plane h j).base+z.val)=(Original.packed (h:=h) (l:=l) positive j z:Word w))
    (countSize : H*2^h≤counts.size) (countFit : counts.Fits w C.input.base)
    (afterPairs : L.middle+D*L.pitch≤C.input.base)
    (gap : C.input.base+C.input.size≤C.flags)
    (statGL : ∀s : Slot (h+l),∀i : Fin C.page,mem (addr C (s,i))=literal (channels*H) h l b w s i.val) :
    let pair:=fun j : Fin D=>(⟨L.middle+j.val*L.pitch,L.bits⟩:Bank)
    let banks:=fieldBanks D h l counts pair plane
    let rows:=H*2^h
    let n:=(schedule (h+l)).length
    let gs:=DescentPackedFlowBatch.passes C.input.base rows rows (channelTerm banks) 0 channels
    let basis:=steps (C.chosen (h+l)) (channels*H) (2^h) 0 n
    let network:=(DescentPackedFlowPublication.procedure L H R M w).seq
      ((program w gs).seq ((scan w C.flags n (T.expr key)).seq (program w basis)))
    ∃dst,network.Exec mem dst (DescentPackedFlowPublication.duration L H R M+
      (clock gs+((4+n*(2*(T.expr key).work+4))+clock basis))) ∧
      (∀d,Dense (h:=h) (l:=l) (slice (((C.chosen (h+l)).bank n).base) H (2^h) d)
        (fun v x=>values loads pairs positive d v ((rearrange μ).symm x)) dst) ∧
      ∀a,a<L.first ∨ C.heap (h+l)+n*C.page≤a→dst a=mem a := by
  let pair:=fun j : Fin D=>(⟨L.middle+j.val*L.pitch,L.bits⟩:Bank)
  let banks:=fieldBanks D h l counts pair plane
  have topo:L.first≤L.middle:=Nat.le_add_right ..
  have lower:L.first≤C.input.base:=by omega
  have hstart:C.input.base≤C.flags:=by omega
  have hshape:=valid.controls
  have cap:=valid.top
  have heap:C.start≤C.heap (h+l):=Nat.le_add_right ..
  have rowSmall:H*2^h<2^w:=countSize.trans_lt countFit.2.1
  have ch : chunks R M=2^h := by
    have head:=DescentSIMDLookup.chunks_group R M (2^k) hm (Nat.two_pow_pos _)
    rw [←size,←lanes,DescentGLPacked.chunk_count] at head
    exact head.symm
  have pairRoom : ∀i : Fin D,(pair i).Fits w C.input.base ∧ H*2^h≤(pair i).size := by
    intro i
    have stop:=Nat.mul_le_mul_right L.pitch i.isLt
    rw [Nat.succ_mul] at stop
    have pitchFit : L.pitch<2^w:=by have :=room.small;omega
    exact ⟨⟨Nat.two_pow_pos _,pitchFit,by dsimp [pair,Bank.size,DescentPackedFlowPublication.Layout.pitch] at *;omega⟩,
      by simpa [pair,Bank.size,DescentPackedFlowPublication.Layout.pitch,ch] using room.pitch⟩
  have keyRoom' : DescentGLControlCode.fits T key w C.input.base :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lower keyRoom.1,
      ⟨keyRoom.2.1.1,keyRoom.2.1.2.1,keyRoom.2.1.2.2.trans lower⟩,
      ⟨keyRoom.2.2.1,keyRoom.2.2.2.1,keyRoom.2.2.2.2.trans lower⟩⟩
  have keyRead (s : Fin (DescentGLControlCode.Count (h+l))) := (eval_below key (s.val:Word w) mem mid keyRoom.1 low).trans (choice s)
  have tables : DescentGLControlCode.installed T name mid :=
    ⟨fun s=>(low _ (by have :=s.isLt;have :=keyRoom.2.1.2.2;omega)).trans (static.1 s),
     fun j=>(low _ (by have :=j.isLt;have :=keyRoom.2.2.2.2;omega)).trans (static.2 j)⟩
  have planeStop (j : Fin (h+l)) (z : Fin (2^h)) : (Original.bank plane h j).base+z.val<L.first := by
    have bound:=Nat.mul_le_mul_right (2^h) j.isLt
    rw [Nat.succ_mul] at bound
    have :=z.isLt
    dsimp [Original.bank];omega
  have shared (j : Fin (h+l)) (z : Fin (2^h)) :=
    (low _ (planeStop j z)).trans (fixed j z)
  have planeRoom (d : Fin (h+l)) : (Original.bank plane h d).Fits w C.input.base := by
    have small:=Nat.mul_le_mul_right (2^h) d.isLt
    rw [Nat.succ_mul] at small
    have narrow : 2^h<2^w := by have :=d.isLt;have :=planeEnd;have :=room.small;omega
    exact ⟨Nat.two_pow_pos _,narrow,by dsimp [Original.bank,Bank.size];omega⟩
  have charts (s : Slot (h+l)) (j : Fin C.page) :
      mid (addr C (s,j))=literal (channels*H) h l b w s j.val := by
    have offset:C.start≤addr C (s,j):=by dsimp [addr,Chart.base];omega
    exact (high _ (by omega)).trans (statGL s j)
  obtain ⟨dst,run,_,reads,frame⟩:=after_data C valid T name key μ keyRoom' off area mid tables keyRead
    counts pair loads pairs wc pf ⟨countFit,countSize⟩ pairRoom plane positive planeRoom shared gap charts
  refine ⟨dst,issued.then run,reads,?_⟩
  intro a f
  rcases f with lo|hi
  · exact (frame a (.inl (lo.trans_le lower))).trans (low a lo)
  · exact (frame a (.inr hi)).trans (high a (by omega))

end Channels
end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
