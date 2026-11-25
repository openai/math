import OAI.Hierarchy.DescentResetStemMuxROM
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # One shared descriptor dictionary followed by every actor ticket column -/
namespace Hierarchy.DescentResetStemIssuer
open DescentSIMDLookup DescentPackedZip DescentResetStemMux Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {Q K a b M H G w : ℕ} (base : ℕ) (key : Fin Q→Expr) (heads : Fin Q→Fin K→Expr)
local notation "selector" => tableFor K a b M base
local notation "foldTable" => mergeTable K a b M base

def fields (a b M : ℕ) := List.ofFn (fun q=>assemble (tableFor K a b M base)
  (mergeTable K a b M base) (key q) (heads q))

def code (a b M H G w out : ℕ) :=
  (Book.install (gates K a b) (unit a b) M w base).seq
    (ProtocolRAM.program w (ProbeStage.Native.columns (H*chunks G M) out (fields base key heads a b M)))

def ticks (a b M H G out : ℕ) :=
  (4+10*words K a b M)+clock (ProbeStage.Native.columns (H*chunks G M) out (fields base key heads a b M))

def output (a b M H G out : ℕ) (m : Memory w) :=
  result (ProbeStage.Native.columns (H*chunks G M) out (fields base key heads a b M))
    (Book.image (gates K a b) (unit a b) M base m)

theorem run (out : ℕ) (x : Fin Q→Fin H→Fin G→Cell a) (v : Fin Q→Fin K→Fin H→Cell b)
    (m : Memory w) (keys : ∀q,(key q).Fits w base) (header : ∀q i,(heads q i).Fits w base)
    (issued : ∀q,Source (key q) (x q) M m)
    (printed : ∀q i,Source (heads q i) (fun h (_ : Fin G)=>v q i h) M m)
    (beyond : base+words K a b M≤out) (room : out+Q*(H*chunks G M)<2^w) :
    let last:=output base key heads a b M H G out m
    (code base key heads a b M H G w out).Exec m last (ticks base key heads a b M H G out) ∧
    (∀q : Fin Q,∀p : Row H G M,
      last (out+q.val*(H*chunks G M)+(row H G M p).val)=
        ((data (fun h g=>pick (x q h g) (fun i=>v q i h)) p).val:Word w)) ∧
    (∀u,u<base ∨ base+words K a b M≤u→u<out ∨ out+Q*(H*chunks G M)≤u→last u=m u) ∧
    CheapCode (code base key heads a b M H G w out) := by
  let n:=H*chunks G M
  let es:=fields base key heads a b M
  let mid:=Book.image (gates K a b) (unit a b) M base m
  have count : es.length=Q := List.length_ofFn
  have limit : out<2^w := (Nat.le_add_right ..).trans_lt room
  obtain ⟨mountCPU,switches,combine,frame,cheap⟩:=
    DescentResetStemMux.mount K a b M base m (beyond.trans_lt limit)
  obtain ⟨selectFit,joinFit⟩:=geometry K a b M base out w beyond limit
  have lower : base≤out := (Nat.le_add_right ..).trans beyond
  have fits (q : Fin Q) : DescentResetStemMux.Fits selector foldTable (key q) (heads q) a b M w out :=
    ⟨selectFit,joinFit,ProtocolRAMGeneratedWrite.fits_mono _ lower (keys q),
      fun i=>ProtocolRAMGeneratedWrite.fits_mono _ lower (header q i)⟩
  have keep (e : Expr) (r : Word w) (efit : e.Fits w base) : e.eval mid r=e.eval m r :=
    eval_below e r m mid efit (fun u hu=>frame u (.inl hu))
  have loaded (q : Fin Q) : Loaded selector foldTable (key q) (heads q) (x q) (v q) M mid :=
    ⟨switches,combine,fun p=>(keep _ _ (keys q)).trans (issued q p),
      fun i p=>(keep _ _ (header q i)).trans (printed q i p)⟩
  have all : ∀e∈es,e.Fits w out := by
    intro e inside
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp inside
    exact assemble_fits _ _ _ _ (fits q)
  have tailCPU : (ProtocolRAM.program w (ProbeStage.Native.columns n out es)).Exec mid
      (result (ProbeStage.Native.columns n out es) mid) (clock (ProbeStage.Native.columns n out es)) :=
    ProbeStage.Native.columns_exec es mid
      (ProbeStage.Native.columns_safe (n:=n) es (le_refl out) all (by simpa only [count] using room))
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then mountCPU tailCPU machine pc reg pub exit rom advice cfg raw enter same,?_,?_,@cheap_seq w _ _ (@cheap) (@program_cheap w (ProbeStage.Native.columns n out es))⟩
  · intro q p
    have inRange : q.val<es.length := by rw [count];exact q.isLt
    have written:=ProbeStage.Native.columns_read (n:=n) es mid (le_refl out) all q.val inRange (row H G M p)
    have field : es[q.val]'inRange=assemble selector foldTable (key q) (heads q) := by
      simp only [es,fields,List.getElem_ofFn]
    rw [field] at written
    exact written.trans (read _ _ _ _ (fits q) (x q) (v q) mid (loaded q) p)
  · intro u left right
    exact (ProbeStage.Native.columns_frame es mid (by simpa only [count] using right)).trans (frame u left)

theorem any (out : ℕ) (m : Memory w) (keys : ∀q,(key q).Fits w base)
    (header : ∀q i,(heads q i).Fits w base)
    (beyond : base+words K a b M≤out) (room : out+Q*(H*chunks G M)<2^w) :
    let last:=output base key heads a b M H G out m
    (code base key heads a b M H G w out).Exec m last (ticks base key heads a b M H G out) ∧
    (∀u,u<base ∨ base+words K a b M≤u→u<out ∨ out+Q*(H*chunks G M)≤u→last u=m u) ∧
    CheapCode (code base key heads a b M H G w out) := by
  let n:=H*chunks G M
  let es:=fields base key heads a b M
  let mid:=Book.image (gates K a b) (unit a b) M base m
  have count : es.length=Q := List.length_ofFn
  have limit : out<2^w := (Nat.le_add_right ..).trans_lt room
  obtain ⟨mountCPU,_,_,frame,cheap⟩:=
    DescentResetStemMux.mount K a b M base m (beyond.trans_lt limit)
  obtain ⟨selectFit,joinFit⟩:=geometry K a b M base out w beyond limit
  have lower : base≤out := (Nat.le_add_right ..).trans beyond
  have fits (q : Fin Q) : DescentResetStemMux.Fits selector foldTable (key q) (heads q) a b M w out :=
    ⟨selectFit,joinFit,ProtocolRAMGeneratedWrite.fits_mono _ lower (keys q),
      fun i=>ProtocolRAMGeneratedWrite.fits_mono _ lower (header q i)⟩
  have all : ∀e∈es,e.Fits w out := by
    intro e inside
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp inside
    exact assemble_fits _ _ _ _ (fits q)
  have tailCPU : (ProtocolRAM.program w (ProbeStage.Native.columns n out es)).Exec mid
      (result (ProbeStage.Native.columns n out es) mid) (clock (ProbeStage.Native.columns n out es)) :=
    ProbeStage.Native.columns_exec es mid
      (ProbeStage.Native.columns_safe (n:=n) es (le_refl out) all (by simpa only [count] using room))
  refine ⟨by
    intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then mountCPU tailCPU machine pc reg pub exit rom advice cfg raw enter same,?_,@cheap_seq w _ _ (@cheap) (@program_cheap w (ProbeStage.Native.columns n out es))⟩
  · intro u left right
    exact (ProbeStage.Native.columns_frame es mid (by simpa only [count] using right)).trans (frame u left)

theorem clock_bound (a b M H G out U V : ℕ)
    (keys : ∀q,(key q).work≤U) (headers : ∀q i,(heads q i).work≤V) :
    ticks base key heads a b M H G out ≤ (4+10*words K a b M)+
      (4+Q*(4+(H*chunks G M)*(2*(1+K*(U+V+22))+4))) := by
  apply Nat.add_le_add_left
  apply le_trans (ProbeStage.Native.columns_clock _ _ (1+K*(U+V+22)) _ ?_)
  · simp only [fields,List.length_ofFn,le_refl]
  · intro e has
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp has
    apply (work_le _ _ _ _ V (headers q)).trans
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by have h:=keys q;omega)) 1

theorem names_bound (a b M H G w out U V : ℕ)
    (keys : ∀q,(key q).work≤U) (headers : ∀q i,(heads q i).work≤V) :
    DescentStaticWordColumn.names (code base key heads a b M H G w out)≤
      15*(words K a b M+1)+(15+Q*(11+4*(1+K*(U+V+22)))) := by
  rw [code,DescentStaticWordColumn.names_seq,DescentResetStemMux.names]
  apply Nat.add_le_add_left
  apply le_trans (ProbeStage.Native.columns_text _ _ _ (1+K*(U+V+22)) _ ?_)
  · simp only [fields,List.length_ofFn,le_refl]
  · intro e has
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp has
    apply (work_le _ _ _ _ V (headers q)).trans
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by have h:=keys q;omega)) 1


end
end Hierarchy.DescentResetStemIssuer

end OAI
