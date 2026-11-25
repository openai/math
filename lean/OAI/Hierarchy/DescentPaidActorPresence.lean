import OAI.Hierarchy.DescentPaidResidentROM
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # All occupied ordinary actor labels from the physical old and born registers -/
namespace Hierarchy.DescentPaidResidentCount.Presence
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {p n N M H G w : ℕ}

def hits (name : Cell n) (d : Cell (n*N)) : Cell 1 :=
  if name≠0 ∧ ∃i,(encode n N).symm d i=name then 1 else 0

theorem hits_empty (name : Cell n) : hits (N:=N) name 0=0:=by
  have zero : (encode n N).symm 0=fun _=>0:=by
    apply (encode n N).injective;rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change 0=(finFunctionFinEquiv (fun _ : Fin N=>(0:Cell n))).val
    simp []
  by_cases z:name=0
  · simp [hits,z]
  · simp [hits,z,zero,Ne.symm z]

def opcode (name : Cell n) (data : Cell (n*N)) (_ : Cell 0) := hits name data

def directory (names : Fin p→Cell n) (N M : ℕ) (i : Fin (p*2)) : Page :=
  let pair:=finProdFinEquiv.symm i
  binary (opcode (N:=N) (names pair.1)) M pair.2

def pair (i : Fin p) (j : Fin 2) :=finProdFinEquiv (i,j)
def expr (names : Fin p→Cell n) (N M lo : ℕ) (src : Expr) (q : Fin p) :=
  (joined (directory names N M) ((n*N)*M) lo (pair q)).read src (.lit 0)

theorem clear_source (installed : Memory w) :
    Source (.lit 0) (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) M installed:=by
  intro pos
  have blank : DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) pos=0 := by
    apply Fin.ext
    change (DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) pos).val=0
    have small : (DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) pos).val<1:=by
      simpa using (DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(0:Cell 0)) pos).isLt
    omega
  simp [blank,Expr.eval]

theorem original (names : Fin p→Cell n) (data : Fin H→Fin G→Fin N→Cell n)
    (src : Expr) (m : Memory w) (lo out : ℕ) (live : ∀j,names j≠0) (valid : src.Fits w lo)
    (previous : Source src (fun h g=>encode n N (data h g)) M m)
    (apart : lo+(p*2)*2^((n*N)*M)≤out) (space : out+p*(H*chunks G M)<2^w) :
    let book:=directory names N M;let width:=n*N*M
    let es:=List.ofFn (expr names N M lo src);let run:=ProbeStage.Native.columns (H*chunks G M) out es
    let installed:=after book width lo m;let done:=result run installed
    ((mount book width w lo).seq (program w run)).Exec m done ((4+10*((p*2)*2^width))+clock run) ∧
    (∀j (pos : Row H G M),done (out+j.val*(H*chunks G M)+(row H G M pos).val)=
      ((DescentSIMDLookup.data (fun h g=>if ∃i,data h g i=names j then (1:Cell 1) else 0) pos).val:Word w)) ∧
    (∀i,i<lo ∨ out+p*(H*chunks G M)≤ i→done i=m i) ∧ CheapCode ((mount book width w lo).seq (program w run)) := by
  intro book width es jobs installed done
  let tab (q:Fin p):=joined book width lo (pair q)
  have pages (q:Fin p) (j:Fin 2) : book (pair q j)=binary (opcode (N:=N) (names q)) M j:=by simp [book,directory,pair]
  have widthRoom (i:Fin (p*2)):(book i).bits≤width:=by
    obtain ⟨⟨q,j⟩,rfl⟩:=finProdFinEquiv.surjective i
    change (book (pair q j)).bits≤width
    rw [pages q j]
    fin_cases j
    · exact le_rfl
    · change (n*N+0)*M≤n*N*M
      simp
  have early:lo≤out:=(Nat.le_add_right ..).trans apart
  have below:out<2^w:=(Nat.le_add_right ..).trans_lt space
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run book width lo m (apart.trans_lt below)
  have retained:=DescentOrdinaryAtomFieldRAM.ROM.frame book width lo m
  have rom (q:Fin p):Static (tab q) (opcode (N:=N) (names q)) M installed:=
    binary_mounted _ M book width lo m widthRoom (pair q) (pages q)
  have mask (q:Fin p):DescentPackedZip.Fits (tab q) src (.lit 0) (n*N) 0 M out w:=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ early valid,trivial,
      bank_room _ _ _ _ _ (widthRoom _) apart below,bank_room _ _ _ _ _ (widthRoom _) apart below,
      congrArg Page.bits (pages q 0),congrArg Page.bits (pages q 1)⟩
  have fs:∀e∈es,e.Fits w out:=by
    intro e he;obtain ⟨q,rfl⟩:=List.mem_ofFn.mp he
    exact ⟨(mask q).apply,(mask q).right,(mask q).shift,(mask q).left⟩
  have len:es.length=p:=List.length_ofFn
  have low : Source src (fun h g=>encode n N (data h g)) M installed :=by
    intro pos
    exact (eval_below src _ m installed valid (fun i hi=>retained i (Or.inl hi))).trans (previous pos)
  have zeros :=clear_source (H:=H) (G:=G) (M:=M) installed
  have pass : (program w jobs).Exec installed done (clock jobs):=
    @ProbeStage.Native.columns_exec w (H*chunks G M) out es installed
      (ProbeStage.Native.columns_safe es le_rfl fs (by simpa only [len] using space))
  refine ⟨Procedure.Exec.then mounted.1 pass,?_,?_,cheap_seq
    (DescentOrdinaryAtomFieldRAM.ROM.cheap book width w lo) (@ProtocolRAM.program_cheap _ _)⟩
  · intro j pos
    change result (ProbeStage.Native.columns (H*chunks G M) out es) installed
      (out+j.val*(H*chunks G M)+(row H G M pos).val)=_
    rw [ProbeStage.Native.columns_read es installed le_rfl fs j.val (j.isLt.trans_eq len.symm) (row H G M pos)]
    simpa [es,expr,tab,opcode,hits,live] using read_data (tab j) src (.lit 0) out (mask j) (opcode (N:=N) (names j))
      (hits_empty _) installed (rom j) _ (fun _ _=>(0:Cell 0)) low zeros pos
  · intro i away
    have scanAway : i<out ∨ out+es.length*(H*chunks G M) ≤ i :=by
      simpa only [len] using away.imp_left (fun h=>h.trans_le early)
    have top : out≤out+p*(H*chunks G M):=Nat.le_add_right ..
    exact (ProbeStage.Native.columns_frame es installed scanAway).trans
      (retained i (away.imp_right (fun h=>apart.trans (top.trans h))))

end
end Hierarchy.DescentPaidResidentCount.Presence

end OAI
