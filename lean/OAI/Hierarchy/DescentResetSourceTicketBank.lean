import OAI.Hierarchy.DescentResetSourceTicketCompare
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # A single reset ticket comparison table and the full host-major query range -/
namespace Hierarchy.DescentResetSourceTicketBank
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare DescentResetSignedScan DescentColonies.SplitRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentPackedSumWords (eval_sum)
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w root b paid M H G X K : ℕ}

def span (b M : ℕ) := (b*5+b*5)*M
def start (root b M : ℕ) := root+2*2^(span b M)
def column (root b M H G K x j : ℕ) : Bank :=
  ⟨start root b M+(x*K+j)*(H*chunks G M),Nat.clog 2 (H*chunks G M)⟩
def endAddress (root b M H G X K : ℕ) :=
  start root b M+(X*K)*(H*chunks G M)+2^(Nat.clog 2 (H*chunks G M))
def Room (w root b M H G X K : ℕ) := endAddress root b M H G X K<2^w

variable (prior : ℕ→ℕ→Bool)

def pages (b paid M : ℕ) := binary (scanLaw prior b paid) M
def comparison (root b paid M : ℕ) := joined (pages prior b paid M) (span b M) root id
def expr (root b paid M : ℕ) (q : Expr) (items : Fin (K+K)→Expr) :=
  total (fun i=>(comparison prior root b paid M).read q (items i)) (List.finRange (K+K))
def expressions (root b paid M : ℕ) (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr) :=
  List.ofFn fun t : Fin (X*K)=>let z:=finProdFinEquiv.symm t;expr prior root b paid M (qs z.1 z.2) (items z.1)
def passes (root b paid M H G : ℕ) (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr) :=
  ProbeStage.Native.columns (H*chunks G M) (start root b M) (expressions prior root b paid M qs items)

theorem column_fits (room : Room w root b M H G X K) (x : Fin X) (j : Fin K) :
    (column root b M H G K x.val j.val).Fits w (endAddress root b M H G X K) := by
  have i : x.val*K+j.val<X*K := by
    have h:=(finProdFinEquiv (x,j)).isLt
    simpa only [finProdFinEquiv_apply_val,Nat.mul_comm K,Nat.add_comm] using h
  let n:=H*chunks G M
  let pad:=2^(Nat.clog 2 n)
  have leq:=Nat.mul_le_mul_right n i.le
  change 0<pad ∧ pad<2^w ∧ start root b M+(x.val*K+j.val)*n+pad≤ start root b M+(X*K)*n+pad
  change start root b M+(X*K)*n+pad<2^w at room
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

structure Sources (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr)
    (f : Fin X→Fin H→Fin G→Fields K b) (M : ℕ) (mem : Memory w) : Prop where
  asked : ∀x j,Source (qs x j) (fun h g=>encode b 5 (literal b (DescentResetSourceTicketCompare.asked (f x h g) j))) M mem
  located : ∀x i,Source (items x i) (fun h g=>encode b 5 (literal b (operands (f x h g) i))) M mem

private theorem page_bits (b paid M : ℕ) (i : Fin 2) : ((pages prior b paid M) i).bits≤ span b M := by
  fin_cases i
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · rfl

private theorem pair_fit (e a : Expr) (eq : e.Fits w root) (ea : a.Fits w root)
    (small : start root b M<2^w) : DescentPackedZip.Fits (comparison prior root b paid M) e a
        (b*5) (b*5) M (start root b M) w := by
  have early : root≤ start root b M:=Nat.le_add_right ..
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ early eq,ProtocolRAMGeneratedWrite.fits_mono _ early ea,
    bank_room _ _ _ _ _ (page_bits prior b paid M 0) le_rfl small,
    bank_room _ _ _ _ _ (page_bits prior b paid M 1) le_rfl small,rfl,rfl⟩

private theorem entry (x : Fin X) (j : Fin K) (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr)
    (f : Fin X→Fin H→Fin G→Fields K b) (mem : Memory w) (qFit : ∀x j,(qs x j).Fits w root)
    (iFit : ∀x i,(items x i).Fits w root) (pos : 1<2^b) (src : Sources qs items f M mem)
    (static : Static (comparison prior root b paid M) (scanLaw prior b paid) M mem) (small : start root b M<2^w)
    (cap : ∀h g,(∑i,feeAt prior (f x h g) j i)<2^paid) :
    (expr prior root b paid M (qs x j) (items x)).Fits w (start root b M) ∧
    Source (expr prior root b paid M (qs x j) (items x)) (fun h g=>⟨∑i,feeAt prior (f x h g) j i,cap h g⟩ : Fin H→Fin G→Cell paid) M mem := by
  let t:=comparison prior root b paid M
  let u:=fun h g=>DescentResetSourceTicketCompare.asked (f x h g) j
  let v:=fun i h g=>operands (f x h g) i
  have fit i:=pair_fit prior (paid:=paid) (qs x j) (items x i) (qFit x j) (iFit x i) small
  have fits i : (t.read (qs x j) (items x i)).Fits w (start root b M):=by
    have h:=fit i
    exact ⟨h.apply,h.right,h.shift,h.left⟩
  have vf (i : Fin (K+K)) (h g) : DescentResetSignedScan.Fits b (v i h g):=by
    refine Fin.addCases (motive:=fun z=>DescentResetSignedScan.Fits b (v z h g)) ?_ ?_ i
    · intro z;simpa [v,operands] using (word_fits (f x h g) z pos).2 false
    · intro z;simpa only [v,operands,Fin.addCases_right] using (word_fits (f x h g) z pos).2 true
  have uf h g : DescentResetSignedScan.Fits b (u h g):=(word_fits (f x h g) j pos).1
  have fitsSum (h g) : (∑i,faceCost prior (u h g) (v i h g))<2^paid :=
    (exactFaces prior (f x h g) j).trans_lt (cap h g)
  have same : totalWord prior u v fitsSum=(fun h g=>⟨_,cap h g⟩ : Fin H→Fin G→Cell paid):=by
    funext h g;exact Fin.ext (exactFaces prior (f x h g) j)
  refine ⟨fits_total _ fits _,?_⟩
  intro p
  have rd (i : Fin (K+K)) :
      (t.read (qs x j) (items x i)).eval mem ((row H G M p).val:Word w) =
        ((data (fun h g=>((faceCost prior (u h g) (v i h g):ℕ):Cell paid)) p).val:Word w) := by
    have eqn:=read_data t (qs x j) (items x i) _ (fit i) (scanLaw prior b paid) (scanEmpty prior b paid) mem static
      (fun h g=>encode b 5 (literal b (u h g))) (fun h g=>encode b 5 (literal b (v i h g)))
      (src.asked x j) (src.located x i) p
    simpa only [scanLaw,unpack_literal _ _ (uf _ _),unpack_literal _ _ (vf _ _ _)] using eqn
  have sums:=eval_sum _ _ mem _ rd (List.finRange (K+K))
  rw [←List.ofFn_eq_map,List.sum_ofFn,sumCells prior u v fitsSum,same] at sums
  exact sums

/-- Run all local-slot comparisons in order against the same immutable pair
of lookup pages, each operand coming from an earlier authenticated column. -/
theorem resident (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr)
    (f : Fin X→Fin H→Fin G→Fields K b) (mem : Memory w) (qFit : ∀x j,(qs x j).Fits w root)
    (iFit : ∀x i,(items x i).Fits w root) (pos : 1<2^b) (src : Sources qs items f M mem)
    (static : Static (comparison prior root b paid M) (scanLaw prior b paid) M mem)
    (cap : ∀x j h g,(∑i,feeAt prior (f x h g) j i)<2^paid) (room : Room w root b M H G X K) :
    let ps:=passes prior root b paid M H G qs items
    let dst:=result ps mem
    (program w ps).Exec mem dst (clock ps) ∧ CheapCode (program w ps) ∧
    (∀x j,Reads (column root b M H G K x.val j.val) (fun h g=>⟨∑i,feeAt prior (f x h g) j i,cap x j h g⟩ : Fin H→Fin G→Cell paid) M dst) ∧
    ∀a,a<start root b M ∨ endAddress root b M H G X K≤a→dst a=mem a := by
  intro ps dst
  let es:=expressions prior root b paid M qs items
  let n:=H*chunks G M
  have len : es.length=X*K:=by simp [es,expressions]
  have top : start root b M+es.length*n<2^w:=by
    change start root b M+(X*K)*n+2^Nat.clog 2 n<2^w at room
    rw [len]
    exact (Nat.le_add_right ..).trans_lt room
  have small : start root b M<2^w:=(Nat.le_add_right ..).trans_lt top
  have all x j :=entry prior x j qs items f mem qFit iFit pos src static small (cap x j)
  have fits : ∀e∈es,e.Fits w (start root b M):=by
    intro e member
    obtain ⟨z,rfl⟩:=List.mem_ofFn.mp member
    exact (all _ _).1
  refine ⟨ProbeStage.Native.columns_exec es mem (ProbeStage.Native.columns_safe es le_rfl fits top),@ProtocolRAM.program_cheap _ _,?_,?_⟩
  · intro x j p
    let z : Fin (X*K):=finProdFinEquiv (x,j)
    have idx : z.val=x.val*K+j.val:=by simp [z,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have seen :(es[z.val]'(z.isLt.trans_eq len.symm))=expr prior root b paid M (qs x j) (items x):=by
      simp only [es,expressions,List.getElem_ofFn,Fin.eta,z,Equiv.symm_apply_apply]
    have rd:=ProbeStage.Native.columns_read es mem le_rfl fits z.val (z.isLt.trans_eq len.symm) (row H G M p)
    rw [seen,idx] at rd
    exact rd.trans ((all x j).2 p)
  · intro a away
    apply ProbeStage.Native.columns_frame es mem
    rcases away with h|h
    · exact .inl h
    · exact .inr ((by rw [len]; exact Nat.le_add_right .. : start root b M+es.length*n≤endAddress root b M H G X K).trans h)

/-- Including the single shared ROM installation followed by all output columns. -/
theorem run (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr)
    (f : Fin X→Fin H→Fin G→Fields K b) (mem : Memory w) (qFit : ∀x j,(qs x j).Fits w root)
    (iFit : ∀x i,(items x i).Fits w root) (pos : 1<2^b) (src : Sources qs items f M mem)
    (cap : ∀x j h g,(∑i,feeAt prior (f x h g) j i)<2^paid) (room : Room w root b M H G X K) :
    let p:=pages prior b paid M
    let mid:=after p (span b M) root mem
    let ps:=passes prior root b paid M H G qs items
    let prog:=(mount p (span b M) w root).seq (program w ps)
    let dst:=result ps mid
    prog.Exec mem dst ((4+10*(2*2^span b M))+clock ps) ∧ CheapCode prog ∧
    (∀x j,Reads (column root b M H G K x.val j.val) (fun h g=>⟨∑i,feeAt prior (f x h g) j i,cap x j h g⟩ : Fin H→Fin G→Cell paid) M dst) ∧
    ∀a,a<root ∨ endAddress root b M H G X K≤a→dst a=mem a := by
  intro p mid ps prog dst
  have limit : start root b M≤endAddress root b M H G X K:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have hdr:=DescentOrdinaryAtomFieldRAM.ROM.run p (span b M) root mem (limit.trans_lt room)
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame p (span b M) root mem
  have carry {a : ℕ} (e : Expr) (v : Fin H→Fin G→Cell a) (fit : e.Fits w root) (src : Source e v M mem) :
      Source e v M mid:=fun r=>(ProtocolRAM.eval_below e _ mem mid fit (fun t ht=>frame _ (.inl ht))).trans (src r)
  have carried : Sources qs items f M mid:=⟨fun x j=>carry _ _ (qFit x j) (src.asked x j),
    fun x i=>carry _ _ (iFit x i) (src.located x i)⟩
  have table:=binary_mounted (scanLaw prior b paid) M p (span b M) root mem (page_bits prior b paid M) id (fun _=>rfl)
  obtain ⟨rs,rc,read,outer⟩:=resident prior qs items f mid qFit iFit pos carried table cap room
  refine ⟨Procedure.Exec.then hdr.1 rs,cheap_seq (cheap p _ _ _) rc,read,?_⟩
  intro a away
  rcases away with h|h
  · exact (outer a (.inl (h.trans_le (Nat.le_add_right ..)))).trans (frame a (.inl h))
  · exact (outer a (.inr h)).trans (frame a (.inr (limit.trans h)))

/-- Safety, cost and frames hold for arbitrary preceding words. -/
theorem any (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr) (m : Memory w)
    (qFit : ∀x j,(qs x j).Fits w root) (iFit : ∀x i,(items x i).Fits w root)
    (room : Room w root b M H G X K) :
    let p:=pages prior b paid M
    let ps:=passes prior root b paid M H G qs items
    let prog:=(mount p (span b M) w root).seq (program w ps)
    let dst:=result ps (after p (span b M) root m)
    prog.Exec m dst ((4+10*(2*2^span b M))+clock ps) ∧ CheapCode prog ∧
    ∀a,a<root ∨ endAddress root b M H G X K≤a→dst a=m a := by
  intro p ps prog dst
  let es:=expressions prior root b paid M qs items
  let n:=H*chunks G M
  have len : es.length=X*K:=by simp [es,expressions]
  have limit : start root b M≤endAddress root b M H G X K:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have startFit:=limit.trans_lt room
  have fit : ∀e∈es,e.Fits w (start root b M):=by
    intro e h;obtain ⟨z,rfl⟩:=List.mem_ofFn.mp h
    apply fits_total
    intro j
    have pair:=pair_fit prior (paid:=paid) _ _ (qFit (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)
      (iFit (finProdFinEquiv.symm z).1 j) startFit
    exact ⟨pair.apply,pair.right,pair.shift,pair.left⟩
  have top : start root b M+es.length*n≤endAddress root b M H G X K:=by rw [len];exact Nat.le_add_right ..
  have hdr:=DescentOrdinaryAtomFieldRAM.ROM.run p (span b M) root m startFit
  have frame:=DescentOrdinaryAtomFieldRAM.ROM.frame p (span b M) root m
  refine ⟨Procedure.Exec.then hdr.1 (ProbeStage.Native.columns_exec es _ (ProbeStage.Native.columns_safe es le_rfl fit (top.trans_lt room))),
    cheap_seq (cheap p _ _ _) (@ProtocolRAM.program_cheap _ _),?_⟩
  intro a away
  have tr:=ProbeStage.Native.columns_frame (base:=start root b M) (n:=n) es (after p (span b M) root m) (address:=a)
  rcases away with h|h
  · exact (tr (.inl (h.trans_le (Nat.le_add_right ..)))).trans (frame a (.inl h))
  · exact (tr (.inr (top.trans h))).trans (frame a (.inr (limit.trans h)))

def expressionCost (K u : ℕ) := 1+(K+K)*(2*u+12)

private theorem term_cost (u : ℕ) (q : Expr) (a : Fin (K+K)→Expr) (ql : q.work≤u) (al : ∀i,(a i).work≤u) :
    (expr prior root b paid M q a).work≤expressionCost K u := by
  have each (i : Fin (K+K)) : ((comparison prior root b paid M).read q (a i)).work≤2*u+11:=by
    simp only [DescentPackedZip.Tables.read,Expr.work]
    have hi:=al i
    omega
  have addCost : (2*u+11)+1 = 2*u+12 := by omega
  simpa only [expr,expressionCost,List.length_finRange,addCost] using
    work_total (fun i=>(comparison prior root b paid M).read q (a i)) (2*u+11) each (List.finRange (K+K))

private theorem column_names (n base u : ℕ) (es : List Expr) (h : ∀e∈es,e.work≤u) :
    DescentStaticWordColumn.names (program w (ProbeStage.Native.columns n base es))≤15+es.length*(11+4*u) := by
  induction es generalizing base with
  | nil =>
    change DescentStaticWordColumn.names (scan w 0 0 (.lit 0)) ≤ 15 + 0*(11+4*u)
    simp [DescentStaticWordColumn.names_scan,Expr.work]
  | cons e es ih =>
    have bound:=h e (.head _)
    have tail:=ih (base+n) (fun z member=>h z (.tail _ member))
    rw [ProbeStage.Native.columns,ProtocolRAM.program,DescentStaticWordColumn.names_seq]
    change DescentStaticWordColumn.names (scan w base n e)+_≤_
    rw [DescentStaticWordColumn.names_scan,List.length_cons,Nat.succ_mul es.length (11+4*u)]
    omega

/-- Shared table words are paid once, independent of hosts, groups and targets. -/
theorem tariff (qs : Fin X→Fin K→Expr) (items : Fin X→Fin (K+K)→Expr)
    (u : ℕ) (qFit : ∀x j,(qs x j).work≤u) (iFit : ∀x i,(items x i).work≤u) :
    let lim:=expressionCost K u
    let ps:=passes prior root b paid M H G qs items
    clock ps≤4+X*K*(4+H*chunks G M*(2*lim+4)) ∧
    DescentStaticWordColumn.names ((mount (pages prior b paid M) (span b M) w root).seq (program w ps))≤
      15*(2*2^(span b M)+1)+(15+X*K*(11+4*lim)) := by
  intro lim ps
  let es:=expressions prior root b paid M qs items
  have len : es.length=X*K:=by simp [es,expressions]
  have bound : ∀e∈es,e.work≤lim:=by
    intro e hit;obtain ⟨z,rfl⟩:=List.mem_ofFn.mp hit
    exact term_cost prior u _ _ (qFit _ _) (iFit _)
  constructor
  · change clock (ProbeStage.Native.columns (H*chunks G M) (start root b M) es) ≤ _
    simpa only [len] using ProbeStage.Native.columns_clock (H*chunks G M) (start root b M) lim es bound
  · rw [DescentStaticWordColumn.names_seq,DescentOrdinaryAtomFieldRAM.ROM.mount,DescentStaticWordColumn.names_mount]
    apply Nat.add_le_add_left
    change DescentStaticWordColumn.names (ProtocolRAM.program w (ProbeStage.Native.columns (H*chunks G M) (start root b M) es)) ≤ _
    simpa only [len] using column_names (w:=w) (H*chunks G M) (start root b M) lim es bound

end
end Hierarchy.DescentResetSourceTicketBank

end OAI
