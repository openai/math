import OAI.Hierarchy.DescentNextSignedTables
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Shared format pages and the full block-by-signed-socket successor publication. -/
namespace Hierarchy.DescentNextSignedWindow.Native.All
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinaryAtomFieldRAM.ROM DescentPacking.PackedMatch.Local DescentDyadicSpan
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap b H G M w c X : ℕ}

def pageCount (cap : ℕ) := (8+2*cap)*2
def headWords (cap b M : ℕ) := pageCount cap*2^(ROM.width b M)
def count (X cap : ℕ) := X*(2*cap)
def endAddress (base X cap b M H G : ℕ) := base+headWords cap b M+count X cap*span (H*chunks G M)
def outputBase (base cap b M : ℕ) := base+headWords cap b M

theorem end_address (base X cap b M H G : ℕ) :
    endAddress base X cap b M H G=base+(16+4*cap)*2^((8*b+b)*M)+X*(2*cap)*span (H*chunks G M) := by
  simp only [endAddress,headWords,pageCount,count,ROM.width]
  rw [Nat.mul_comm b 8]
  ring

def address (cap : ℕ) : (Fin 8 ⊕ Fin (2*cap)) × Fin 2 ≃ Fin (pageCount cap) :=
  (finSumFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def pages (D cap b M : ℕ) (i : Fin (pageCount cap)) : Page :=
  let u:=(address cap).symm i
  u.1.elim (fun k=>binary (Gather.setField (d:=b) k) M u.2)
    (fun j=>binary (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) M u.2)

def banks (D cap b M base : ℕ) (k : Fin 8 ⊕ Fin (2*cap)) :=
  joined (pages D cap b M) (ROM.width b M) base (fun i=>address cap (k,i))

theorem join_at (i : Fin 8) (s : Fin 2) :
    pages D cap b M (address cap (.inl i,s))=binary (Gather.setField (d:=b) i) M s := by simp [pages]

theorem lut_at (j : Fin (2*cap)) (s : Fin 2) :
    pages D cap b M (address cap (.inr j,s))=binary (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) M s := by simp [pages]

theorem room (a : Fin (pageCount cap)) : (pages D cap b M a).bits≤ROM.width b M := by
  obtain ⟨⟨k,u⟩,rfl⟩:=(address cap).surjective a
  cases k with
  | inl i=>rw [join_at];fin_cases u <;> change _≤(b*8+b)*M <;> first
    | exact le_rfl
    | exact Nat.mul_le_mul_right M (Nat.le_add_right (b*8) b)
  | inr j=>rw [lut_at];fin_cases u <;> change _≤(b*8+b)*M <;> simpa [binary] using Nat.mul_le_mul_right M (Nat.le_add_right (b*8) b)

def page (base X cap b M H G : ℕ) (x : Fin X) (j : Fin (2*cap)) : Bank :=
  ⟨outputBase base cap b M+(finProdFinEquiv (x,j)).val*span (H*chunks G M),Nat.clog 2 (H*chunks G M)⟩

variable (base : ℕ)
local notation "P" => pages D cap b M
local notation "start" => outputBase base cap b M
local notation "js" => fun i : Fin 8=>banks D cap b M base (.inl i)
local notation "last" j => banks D cap b M base (.inr j)
local notation "N" => H*chunks G M

theorem bankFits {x y z : ℕ} (fn : Cell x→Cell y→Cell z) (k : Fin 8⊕Fin (2*cap))
    (kind : ∀s,P (address cap (k,s))=binary fn M s) (space : start<2^w)
    (u v : Expr) (left : u.Fits w start) (right:v.Fits w start) :
    DescentPackedZip.Fits (banks D cap b M base k) u v x y M start w :=
  ⟨left,right,bank_room P _ _ _ _ (room _) le_rfl space,bank_room P _ _ _ _ (room _) le_rfl space,
    congrArg Page.bits (kind 0),congrArg Page.bits (kind 1)⟩

def body (base D b M : ℕ) (j : Fin (2*cap)) (field : Fin c→Fin 8→Expr) :=
  op (banks D cap b M base (.inr j)) (fun a=>Gather.assembly (fun i=>banks D cap b M base (.inl i)) (field a))

theorem body_fits (j : Fin (2*cap)) (field : Fin c→Fin 8→Expr)
    (early : ∀a i,(field a i).Fits w base) (space : start<2^w) :
    (body base D b M j field).Fits w start :=by
  have before : base≤ start:=Nat.le_add_right ..
  have guards (a : Fin c) : Gather.Bounds (d:=b) (M:=M) (w:=w) js (field a) start :=by
    intro i
    have held:=bankFits (D:=D) (cap:=cap) (M:=M) base (Gather.setField (d:=b) i) (.inl i) (join_at (D:=D) (cap:=cap) (M:=M) i) space (.lit 0) (field a i) trivial
      (ProtocolRAMGeneratedWrite.fits_mono _ before (early a i))
    exact ⟨held.right,held.shift,held.apply,held.shiftBits,held.applyBits⟩
  apply fits_total
  intro a
  have held:=bankFits base (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) (.inr j)
    (lut_at j) space (Gather.assembly js (field a)) (.lit 0) (Gather.fits _ _ _ (guards a) _) trivial
  simp [Tables.read,Expr.Fits,held.left,held.shift,held.apply]

theorem one (j : Fin (2*cap)) (field : Fin c→Fin 8→Expr) (m : Memory w)
    (rows : Fin H→Fin G→Fin c→Option (Record D cap)) (target : Fin H→Fin G→Option (Stage.Live D cap))
    (early : ∀a i,(field a i).Fits w base) (actual : ∀a i,Source (field a i) (fun h g=>(fields (rows h g a) i:Cell b)) M m)
    (small : ∀h g i t,fields (rows h g i) t<2^b)
    (empty : ∀h g,target h g=none→∀i,(rows h g i).bind (fun r=>read r j)=none)
    (live : ∀h g r,target h g=some r→∃i,(rows h g i).bind (fun u=>read u j)=some r ∧ ∀l,l≠i→(rows h g l).bind (fun u=>read u j)=none)
    (space : start+N<2^w) :
    let e:=body base D b M j field
    e.Fits w start ∧ Source e (fun h g=>DescentSignedCableCodec.encode (target h g)) M (after P (ROM.width b M) base m) := by
  intro e
  let loaded:=after P (ROM.width b M) base m
  have below : base≤ start:=Nat.le_add_right ..
  have fits : start<2^w:=(Nat.le_add_right ..).trans_lt space
  have inputs (a:Fin c) (i:Fin 8):Source (field a i) (fun h g=>(fields (rows h g a) i:Cell b)) M loaded:=by
    intro p;exact (eval_below _ _ m loaded (early a i) (fun z hz=>frame P _ base m z (.inl hz))).trans (actual a i p)
  have guards (a : Fin c) : Gather.Bounds (d:=b) (M:=M) (w:=w) js (field a) start := by
    intro i
    have held:=bankFits (D:=D) (cap:=cap) (M:=M) base (Gather.setField (d:=b) i) (.inl i) (join_at i) fits (.lit 0) (field a i) trivial
      (ProtocolRAMGeneratedWrite.fits_mono _ below (early a i))
    exact ⟨held.right,held.shift,held.apply,held.shiftBits,held.applyBits⟩
  have finalFit (a : Fin c) := bankFits base (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) (.inr j)
    (lut_at j) fits (Gather.assembly js (field a)) (.lit 0) (Gather.fits _ _ _ (guards a) _) trivial
  have stat (i : Fin 8) : Static (js i) (Gather.setField (d:=b) i) M loaded :=
    binary_mounted _ M P (ROM.width b M) base m room _ (join_at i)
  have lastStat : Static (last j) (fun x (_:Cell 0)=>Native.table (D:=D) (b:=b) j x) M loaded :=
    binary_mounted _ M P _ base m room _ (lut_at j)
  let sink : Bank:=⟨start,Nat.clog 2 N⟩
  have issued:=run_fields j js (last j) field sink loaded rows target guards stat inputs finalFit small lastStat empty live space
  constructor
  · apply fits_total
    intro a
    simp [Tables.read,Expr.Fits,(finalFit a).left,(finalFit a).shift,(finalFit a).apply]
  · intro p
    exact (ProtocolRAMGeneratedWrite.read_image sink.base N e loaded (row H G M p)).symm.trans (issued.2.1 p)

def exp (base X D cap b M : ℕ) (f : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (s : ℕ) : Expr :=
  if h:s<count X cap then
    let t : Fin X × Fin (2*cap) := finProdFinEquiv.symm ⟨s,h⟩
    body base D b M t.2 (f t.1 t.2)
  else .lit 0

private theorem unpack {m n : ℕ} (a : Fin m × Fin n) (h : (finProdFinEquiv a).val < m*n) :
    (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).symm ⟨(finProdFinEquiv a).val,h⟩ = a :=
  (congrArg (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).symm
    (Fin.ext (show (⟨(finProdFinEquiv a).val,h⟩ : Fin (m*n)).val = (finProdFinEquiv a).val from rfl))).trans
    (finProdFinEquiv.symm_apply_apply a)

@[simp] theorem exp_at (f : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (x : Fin X) (j : Fin (2*cap)) :
    exp base X D cap b M f (finProdFinEquiv (x,j)).val = body base D b M j (f x j) := by
  unfold exp count
  rw [dite_eq_left (finProdFinEquiv (x,j)).isLt]
  simp only [unpack]

def passes (base X D cap b M H G : ℕ) (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) :=
  DescentPackedFlowBatch.passes (outputBase base cap b M) (H*chunks G M) (span (H*chunks G M))
    (exp base X D cap b M field) 0 (count X cap)

def program (base X D cap b M H G w : ℕ) (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) :=
  (mount (pages D cap b M) (ROM.width b M) w base).seq (ProtocolRAM.program w (passes base X D cap b M H G field))

def memory (base X D cap b M H G : ℕ) (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (m : Memory w) :=
  ProtocolRAM.result (passes base X D cap b M H G field) (after (pages D cap b M) (ROM.width b M) base m)

def time (base X D cap b M H G : ℕ) (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) :=
  (4+10*headWords cap b M)+ProtocolRAM.clock (passes base X D cap b M H G field)

theorem run (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (m : Memory w)
    (rows : Fin X→Fin H→Fin G→Fin c→Option (Record D cap))
    (target : Fin X→Fin (2*cap)→Fin H→Fin G→Option (Stage.Live D cap))
    (early : ∀x j a i,(field x j a i).Fits w base)
    (actual : ∀x j a i,Source (field x j a i) (fun h g=>(fields (rows x h g a) i:Cell b)) M m)
    (small : ∀x h g i t,fields (rows x h g i) t<2^b)
    (empty : ∀x j h g,target x j h g=none→∀i,(rows x h g i).bind (fun r=>read r j)=none)
    (live : ∀x j h g r,target x j h g=some r→∃i,(rows x h g i).bind (fun u=>read u j)=some r ∧ ∀l,l≠i→(rows x h g l).bind (fun u=>read u j)=none)
    (space : endAddress base X cap b M H G<2^w) :
    let done:=memory base X D cap b M H G field m
    (program base X D cap b M H G w field).Exec m done (time base X D cap b M H G field) ∧
    (∀x j,Reads (page base X cap b M H G x j) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M done) ∧
    (∀a,a<base ∨ endAddress base X cap b M H G≤a→done a=m a) ∧ CheapCode (program base X D cap b M H G w field) := by
  intro done
  let loaded:=after P (ROM.width b M) base m
  let expression:=exp base X D cap b M field
  have upper : start≤endAddress base X cap b M H G:=Nat.le_add_right ..
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run P (ROM.width b M) base m (upper.trans_lt space)
  have held (x : Fin X) (j : Fin (2*cap)) :
      (body base D b M j (field x j)).Fits w start ∧
      Source (body base D b M j (field x j)) (fun h g=>DescentSignedCableCodec.encode (target x j h g)) M loaded := by
    have positive : 0<count X cap:=Nat.mul_pos (Nat.zero_lt_of_lt x.isLt) (Nat.zero_lt_of_lt j.isLt)
    have budget : span N≤count X cap*span N:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (span N) positive
    have fitN:=span_ge N
    have fit : start+N<2^w:=by unfold endAddress at space;change base+headWords cap b M+_<_ at space;dsimp [outputBase];omega
    exact one base j (field x j) m (rows x) (target x j) (early x j) (actual x j) (small x) (empty x j) (live x j) fit
  have valid (i : ℕ) (hi : i<count X cap) : (expression i).Fits w start := by
    obtain ⟨⟨x,j⟩,eqn⟩:=finProdFinEquiv.surjective (⟨i,hi⟩ : Fin (X*(2*cap)))
    have val:=congrArg Fin.val eqn
    dsimp only at val
    rw [←val]
    change (exp base X D cap b M field (finProdFinEquiv (x,j)).val).Fits w start
    rw [exp_at]
    exact (held x j).1
  have batch:=DescentPackedFlowBatch.execute start N (span N) (count X cap) expression loaded valid space (span_ge N)
  refine ⟨Procedure.Exec.then mounted.1 batch.1,?_,?_,?_⟩
  · intro x j p
    let i:=finProdFinEquiv (x,j)
    have reading:=batch.2.1 i (row H G M p)
    change done (start+i.val*span N+(row H G M p).val)=_
    apply reading.trans
    rw [show expression i.val=body base D b M j (field x j) from exp_at base field x j]
    exact (held x j).2 p
  · intro a away
    rcases away with old|later
    · exact (batch.2.2 a (old.trans_le (Nat.le_add_right ..))).trans (frame P _ base m a (.inl old))
    · have rest:=DescentPackedFlowBatch.above start N (span N) expression loaded 0 (count X cap) a (span_ge N)
        (by simpa only [endAddress,outputBase,Nat.zero_add] using later)
      exact rest.trans (frame P _ base m a (.inr (upper.trans later)))
  · exact cheap_seq (cheap P _ w base) (program_cheap w _)

/-- Blind execution has the same numeric endpoint and clock for every input memory. -/
theorem any (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (m : Memory w)
    (early : ∀x j a i,(field x j a i).Fits w base) (space : endAddress base X cap b M H G<2^w) :
    let done:=memory base X D cap b M H G field m
    (program base X D cap b M H G w field).Exec m done (time base X D cap b M H G field) ∧
      (∀a,a<base ∨ endAddress base X cap b M H G≤a→done a=m a) ∧
      CheapCode (program base X D cap b M H G w field) :=by
  intro done
  let loaded:=after P (ROM.width b M) base m
  let expression:=exp base X D cap b M field
  have upper : start≤endAddress base X cap b M H G:=Nat.le_add_right ..
  have mounted:=DescentOrdinaryAtomFieldRAM.ROM.run P (ROM.width b M) base m (upper.trans_lt space)
  have valid (i : ℕ) (hi : i<count X cap) : (expression i).Fits w start:=by
    obtain ⟨⟨x,j⟩,eqn⟩:=finProdFinEquiv.surjective (⟨i,hi⟩ : Fin (X*(2*cap)))
    have val:=congrArg Fin.val eqn
    change (exp base X D cap b M field i).Fits w start
    rw [←show (finProdFinEquiv (x,j)).val=i from val,exp_at]
    exact body_fits base j (field x j) (early x j) (upper.trans_lt space)
  have batch:=DescentPackedFlowBatch.execute start N (span N) (count X cap) expression loaded valid space (span_ge N)
  refine ⟨Procedure.Exec.then mounted.1 batch.1,?_,cheap_seq (cheap P _ w base) (program_cheap w _)⟩
  intro a away
  rcases away with old|later
  · exact (batch.2.2 a (old.trans_le (Nat.le_add_right ..))).trans (frame P _ base m a (.inl old))
  · have rest:=DescentPackedFlowBatch.above start N (span N) expression loaded 0 (count X cap) a (span_ge N)
        (by simpa only [endAddress,outputBase,Nat.zero_add] using later)
    exact rest.trans (frame P _ base m a (.inr (upper.trans later)))

theorem clock_bound (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (lim : ℕ)
    (early : ∀x j a i,(field x j a i).work≤lim) :
    time base X D cap b M H G field≤
      (4+10*headWords cap b M)+(4+count X cap*(4+N*(2*(1+c*(14+8*(lim+11)))+4))) := by
  apply Nat.add_le_add_left
  apply DescentPackedFlowBatch.tariff
  intro i hi
  obtain ⟨⟨x,j⟩,eqn⟩:=finProdFinEquiv.surjective (⟨i,hi⟩ : Fin (X*(2*cap)))
  have val:=congrArg Fin.val eqn
  rw [←show (finProdFinEquiv (x,j)).val=i from val,exp_at]
  exact ROM.operation_work js (last j) (field x j) lim (early x j)

theorem sweep_names (rows pitch start_ n : ℕ) (e : ℕ→Expr) (K : ℕ)
    (limit : ∀j,start_≤j→j<start_+n→(e j).work≤K) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (DescentPackedFlowBatch.passes base rows pitch e start_ n))
      ≤15+n*(11+4*K) :=by
  induction n generalizing start_ with
  | zero=>
    change DescentStaticWordColumn.names (scan w 0 0 (.lit 0))≤_
    rw [DescentStaticWordColumn.names_scan]
    simp [Expr.work]
  | succ n ih=>
    have tail:=ih (start_+1) (fun j lo hi=>limit j (by omega) (by omega))
    have head:=limit start_ (by omega) (by omega)
    change DescentStaticWordColumn.names ((scan w (base+start_*pitch) rows (e start_)).seq
      (ProtocolRAM.program w (DescentPackedFlowBatch.passes base rows pitch e (start_+1) n)))≤_
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,Nat.succ_mul n (11+4*K)]
    omega

theorem text_bound (field : Fin X→Fin (2*cap)→Fin c→Fin 8→Expr) (lim : ℕ)
    (early : ∀x j a i,(field x j a i).work≤lim) :
    DescentStaticWordColumn.names (program base X D cap b M H G w field)≤
      15*(headWords cap b M+1)+15+count X cap*(11+4*(1+c*(14+8*(lim+11)))) :=by
  rw [program,DescentStaticWordColumn.names_seq]
  have mounted : DescentStaticWordColumn.names (mount P (ROM.width b M) w base)=15*(headWords cap b M+1) :=
    DescentStaticWordColumn.names_mount w base _ _
  rw [mounted,Nat.add_assoc]
  apply Nat.add_le_add_left
  apply sweep_names
  intro i _ bound
  have hi : i<count X cap:=by omega
  obtain ⟨⟨x,j⟩,eqn⟩:=finProdFinEquiv.surjective (⟨i,hi⟩ : Fin (X*(2*cap)))
  have val:=congrArg Fin.val eqn
  rw [←show (finProdFinEquiv (x,j)).val=i from val,exp_at]
  exact ROM.operation_work js (last j) (field x j) lim (early x j)

end
end Hierarchy.DescentNextSignedWindow.Native.All

end OAI
