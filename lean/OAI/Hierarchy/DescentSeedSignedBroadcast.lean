import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! Broadcast an immutable small cell to all live group lanes and mask the incomplete chunk. -/
namespace Hierarchy.DescentSeedSignedBroadcast
open DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {C H G M b w : ℕ}

def wide (M : ℕ) (x : Cell b) := encode b M (fun _=>x)

theorem last_word (f : Fin H→Cell b) (p : Row H G M) :
    (wide M (f p.1)).val % 2^(b*used G M p.2.val) = (data (fun v (_ : Fin G)=>f v) p).val := by
  have eqn:=DescentSixParty.PackedCensus.masked_data (fun _ : Cell 1=>f p.1)
    (fun _ : Fin H=>fun _ : Fin G=>(0:Cell 1)) p
  simpa only [masked,table,wide,data,Function.comp_def] using eqn

structure Banks where
  word : Bank
  index : Bank
  mask : Bank

def body (B : Banks) : Expr := .op .mask (.lookup B.word (.lookup B.index .row)) (.lookup B.mask .row)

structure Fits (B : Banks) (out H G M C b w : ℕ) : Prop where
  word : B.word.Fits w out
  index : B.index.Fits w out
  mask : B.mask.Fits w out
  cells : C≤B.word.size
  indices : H*chunks G M≤B.index.size
  masks : H*chunks G M≤B.mask.size
  bits : b*M≤w
  outside : out+H*chunks G M<2^w

structure Stored (B : Banks) (f : Fin C→Cell b) (key : Fin H→Fin C) (G M : ℕ) (m : Memory w) : Prop where
  word : ∀c,m (B.word.base+c.val)=((wide M (f c)).val:Word w)
  index : ∀p : Row H G M,m (B.index.base+(row H G M p).val)=((key p.1).val:Word w)
  mask : ∀p : Row H G M,m (B.mask.base+(row H G M p).val)=(maskWord b M G p.2.val:Word w)

def maskBits (b M G : ℕ) (p : Row H G M) := maskWord b M G p.2.val

theorem mask_eval (v k : ℕ) (wordFit : v < 2^w) (maskFit : 2^k-1 < 2^w) :
    BinaryOp.bitAnd.eval (v : Word w) ((2^k-1 : ℕ) : Word w) = ((v % 2^k : ℕ) : Word w) := by
  change (((v : Word w).val &&& (((2^k-1 : ℕ) : Word w).val) : ℕ) : Word w) = _
  rw [Fin.val_cast_of_lt wordFit,Fin.val_cast_of_lt maskFit,Nat.and_two_pow_sub_one_eq_mod]

theorem at_row (B : Banks) (out : ℕ) (fit : Fits B out H G M C b w) (f : Fin C→Cell b)
    (key : Fin H→Fin C) (m : Memory w) (st : Stored B f key G M m) (p : Row H G M) :
    (body B).eval m ((row H G M p).val:Word w)=((data (fun h (_ : Fin G)=>f (key h)) p).val:Word w) := by
  let t:=wide M (f (key p.1))
  have lim : t.val<2^w:=t.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit.bits)
  have hm : maskWord b M G p.2.val<2^w :=
    (Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide)
      ((Nat.mul_le_mul_left b (Nat.min_le_left ..)).trans fit.bits))
  have left:=DescentPackedZip.bank_read B.index m ((row H G M p).isLt.trans_le fit.indices) fit.index
  have right:=DescentPackedZip.bank_read B.mask m ((row H G M p).isLt.trans_le fit.masks) fit.mask
  have src:=DescentPackedZip.bank_read B.word m ((key p.1).isLt.trans_le fit.cells) fit.word
  rw [←last_word (fun h=>f (key h)) p]
  simp only [body,Expr.eval,left,right,st.index,st.mask,src,st.word,RowOp.opcode]
  exact mask_eval _ _ lim hm

theorem run (B : Banks) (out : ℕ) (fit : Fits B out H G M C b w) (f : Fin C→Cell b)
    (key : Fin H→Fin C) (m : Memory w) (st : Stored B f key G M m) :
    let result:=image out (H*chunks G M) (body B) m
    (scan w out (H*chunks G M) (body B)).Exec m result (4+H*chunks G M*(2*(body B).work+4)) ∧
    (∀p : Row H G M,result (out+(row H G M p).val)=((data (fun h (_ : Fin G)=>f (key h)) p).val:Word w)) ∧
    (∀a,a<out ∨ out+H*chunks G M≤a→ result a=m a) ∧ CheapCode (scan w out (H*chunks G M) (body B)) := by
  intro result
  have safe : (body B).Fits w out := ⟨⟨fit.word,fit.index,trivial⟩,fit.mask,trivial⟩
  exact ⟨scan_exec _ _ _ _ safe fit.outside,
    fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M p)).trans (at_row B out fit f key m st p),
    fun _ h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ h,scan_cheap w out (H*chunks G M) (body B)⟩

/-- All literal banks together store one full broadcast per original cell, plus two words per packed physical row. -/
def RAM (base C count : ℕ) : Banks :=
  ⟨⟨base,Nat.clog 2 C⟩,⟨base+span C,Nat.clog 2 count⟩,⟨base+span C+span count,Nat.clog 2 count⟩⟩

def finRead {n : ℕ} (f : Fin n→ℕ) (j : ℕ) := if h : j<n then f ⟨j,h⟩ else 0

def size (C H G M : ℕ) := (span C)+2*(span (H*chunks G M))

def literals (G M : ℕ) (f : Fin C→Cell b) (key : Fin H→Fin C) (j : ℕ) : ℕ :=
  if j<span C then finRead (fun c=>(wide M (f c)).val) j
  else if j<span C+(span (H*chunks G M)) then
    finRead (fun q : Fin (H*chunks G M)=>(key ((row H G M).symm q).1).val) (j-(span C))
  else finRead (fun q : Fin (H*chunks G M)=>maskWord b M G ((row H G M).symm q).2.val) (j-(span C+(span (H*chunks G M))))

theorem size_le (C H G M : ℕ) : size C H G M≤2*C+4*(H*chunks G M)+3 := by
  have cells:=span_le C
  have rows:=span_le (H*chunks G M)
  unfold size
  omega

/-- The original codebook has an additional linear word bill, while each actual group lane uses bounded bits. -/
theorem tape_bits (C H G w b : ℕ) (positive : 0<b) (wideEnough : 2*b≤w) :
    (size C H G (lanes w b)+H*chunks G (lanes w b))*w≤
      (2*C+3)*w+5*(H*w+4*H*G*b) := by
  have sizeBill:=Nat.mul_le_mul_right w (size_le C H G (lanes w b))
  have packed:=volume H G w b positive wideEnough
  nlinarith only [sizeBill,packed]

theorem fresh (G M base : ℕ) (f : Fin C→Cell b) (key : Fin H→Fin C) (m : Memory w)
    (bits : b*M≤w) (space : base+size C H G M+H*chunks G M<2^w) :
    let n:=H*chunks G M
    let B:=RAM base C n
    let out:=base+size C H G M
    let table:=literals G M f key
    let prep:=DescentStaticWordColumn.image base table m (size C H G M)
    let result:=image out n (body B) prep
    ((DescentStaticWordColumn.program w base table (size C H G M)).seq (scan w out n (body B))).Exec m result
        ((4+10*size C H G M)+(4+n*(2*(body B).work+4))) ∧
    (∀p : Row H G M,result (out+(row H G M p).val)=((data (fun h (_ : Fin G)=>f (key h)) p).val:Word w)) ∧
    ∀a,a<base ∨ out+n≤a→ result a=m a := by
  intro n B out table prep result
  have enough:=span_ge C
  have rows:=span_ge (H*chunks G M)
  have cellsPos:=span_pos C
  have chunkPos:=span_pos (H*chunks G M)
  have lim : base+size C H G M<2^w:=by omega
  have fit : Fits B out H G M C b w := by
    change base+(span C+2*span n) < 2^w at lim
    refine ⟨?_,?_,?_,enough,rows,rows,bits,space⟩
    · change 0 < span C ∧ span C < 2^w ∧ base+span C ≤ base+(span C+2*span n)
      exact ⟨cellsPos,by omega,by omega⟩
    · change 0 < span n ∧ span n < 2^w ∧ base+span C+span n ≤ base+(span C+2*span n)
      exact ⟨chunkPos,by omega,by omega⟩
    · change 0 < span n ∧ span n < 2^w ∧ base+span C+span n+span n ≤ base+(span C+2*span n)
      exact ⟨chunkPos,by omega,by omega⟩
  have st : Stored B f key G M prep := by
    constructor
    · intro c
      change DescentStaticWordColumn.image base table m (size C H G M) (base+c.val)=_
      rw [DescentStaticWordColumn.read _ _ _ _ (by dsimp [size];omega : c.val<size C H G M)]
      simp [table,literals,finRead,c.isLt,show c.val<span C by omega]
    · intro p
      let u:=row H G M p
      have hu:=u.isLt
      change DescentStaticWordColumn.image base table m (size C H G M) (base+(span C)+u.val)=_
      rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ (by dsimp [size];omega : span C+u.val<size C H G M)]
      simp [table,literals,finRead,u,show ¬span C+u.val<span C by omega,
        show span C+u.val<span C+(span (H*chunks G M)) by omega,(row H G M p).isLt]
    · intro p
      let u:=row H G M p
      have hu:=u.isLt
      change DescentStaticWordColumn.image base table m (size C H G M) (base+(span C)+(span (H*chunks G M))+u.val)=_
      rw [show base+(span C)+(span (H*chunks G M))+u.val=base+(span C+(span (H*chunks G M))+u.val) by omega,
        DescentStaticWordColumn.read _ _ _ _ (by dsimp [size];omega : span C+(span (H*chunks G M))+u.val<size C H G M)]
      simp [table,literals,finRead,u,show ¬span C+(span (H*chunks G M))+u.val<span C by omega,
        show ¬span C+(span (H*chunks G M))+u.val<span C+(span (H*chunks G M)) by omega,(row H G M p).isLt]
  have used:=run B out fit f key prep st
  have install : (DescentStaticWordColumn.program w base table (size C H G M)).Exec m prep (4+10*size C H G M) :=
    DescentStaticWordColumn.mount base _ table m lim
  refine ⟨?_,used.2.1,?_⟩
  · intro P R K machine pc reg pub exit rom advice cfg mem enter same
    exact Procedure.Exec.then install used.1 machine pc reg pub exit rom advice cfg mem enter same
  intro a away
  have base_out : base ≤ out := Nat.le_add_right ..
  have old := used.2.2.1 a (away.imp (fun h=>h.trans_le base_out) id)
  have preserve : a < base ∨ base+size C H G M ≤ a :=
    away.imp id (fun h => (Nat.le_add_right out n).trans h)
  exact old.trans (DescentStaticWordColumn.frame base (size C H G M) table m a preserve)

end
end Hierarchy.DescentSeedSignedBroadcast

end OAI
