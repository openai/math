import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Short raw neighbor tickets from physically installed private reset panels -/
namespace Hierarchy.DescentResetPeerUnionRAM.PrivateEvidence
open DescentSIMDLookup DescentPackedColony DescentIssuedTerminalId DescentDyadicSpan DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H S D b a G M cap w : ℕ}

def ticket (D shapes here : ℕ) (fields : Fin 5→ℕ) : ℕ :=
  if fields 0=1 then
    if fields 1=here then D*shapes+fields 2+1
    else if fields 2=here then D*shapes+fields 1+1 else 0
  else 0

def frame (b cap : ℕ) (slot : Fin cap) (raw : Cell (b*(cap*5))) (j : Fin 5) :=
  digit b (finProdFinEquiv (slot,j)).val raw.val

def word (D S b cap a : ℕ) (here : Fin S) (slot : Fin cap) (raw : Cell (b*(cap*5))) : Cell a :=
  ticket D S here.val (frame b cap slot raw)

@[simp] theorem word_blank (D S b cap a : ℕ) (here : Fin S) (slot : Fin cap) :
    word D S b cap a here slot 0=0 := by simp [word,ticket,frame,digit]

def page (S cap b M : ℕ) := span (S*2^((b*(cap*5))*M))
def start (base H S : ℕ) := base+2*span (H*S)
def extent (H S cap b M : ℕ) := 2*span (H*S)+cap*page S cap b M
def endAddress (base H S cap b M : ℕ) := base+extent H S cap b M

def parent (base H S : ℕ) : Bank := ⟨base,Nat.clog 2 (H*S)⟩
def offsets (base H S : ℕ) : Bank := ⟨base+span (H*S),Nat.clog 2 (H*S)⟩
def book (base H S cap b M : ℕ) (slot : Fin cap) : Bank :=
  ⟨start base H S+slot.val*page S cap b M,Nat.clog 2 (S*2^((b*(cap*5))*M))⟩

def atOld (base H S : ℕ) (old : Bank) (chunk : ℕ) : Expr :=
  .lookup old (.op .add (.lookup (parent base H S) .row) (.lit chunk))
def operand (base H S cap b M : ℕ) (old : Bank) (slot : Fin cap) (chunk : ℕ) : Expr :=
  .lookup (book base H S cap b M slot)
    (.op .add (.lookup (offsets base H S) .row) (atOld base H S old chunk))

def rendered (D S cap b M a : ℕ) (slot : Fin cap) (here : Fin S) (raw : Cell ((b*(cap*5))*M)) :=
  (encode a M (fun j=>word D S b cap a here slot ((encode (b*(cap*5)) M).symm raw j))).val

private def panelCell {slots shapes keys : ℕ}
    (emit : Fin slots → Fin shapes → Fin keys → ℕ) (sl index : ℕ) : ℕ :=
  if hs : sl < slots then
    if hi : index < shapes*keys then
      let p := finProdFinEquiv.symm (⟨index,hi⟩ : Fin (shapes*keys))
      emit ⟨sl,hs⟩ p.1 p.2
    else 0
  else 0

private theorem panelCell_at {slots shapes keys : ℕ}
    (emit : Fin slots → Fin shapes → Fin keys → ℕ) (sl : Fin slots)
    (p : Fin shapes × Fin keys) :
    panelCell emit sl.val (finProdFinEquiv p).val = emit sl p.1 p.2 := by
  rw [panelCell,dite_eq_left sl.isLt,dite_eq_left (finProdFinEquiv p).isLt]
  exact congrArg (fun q : Fin shapes × Fin keys => emit sl q.1 q.2)
    (finProdFinEquiv.symm_apply_apply p)

private def panelWord {slots shapes keys : ℕ} (n per : ℕ) (first second : ℕ → ℕ)
    (emit : Fin slots → Fin shapes → Fin keys → ℕ) (addr : ℕ) : ℕ :=
  if addr < n then first addr else if addr < 2*n then second (addr-n) else
    panelCell emit ((addr-2*n)/per) ((addr-2*n)%per)

private theorem panelWord_at {slots shapes keys : ℕ} (n per : ℕ) (first second : ℕ → ℕ)
    (emit : Fin slots → Fin shapes → Fin keys → ℕ) (sl : Fin slots)
    (here : Fin shapes) (raw : Fin keys) (fits : shapes*keys ≤ per) :
    panelWord n per first second emit (2*n+sl.val*per+(here.val*keys+raw.val)) =
      emit sl here raw := by
  let k : Fin (shapes*keys) := finProdFinEquiv (here,raw)
  have idx : k.val = here.val*keys+raw.val := by
    simp only [k,finProdFinEquiv_apply_val,Nat.mul_comm keys,Nat.add_comm]
  have small : k.val < per := k.isLt.trans_le fits
  have positive : 0 < per := Nat.zero_lt_of_lt small
  let addr := 2*n+sl.val*per+k.val
  have firstMiss : ¬ addr < n := by dsimp only [addr]; omega
  have secondMiss : ¬ addr < 2*n := by dsimp only [addr]; omega
  have delta : addr-2*n = sl.val*per+k.val := by dsimp only [addr]; omega
  have quotient : (sl.val*per+k.val)/per = sl.val := by
    rw [Nat.mul_comm sl.val, Nat.mul_add_div positive, Nat.div_eq_of_lt small, Nat.add_zero]
  have remainder : (sl.val*per+k.val)%per = k.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt small]
  rw [←idx]
  change panelWord n per first second emit addr = _
  rw [panelWord,ite_eq_right firstMiss,ite_eq_right secondMiss,delta,quotient,remainder]
  exact panelCell_at emit sl (here,raw)

def constants (H S D cap b M a G : ℕ) (i : ℕ) : ℕ :=
  let n:=span (H*S)
  if i < n then i/S*chunks G M else if i < 2*n then (i-n)%S*2^((b*(cap*5))*M) else
    let j:=i-2*n
    let p:=page S cap b M
    panelCell (rendered D S cap b M a) (j/p) (j%p)

private theorem table_read (H S D cap b M a G : ℕ) (slot : Fin cap) (here : Fin S)
    (raw : Cell ((b*(cap*5))*M)) :
    constants H S D cap b M a G
        (2*span (H*S)+slot.val*page S cap b M+(here.val*2^((b*(cap*5))*M)+raw.val))=
      rendered D S cap b M a slot here raw := by
  exact panelWord_at (span (H*S)) (page S cap b M)
    (fun i => i/S*chunks G M) (fun j => j%S*2^((b*(cap*5))*M))
    (rendered D S cap b M a) slot here raw (span_ge _)

def program (w base H S D cap b M a G : ℕ) :=
  DescentStaticWordColumn.program w base (constants H S D cap b M a G) (extent H S cap b M)
def image (base H S D cap b M a G : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (constants H S D cap b M a G) m (extent H S cap b M)

/-- One statically printed short lookup is shared by all sites, all old signed
sides, all root tickets and every selected private device of this date. -/
theorem run (base H S D cap b M a G : ℕ) (m : Memory w) (room : endAddress base H S cap b M < 2^w) :
    let n:=extent H S cap b M
    let out:=image base H S D cap b M a G m
    let code:=program w base H S D cap b M a G
    code.Exec m out (4+10*n) ∧ CheapCode code ∧ DescentStaticWordColumn.names code=15*(n+1) ∧
    (∀x,x < base ∨ base+n ≤ x → out x=m x) ∧
    ∀(old : Bank) (values : Fin H→Fin G→Cell (b*(cap*5))),
      old.Fits w base → H*chunks G M ≤ old.size →
      (∀p : Row H G M,m (old.base+(row H G M p).val)=((data (M:=M) values p).val:Word w)) →
      ∀(slot : Fin cap) (c : Fin (chunks G M)),
        (operand base H S cap b M old slot c.val).Fits w (endAddress base H S cap b M) ∧
        ∀v : Fin (H*S),(operand base H S cap b M old slot c.val).eval out (v.val:Word w)=
          ((data (M:=M) (fun h g=>
            let p:=finProdFinEquiv.symm h
            word D S b cap a p.2 slot (values p.1 g)) (v,c)).val:Word w) := by
  intro n out code
  have reserve : base+n < 2^w := room
  have fr (x : ℕ) (away : x < base ∨ base+n ≤ x) : out x=m x :=
    DescentStaticWordColumn.frame _ _ _ _ _ away
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ reserve,@DescentStaticWordColumn.cheap _ _ _ _,
    DescentStaticWordColumn.names_mount ..,fr,?_⟩
  intro old values ofit orows reads slot c
  let width:=b*(cap*5)
  let per:=page S cap b M
  have slotEnd:=Nat.mul_le_mul_right per slot.isLt
  rw [Nat.succ_mul] at slotEnd
  have bankFit (q : Bank) (range : q.base+q.size ≤ base+n) : q.Fits w (base+n) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (range.trans_lt reserve),range⟩
  have pf:=bankFit (parent base H S) (by change base+span (H*S) ≤ base+(2*span (H*S)+cap*per);omega)
  have sf:=bankFit (offsets base H S) (by change base+span (H*S)+span (H*S) ≤ base+(2*span (H*S)+cap*per);omega)
  have tf:=bankFit (book base H S cap b M slot)
    (by change base+2*span (H*S)+slot.val*per+per ≤ base+(2*span (H*S)+cap*per);omega)
  have oldFit:=bankFit old (ofit.2.2.trans (Nat.le_add_right ..))
  refine ⟨⟨tf,⟨⟨sf,trivial⟩,⟨oldFit,⟨⟨pf,trivial⟩,trivial⟩⟩⟩⟩,?_⟩
  intro v
  let p : Fin H×Fin S:=finProdFinEquiv.symm v
  have vr : v.val=p.1.val*S+p.2.val := by
    rw [←finProdFinEquiv.apply_symm_apply v]
    simp only [p,finProdFinEquiv_apply_val,Nat.mul_comm S,Nat.add_comm]
  have little:=p.2.isLt
  have positive : 0 < S:=Nat.zero_lt_of_lt little
  have vdiv : v.val/S=p.1.val :=by
    rw [vr,Nat.mul_comm p.1.val S,Nat.mul_add_div positive,Nat.div_eq_of_lt little,Nat.add_zero]
  have vmod : v.val%S=p.2.val :=by rw [vr,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt little]
  have inline:=v.isLt.trans_le (span_ge (H*S))
  have nRange : 2*span (H*S) ≤ n := Nat.le_add_right ..
  have ptr : out (base+v.val)=((p.1.val*chunks G M:ℕ):Word w) :=by
    rw [show out (base+v.val)=(constants H S D cap b M a G v.val:Word w) from
      DescentStaticWordColumn.read _ _ _ _ (by omega)]
    simp [constants,inline,vdiv]
  have shift : out (base+span (H*S)+v.val)=((p.2.val*2^(width*M):ℕ):Word w) :=by
    rw [Nat.add_assoc,show out (base+(span (H*S)+v.val))=(constants H S D cap b M a G (span (H*S)+v.val):Word w) from
      DescentStaticWordColumn.read _ _ _ _ (by omega)]
    simp [constants,show span (H*S)+v.val < 2*span (H*S) by omega,vmod,width]
  let raw:=data (M:=M) values (p.1,c)
  let pos:=row H G M (p.1,c)
  have posAt : pos.val=p.1.val*chunks G M+c.val := by simp [pos,row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have source : (atOld base H S old c.val).eval out (v.val:Word w)=(raw.val:Word w) :=by
    have off:=(lookup_nat (parent base H S) out _ .row v.val rfl inline pf.2.1).trans ptr
    have addr : (Expr.op .add (.lookup (parent base H S) .row) (.lit c.val)).eval out (v.val:Word w)=(pos.val:Word w) :=by
      change (Expr.lookup _ .row).eval out _+(c.val:Word w)=_
      rw [off,posAt,Nat.cast_add]
    exact (lookup_nat old out _ _ pos.val addr (pos.isLt.trans_le orows) ofit.2.1).trans
      ((fr (old.base+pos.val) (.inl (by have :=ofit.2.2;have :=pos.isLt.trans_le orows;omega))).trans (reads (p.1,c)))
  let key:=p.2.val*2^(width*M)+raw.val
  have bound : key < S*2^(width*M) :=
    (Nat.add_lt_add_left raw.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ p.2.isLt)
  have idx:=bound.trans_le (span_ge _)
  have offset:=(lookup_nat (offsets base H S) out _ .row v.val rfl inline sf.2.1).trans shift
  have addr : (Expr.op .add (.lookup (offsets base H S) .row) (atOld base H S old c.val)).eval out (v.val:Word w)=
      (key:Word w) :=by
    change (Expr.lookup _ .row).eval out _+(atOld base H S old c.val).eval out _=_
    rw [offset,source]
    exact (Nat.cast_add ..).symm
  refine (lookup_nat (book base H S cap b M slot) out _ _ key addr idx tf.2.1).trans ?_
  have entry : 2*span (H*S)+slot.val*per+key < n := by
    calc
      _ < 2*span (H*S)+slot.val*per+per := Nat.add_lt_add_left idx _
      _ = 2*span (H*S)+(slot.val*per+per) := Nat.add_assoc ..
      _ ≤ 2*span (H*S)+cap*per := Nat.add_le_add_left slotEnd _
  have stored : out (base+(2*span (H*S)+slot.val*per+key)) =
      (constants H S D cap b M a G (2*span (H*S)+slot.val*per+key):Word w) :=
    DescentStaticWordColumn.read base n (constants H S D cap b M a G) m entry
  have decoded : constants H S D cap b M a G (2*span (H*S)+slot.val*per+key) =
      rendered D S cap b M a slot p.2 raw :=
    table_read H S D cap b M a G slot p.2 raw
  change out ((base+2*span (H*S)+slot.val*per)+key)=_
  rw [show (base+2*span (H*S)+slot.val*per)+key=base+(2*span (H*S)+slot.val*per+key) by omega,
    stored,decoded]
  apply congrArg (fun t : ℕ=>(t:Word w))
  unfold rendered
  apply congrArg Fin.val
  apply congrArg (encode a M)
  funext j
  by_cases inside : c.val*M+j.val < G <;> simp [raw,data,p,inside,word_blank]

theorem operand_work (base H S cap b M : ℕ) (old : Bank) (slot : Fin cap) (chunk : ℕ) :
    (operand base H S cap b M old slot chunk).work=27 := rfl

end
end Hierarchy.DescentResetPeerUnionRAM.PrivateEvidence

end OAI
