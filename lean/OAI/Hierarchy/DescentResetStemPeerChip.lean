import OAI.Hierarchy.DescentResetPeerCandidates
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Raw stem-neighbor evidence in the relative old-self socket -/
namespace Hierarchy.DescentResetStemPeerChip
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {S K : ℕ}

/-- Neighbor evidence is kept entirely within the donor's old-host block. A loop
has the same shape at both ends. A missing, overflowing or nonincident key gives zero. -/
def opposite (here : Fin S) (pair : Option (Fin S×Fin S)) : Option (Fin S) := do
  let (a,b) ← pair
  if here=a then some b else if here=b then some a else none

def marker (template : Fin K→Option (Fin S×Fin S)) (D : ℕ) (here : Fin S) (key : ℕ) : ℕ :=
  if hit : 0< key ∧ key≤K then
    (opposite here (template ⟨key-1,by omega⟩)).elim 0 (fun y=>D*S+y.val+1)
  else 0

variable (template : Fin K→Option (Fin S×Fin S))
def bits (D : ℕ) (shape : Fin S) {a b : ℕ} (x : Cell a) : Cell b:=marker template D shape x.val

def table (D a b M : ℕ) (j : ℕ) : ℕ:=
  if live : j<S*2^(a*M) then
    let (shape,word_):=finProdFinEquiv.symm (⟨j,live⟩:Fin (S*2^(a*M)))
    (encode b M (fun t=>bits template D shape ((encode a M).symm word_ t))).val
  else 0

def start (S base H : ℕ) := base+span (H*S)
def endAddress (S base H a M : ℕ) :=start S base H+span (S*2^(a*M))
def cols (S base H : ℕ) : Bank:=⟨base,Nat.clog 2 (H*S)⟩
def book (S base H a M : ℕ) : Bank:=⟨start S base H,Nat.clog 2 (S*2^(a*M))⟩
def headers (S H a M : ℕ) (j : ℕ) : ℕ:=
  if ok : j<H*S then ((finProdFinEquiv.symm (⟨j,ok⟩:Fin (H*S)) : Fin H×Fin S).2.val)*2^(a*M) else 0
def constants (H M D a b j : ℕ) : ℕ:=
  if j< span (H*S) then headers S H a M j else table template D a b M (j-span (H*S))
def dataExpr (S base H a M : ℕ) (actor : Expr) : Expr:=
  .lookup (book S base H a M) (.op .add (.lookup (cols S base H) .row) actor)
def program (base H M D a b w : ℕ):=DescentStaticWordColumn.program w base (constants template H M D a b)
  (span (H*S)+span (S*2^(a*M)))
def memory {w : ℕ} (base H M D a b : ℕ) (m : Memory w):=DescentStaticWordColumn.image base (constants template H M D a b) m
  (span (H*S)+span (S*2^(a*M)))

theorem run {G M a b H D w : ℕ} (base : ℕ) (src : Fin (chunks G M)→Expr) (m : Memory w)
    (state : Fin (H*S)→Fin G→Cell a)
    (old : ∀c v,(src c).eval m (v.val:Word w)=((data (M:=M) state (v,c)).val:Word w))
    (low : ∀c,(src c).Fits w base) (room : endAddress S base H a M<2^w) :
    let top:=endAddress S base H a M
    let done:=memory template base H M D a b m
    let p:=program template base H M D a b w
    p.Exec m done (4+10*(span (H*S)+span (S*2^(a*M)))) ∧
    (∀c,(dataExpr S base H a M (src c)).Fits w top) ∧
    (∀c (v : Fin (H*S)),(dataExpr S base H a M (src c)).eval done (v.val:Word w)=
      ((data (M:=M) (fun a g=> (bits template D
        ((finProdFinEquiv.symm a : Fin H×Fin S).2) (state a g):Cell b)) (v,c)).val:Word w)) ∧
    (∀u,u< base ∨ top≤ u→done u=m u) ∧ DescentStaticWordColumn.names p=15*(span (H*S)+span (S*2^(a*M))+1) ∧ CheapCode p :=by
  intro top done p
  have space : base+(span (H*S)+span (S*2^(a*M)))<2^w:=by simpa [endAddress,start,Nat.add_assoc] using room
  have prop : (cols S base H).Fits w top:=⟨span_pos _,by change span (H*S)<2^w; omega,by change base+span (H*S)≤base+span (H*S)+span (S*2^(a*M)); omega⟩
  have fixed : (book S base H a M).Fits w top:=⟨span_pos _,by change span (S*2^(a*M))<2^w; omega,le_rfl⟩
  have baseTop : base≤ top:=by dsimp [top,endAddress,start];omega
  have stable (a : ℕ) (away : a< base ∨ top≤ a) : done a=m a:=by
    apply DescentStaticWordColumn.frame
    simpa [top,endAddress,start,Nat.add_assoc] using away
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,fun c=>⟨fixed,⟨prop,trivial⟩,ProtocolRAMGeneratedWrite.fits_mono _ baseTop (low c)⟩,
    ?_,stable,DescentStaticWordColumn.names_mount ..,?_⟩
  · intro c v
    let shape:=(finProdFinEquiv.symm v : Fin H×Fin S).2
    let x:=data (M:=M) state (v,c)
    let ix:=finProdFinEquiv (shape,x)
    have ixAt : ix.val=shape.val*2^(a*M)+x.val:=by simp [ix,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have small:=v.isLt.trans_le (span_ge (H*S))
    have mid : v.val< span (H*S)+span (S*2^(a*M)):=small.trans_le (Nat.le_add_right ..)
    have ofst : done (base+v.val)=(shape.val*2^(a*M):ℕ):=by
      dsimp only [done,memory]
      rw [DescentStaticWordColumn.read _ _ _ _ mid];simp [constants,small,headers,v.isLt,shape]
    have jump : done ((start S base H)+ix.val)=(table template D a b M ix.val:Word w):=by
      have under:=ix.isLt.trans_le (span_ge (S*2^(a*M)))
      dsimp only [done,memory]
      rw [start,Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ (Nat.add_lt_add_left under _)]
      simp [constants]
    rw [show (dataExpr S base H a M (src c)).eval done (v.val:Word w)=
      (book S base H a M).read done (((cols S base H).read done (v.val:Word w))+
        (src c).eval done (v.val:Word w)) by rfl,
      bank_read _ _ small prop,show (cols S base H).base=base by rfl,ofst,ProtocolRAM.eval_below _ _ m done (low c) (fun a ha=>stable a (.inl ha)),
      old c v,←Nat.cast_add,←ixAt,bank_read _ _ (ix.isLt.trans_le (span_ge _)) fixed,show (book S base H a M).base=start S base H by rfl,jump]
    apply congrArg (fun j : ℕ=>(j:Word w))
    have unpack : finProdFinEquiv.symm ix = (shape,x) := finProdFinEquiv.symm_apply_apply _
    unfold table
    rw [dite_eq_left ix.isLt]
    change (encode b M (fun t => bits template D (finProdFinEquiv.symm ix).1
      ((encode a M).symm (finProdFinEquiv.symm ix).2 t))).val = _
    rw [unpack]
    apply congrArg Fin.val
    unfold x data
    rw [Equiv.symm_apply_apply]
    apply congrArg (encode b M)
    funext t
    by_cases live : c.val*M+t.val<G
    · simp only [dite_eq_left live]
      rfl
    · simp [live,bits,marker]
  · exact @DescentStaticWordColumn.cheap w base (constants template H M D a b)
      (span (H*S)+span (S*2^(a*M)))

theorem data_work (S base H a M : ℕ) (src : Expr) :
    (dataExpr S base H a M src).work=src.work+13 := by
  change (2+5)+src.work+1+5=_
  omega

theorem marker_zero (D : ℕ) (here : Fin S) : marker template D here 0=0 := by simp [marker]

end
end Hierarchy.DescentResetStemPeerChip

end OAI
