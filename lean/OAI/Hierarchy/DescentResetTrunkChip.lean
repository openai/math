import OAI.Hierarchy.DescentResetTrunkPalette
import OAI.Hierarchy.DescentResetPeerCandidates
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Raw trunk-neighbor evidence in the relative old-self socket -/
namespace Hierarchy.DescentResetTrunkChip
open DescentSIMDLookup DescentPackedZip DescentDenseHostOrder DescentCommonHost DescentDyadicSpan ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
local notation "S" => (roster board r depth).card

/-- The donor root is always the receiver's original host. The opposite
shape is computed once on that finite unlabelled public palette. -/
def other (key : Fin S) : Option (Fin S):=
  let label:=(DescentResetTrunkPalette.order board r depth).symm key
  match label.val with
  | .trunk side z=>
    if h : .trunk (!side) z∈roster board r depth then some (localRank board r depth ⟨_,h⟩) else none
  | _=>none

def marker (D : ℕ) (key : Fin S) : ℕ := (other board r depth key).elim 0 (fun y=>D*S+y.val+1)

def bits (D : ℕ) (key : Fin S) {b : ℕ} (x : Cell 1) : Cell b:=if x.val=1 then marker board r depth D key else 0

def table (D b M : ℕ) (j : ℕ) : ℕ:=
  if live : j<S*2^M then
    let (shape,word_):=finProdFinEquiv.symm (⟨j,live⟩:Fin (S*2^M))
    (encode b M (fun t=>bits board r depth D shape ((encode 1 M).symm (Fin.cast (by simp) word_) t))).val
  else 0

def start (base H : ℕ) := base+span (H*S)
def endAddress (base H M : ℕ) :=start board r depth base H+span (S*2^M)
def cols (base H : ℕ) : Bank:=⟨base,Nat.clog 2 (H*S)⟩
def book (base H M : ℕ) : Bank:=⟨start board r depth base H,Nat.clog 2 (S*2^M)⟩
def headers (H M : ℕ) (j : ℕ) : ℕ:=
  if ok : j<H*S then ((finProdFinEquiv.symm (⟨j,ok⟩:Fin (H*S)) : Fin H×Fin S).2.val)*2^M else 0
def constants (H M D b j : ℕ) : ℕ:=
  if j< span (H*S) then headers board r depth H M j else table board r depth D b M (j-span (H*S))
def dataExpr (base H M : ℕ) (actor : Expr) : Expr:=
  .lookup (book board r depth base H M) (.op .add (.lookup (cols board r depth base H) .row) actor)
def program (base H M D b w : ℕ):=DescentStaticWordColumn.program w base (constants board r depth H M D b)
  (span (H*S)+span (S*2^M))
def memory {w : ℕ} (base H M D b : ℕ) (m : Memory w):=DescentStaticWordColumn.image base (constants board r depth H M D b) m
  (span (H*S)+span (S*2^M))

theorem run {G M b H D w : ℕ} (base : ℕ) (src : Fin (chunks G M)→Expr) (m : Memory w)
    (state : Fin (H*S)→Fin G→Cell 1)
    (old : ∀c v,(src c).eval m (v.val:Word w)=((data (M:=M) state (v,c)).val:Word w))
    (low : ∀c,(src c).Fits w base) (room : endAddress board r depth base H M<2^w) :
    let top:=endAddress board r depth base H M
    let done:=memory board r depth base H M D b m
    let p:=program board r depth base H M D b w
    p.Exec m done (4+10*(span (H*S)+span (S*2^M))) ∧
    (∀c,(dataExpr board r depth base H M (src c)).Fits w top) ∧
    (∀c (v : Fin (H*S)),(dataExpr board r depth base H M (src c)).eval done (v.val:Word w)=
      ((data (M:=M) (fun a g=> (bits board r depth D
        ((finProdFinEquiv.symm a : Fin H×Fin S).2) (state a g):Cell b)) (v,c)).val:Word w)) ∧
    (∀u,u<base ∨ top≤u→done u=m u) ∧ DescentStaticWordColumn.names p=15*(span (H*S)+span (S*2^M)+1) ∧ CheapCode p :=by
  intro top done p
  have space : base+(span (H*S)+span (S*2^M))<2^w:=by simpa [endAddress,start,Nat.add_assoc] using room
  have prop : (cols board r depth base H).Fits w top:=
    ⟨span_pos _,by change span (H*S)<2^w; omega,
      by change base+span (H*S)≤base+span (H*S)+span (S*2^M); exact Nat.le_add_right ..⟩
  have fixed : (book board r depth base H M).Fits w top:=
    ⟨span_pos _,by change span (S*2^M)<2^w; omega,le_rfl⟩
  have baseTop : base≤top:=by dsimp [top,endAddress,start];omega
  have stable (a : ℕ) (away : a<base ∨ top≤a) : done a=m a:=by
    apply DescentStaticWordColumn.frame
    simpa [top,endAddress,start,Nat.add_assoc] using away
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,fun c=>⟨fixed,⟨prop,trivial⟩,ProtocolRAMGeneratedWrite.fits_mono _ baseTop (low c)⟩,
    ?_,stable,DescentStaticWordColumn.names_mount ..,?_⟩
  · intro c v
    let shape:=(finProdFinEquiv.symm v : Fin H×Fin S).2
    let x:=data (M:=M) state (v,c)
    let ix:=finProdFinEquiv (shape,(Fin.cast (by simp) x:Fin (2^M)))
    have ixAt : ix.val=shape.val*2^M+x.val:=by simp [ix,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    have small:=v.isLt.trans_le (span_ge (H*S))
    have mid : v.val< span (H*S)+span (S*2^M):=small.trans_le (Nat.le_add_right ..)
    have ofst : done (base+v.val)=(shape.val*2^M:ℕ):=by
      dsimp only [done,memory]
      rw [DescentStaticWordColumn.read _ _ _ _ mid];simp [constants,small,headers,v.isLt,shape]
    have jump : done ((start board r depth base H)+ix.val)=(table board r depth D b M ix.val:Word w):=by
      have under:=ix.isLt.trans_le (span_ge (S*2^M))
      dsimp only [done,memory]
      rw [start,Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ (Nat.add_lt_add_left under _)]
      simp [constants]
    rw [show (dataExpr board r depth base H M (src c)).eval done (v.val:Word w)=
      (book board r depth base H M).read done (((cols board r depth base H).read done (v.val:Word w))+
        (src c).eval done (v.val:Word w)) by rfl,
      bank_read _ _ small prop,show (cols board r depth base H).base=base by rfl,ofst,
      ProtocolRAM.eval_below _ _ m done (low c) (fun a ha=>stable a (.inl ha)),
      old c v,←Nat.cast_add,←ixAt,bank_read _ _ (ix.isLt.trans_le (span_ge _)) fixed,
      show (book board r depth base H M).base=start board r depth base H by rfl,jump]
    apply congrArg (fun j : ℕ=>(j:Word w))
    have unpack : finProdFinEquiv.symm ix=(shape,(Fin.cast (by simp) x : Fin (2^M))) :=
      finProdFinEquiv.symm_apply_apply _
    unfold table
    rw [dite_eq_left ix.isLt]
    change (encode b M (fun t => bits board r depth D (finProdFinEquiv.symm ix).1
      ((encode 1 M).symm (Fin.cast (by simp) (finProdFinEquiv.symm ix).2) t))).val=_
    rw [unpack]
    change (encode b M (fun t => bits board r depth D shape ((encode 1 M).symm x t))).val=_
    apply congrArg Fin.val
    unfold x data
    rw [Equiv.symm_apply_apply]
    apply congrArg (encode b M)
    funext a
    by_cases yes : c.val*M+a.val<G
    · simp only [dite_eq_left yes]
      rfl
    · simp [yes,bits]
  · apply DescentStaticWordColumn.cheap

end
end Hierarchy.DescentResetTrunkChip

end OAI
