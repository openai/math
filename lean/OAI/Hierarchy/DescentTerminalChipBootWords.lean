import OAI.Hierarchy.DescentTerminalAppendixNumbers
import Mathlib.Tactic.FinCases
import OAI.Hierarchy.DescentTerminalEmitterBoot
import OAI.Hierarchy.DescentTerminalEmitter

namespace OAI
/-! # Four original hidden-word views and six immutable terminal chip tables -/
namespace Hierarchy.DescentTerminalChipBootWords
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalBinReaddress DescentTerminalDenseWindow
open DescentTerminalDenseWindowRAM DescentTerminalEmitter ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (K W q p codes:ℕ)
local notation "n" => K*W
local notation "d" => q*(W*p)
local notation "R" => 2^d
local notation "M" => Menus q (W*p)
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "sw" => sliceWidth W q p
local notation "route_" => DescentTerminalBinFormat.address W q

def bank (base:ℕ) (col:Fin 10) : Bank := ⟨base+«begin» K W q p codes col,bits K W q p codes col⟩

private def grab {w size:ℕ} (v:Vector (Word w) size) (i:ℕ) := if h:i<size then v[i] else 0
variable {K W q p}

def words (z:Inputs K W q p→Bool) (w codes:ℕ) (col:Fin 10) (i:ℕ) : Word w :=
  match col.val with
  | 0 => column z false false i
  | 1 => column z false true i
  | 2 => column z true false i
  | 3 => column z true true i
  | 4 => grab (offsets w R R) i
  | 5 => grab (offsets w M (R*R)) i
  | 6 => grab (DescentTerminalDenseWindow.rows w q (W*p)) i
  | 7 => grab (DescentTerminalBinSliceCheap.pointers w c sw) i
  | 8 => grab (advice w p route_) i
  | _ => (((DescentTerminalScalarDispatch.pointers (fun a:Fin codes=>a.val*2^d))[i]?.getD 0):ℕ)

theorem words_static (z z':Inputs K W q p→Bool) (w codes:ℕ) (col:Fin 10) (i:ℕ) (fixed:4≤col.val) :
    words z w codes col i=words z' w codes col i := by
  fin_cases col <;> first | rfl | (exfalso; revert fixed; decide)

def chipBanks (L:DescentTerminalEmitter.Layout) (base empty:ℕ) : Banks :=
  let b:=bank K W q p codes base
  ⟨L.indices.output,L.formats.output,L.plane.raw,b 5,b 4,b 6,L.route.gate,b 1,b 7,b 8,
    ⟨⟨L.scalar,L.indices.output.bits⟩,b 2,b 9⟩,b 0,b 3,empty⟩

variable {w : ℕ} (L:DescentTerminalEmitter.Layout) (base empty:ℕ)
local notation "B" => chipBanks (K:=K) (W:=W) (q:=q) (p:=p) codes L base empty

theorem source (z:Inputs K W q p→Bool) (m:Memory w)
    (read:∀(col:Fin 10) (i:ℕ),i<need K W q p codes col→m ((bank K W q p codes base col).base+i)=words z w codes col i) :
    DescentTerminalEmitter.Boot B m z := by
  constructor
  · intro a b i;cases a <;> cases b
    · exact read 0 _ i.isLt
    · exact read 1 _ i.isLt
    · exact read 2 _ i.isLt
    · exact read 3 _ i.isLt
  · intro u;exact (read 4 _ u.isLt).trans (by change grab (offsets w R R) u.val=_; exact dite_eq_left u.isLt)
  · intro v;exact (read 5 _ v.isLt).trans (by change grab (offsets w M (R*R)) v.val=_; exact dite_eq_left v.isLt)
  · intro v lo hi
    let pair:Fin (R*R):=finProdFinEquiv (lo,hi)
    let at_:Fin (M*(R*R)):=finProdFinEquiv (v,pair)
    have row:=read 6 at_.val at_.isLt
    have addr : v.val*(R*R)+(lo.val*R+hi.val)=at_.val := by
      change _=(hi.val+R*lo.val)+(R*R)*v.val
      ring
    change m ((bank K W q p codes base 6).base+(v.val*(R*R)+(lo.val*R+hi.val)))=_
    rw [addr,row]
    change grab (DescentTerminalDenseWindow.rows w q (W*p)) at_.val=_
    simp only [grab,dite_eq_left at_.isLt,DescentTerminalDenseWindow.rows,Vector.getElem_ofFn,Fin.eta]
    simp only [at_,pair,Equiv.symm_apply_apply]
  · intro a;exact (read 7 _ a.isLt).trans (by change grab (DescentTerminalBinSliceCheap.pointers w c sw) a.val=_; exact dite_eq_left a.isLt)
  · intro a b
    let at_:Fin (2^c*2^sw):=finProdFinEquiv (a,b)
    have row:=read 8 at_.val at_.isLt
    have addr : a.val*2^sw+b.val=at_.val := by
      change _=b.val+2^sw*a.val
      ring
    change m ((bank K W q p codes base 8).base+(a.val*2^sw+b.val))=_
    rw [addr,row]
    change grab (advice w p route_) at_.val=_
    simp only [grab,dite_eq_left at_.isLt,advice,Vector.getElem_ofFn,Fin.eta]
    simp only [at_,Equiv.symm_apply_apply]

theorem scalar_table (z:Inputs K W q p→Bool) (m:Memory w)
    (read:∀ (j : Fin (codes+1)),m ((bank K W q p codes base 9).base+j.val)=words z w codes 9 j.val)
    (j : Fin (codes+1)) : m ((B).scalar.pointer.base+j.val)=
      ((DescentTerminalScalarDispatch.pointers (fun a:Fin codes=>a.val*2^d))[j.val]'(by
        simpa [DescentTerminalScalarDispatch.pointers] using j.isLt):Word w) := by
  rw [show (B).scalar.pointer=bank K W q p codes base 9 by rfl,read]
  simp [words,show j.val<(DescentTerminalScalarDispatch.pointers (fun a:Fin codes=>a.val*2^d)).length by
    simpa [DescentTerminalScalarDispatch.pointers] using j.isLt]


end
end Hierarchy.DescentTerminalChipBootWords

end OAI
