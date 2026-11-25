import OAI.Hierarchy.DescentTerminalHeaderEventLiterals

namespace OAI
/-! # Native draft-event columns realize both original bounded header scatters -/
namespace Hierarchy.DescentTerminalHeaderDraft
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPaidHeaderEvents DescentTerminalRowArena
open DescentTerminalRecipeRows DescentTerminalChipSource DescentTerminalHeaderScatter
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Both header columns use one event per paid row. The bank's sink is the first
location after the paid positions, also when every position is a gap. -/
def header (n:ℕ) (s:Fixed) (O:Output) (inner outer dest:Bank) (src shift blank:ℕ) : DescentTerminalEmitter.Header :=
  ⟨wires s O inner outer,dest,src,n,n,dest.base+n,shift,blank⟩

variable {w q W H K:ℕ}
def answer (sites : Fin H→Site) (start : GroupRow (q:=q) sites→ℕ)
    (isPublic : GroupRow (q:=q) sites→Bool) (f:Column) (a:GroupRow (q:=q) sites) : ℕ := match f with
  | .active=>1
  | .mode=>if isPublic a then 1 else 0
  | .source=>start a

def emits (sites:Fin H→Site) (wp:0<W) (fit:∀v,(sites v).rows q≤W)
    (bins:Bins (W:=W) (q:=q) sites≤K)
    (s:Fixed) (O:Output) (inner outer dest:Bank) (src shift blank:ℕ) (mem:Memory w)
    (start:GroupRow (q:=q) sites→ℕ) (isPublic:GroupRow (q:=q) sites→Bool)
    (ans:GroupRow (q:=q) sites→Word w)
    (fixed:s.Reads mem (K*W)) (idx:K*W≤2^w) (size:∀c:Column,K*W≤(O.get c).size)
    (columns:∀(c:Column) (i:Fin (K*W)),mem ((O.get c).base+i.val)=
      (((Slots.emitted (K:=K) (sites:=sites) wp fit i).elim 0 (answer sites start isPublic c) : ℕ):Word w))
    (interior:∀a,isPublic a=false→inner.read mem (start a:Word w)=ans a)
    (exterior:∀a,isPublic a=true→(shift:Word w)+outer.read mem (start a:Word w)=ans a)
    (space:K*W<dest.size)
    (readable:(stage (DescentTerminalScatterChip.dest (wires s O inner outer) dest.base (dest.base+K*W))
      (DescentTerminalScatterChip.datum (wires s O inner outer) shift) s.lane).Fits w dest.base) :
    DescentTerminalEmitter.Header.Emits (header (K*W) s O inner outer dest src shift blank)
      mem (DescentTerminalScatterColumns.fixed sites wp bins) ans := by
  let atRow := DescentTerminalScatterColumns.fixed sites wp bins
  let liveAt := Slots.emitted (K:=K) (sites:=sites) wp fit
  have word (c:Column) (i:Fin (K*W)) : (O.get c).read mem (i.val:Word w)=
      (((liveAt i).elim 0 (answer sites start isPublic c) : ℕ):Word w) := by
    simpa [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le idx),Nat.mod_eq_of_lt (i.isLt.trans_le (size c))] using columns c i
  have on (a:GroupRow (q:=q) sites) : liveAt (atRow a)=some a:=Slots.occurrence wp fit bins a
  have placed_ (i:Fin (K*W)) (a:GroupRow (q:=q) sites) (found:liveAt i=some a) : atRow a=i:=
    Slots.placed wp fit bins i a found
  refine ⟨liveAt,fun a=>(atRow a).val,fun a=>(atRow a).val,fun _=>0,start,fun _=>0,isPublic,
    fun a=>⟨atRow a,on a⟩,?_,?_,by simp [header],by simpa [header] using space,by simp [header],readable⟩
  · constructor
    · exact fixed.halfRead
    · exact fixed.laneRead
    · intro i;have got:=word .active i;cases hg:liveAt i <;> simpa [wires,header,hg,answer,Output.get] using got
    · intro i a hit;rw [placed_ i a hit];exact fixed.direct i
    · intro i a hit;exact fixed.blank i
    · intro a;exact fixed.direct _
    · intro a;exact fixed.blank _
    · intro a;simpa only [on,Option.elim_some,answer,Output.get,header,wires] using word .source (atRow a)
    · intro a;simpa only [on,Option.elim_some,answer,Output.get,header,wires] using word .mode (atRow a)
  · constructor
    · intro a
      change s.identity.read mem ((atRow a).val : Word w) + ((0+0 : ℕ) : Word w) =
        ((atRow a).val : Word w)
      rw [fixed.direct (atRow a)]
      exact add_zero _
    · intro a no;simpa [header,wires] using interior a no
    · intro a yes;simpa [header,wires] using exterior a yes

/-- The scalar-side machine may have resumed and written elsewhere. Only the
attained paid addresses are carried from the draft checkpoint. -/
theorem columns_kept (O':Output) {old later:Memory w} {n':ℕ}
    (endAt:ℕ) (compare:∀c:Column,(O'.get c).base+n'≤endAt)
    (fr:∀a<endAt,later a=old a) {x:Column→Fin n'→Word w}
    (oldRead:∀c (i:Fin n'),old ((O'.get c).base+i.val)=x c i) :
    ∀c (i:Fin n'),later ((O'.get c).base+i.val)=x c i := by
  intro c i;exact (fr _ ((Nat.add_lt_add_left i.isLt _).trans_le (compare c))).trans (oldRead c i)


end
end Hierarchy.DescentTerminalHeaderDraft

end OAI
