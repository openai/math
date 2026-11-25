import OAI.Hierarchy.DescentDatedNodeMetadataChart
import OAI.Hierarchy.DescentResetNodeBooks
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Checkpoint every occupied-node flag and flattened arity in the successor input layout -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentStaticWordColumn
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : DescentDatedNodeMetadata.Chart)

abbrev Input := Fin 2→Fin v.blocks→Fin v.nodes→Expr

def gather (src : v.Input) (j : Fin v.jobs) : Expr :=
  let p : Fin v.names×Fin v.nodes:=finProdFinEquiv.symm j
  let f : Fin 2×Fin v.blocks:=finProdFinEquiv.symm p.1
  src f.1 f.2 p.2

def reads (base : ℕ) (src : v.Input) :=ProbeStage.Native.columns v.rows base (List.ofFn (v.gather src))
def packed (base w : ℕ) :=DescentResetNodeBooks.program (v.scalarEnd base) base v.names v.nodes v.hosts v.groups v.bits v.lanes w
def program (base w : ℕ) (src : v.Input) :=(ProtocolRAM.program w (v.reads base src)).seq (v.packed base w)
def ticks (base : ℕ) (src : v.Input) :=clock (v.reads base src)+DescentResetNodeBooks.ticks (v.scalarEnd base) base v.names v.nodes v.hosts v.groups v.bits v.lanes
def contents (base : ℕ) (src : v.Input) (m : Memory w) :=result (v.reads base src) m
def image (base : ℕ) (src : v.Input) (m : Memory w) :=DescentResetNodeBooks.image (v.scalarEnd base) base v.names v.nodes v.hosts v.groups v.bits v.lanes (v.contents base src m)

theorem cheap (base w : ℕ) (src : v.Input) : CheapCode (v.program base w src) :=by
  unfold program packed
  apply cheap_seq
  · apply program_cheap
  · apply DescentResetNodeBooks.cheap

theorem inputs_fit (base : ℕ) (src : v.Input) (room : ∀f x n,(src f x n).Fits w base) :
    ∀e∈List.ofFn (v.gather src),e.Fits w base :=by
  intro e h;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp h;apply room

theorem any (base : ℕ) (src : v.Input) (m : Memory w) (early : ∀f x n,(src f x n).Fits w base)
    (room : v.endAddress base<2^w) : (v.program base w src).Exec m (v.image base src m) (v.ticks base src) ∧
    (∀a,a<base ∨ v.endAddress base≤a→v.image base src m a=m a) ∧ CheapCode (v.program base w src) :=by
  let terms:=List.ofFn (v.gather src)
  have length_ : terms.length=v.jobs:=List.length_ofFn
  have hi : v.scalarEnd base≤v.endAddress base:=((Nat.le_add_right _ (max v.dictionary v.rounded)).trans
    (Nat.le_add_right _ (v.names*v.rows))).trans (Nat.le_add_right ..)
  have bound : base+terms.length*v.rows<2^w:=by rw [length_];exact hi.trans_lt room
  have one : (ProtocolRAM.program w (v.reads base src)).Exec m (v.contents base src m) (clock (v.reads base src)):=
    ProbeStage.Native.columns_exec terms m (ProbeStage.Native.columns_safe (n:=v.rows) terms (le_refl base)
      (v.inputs_fit base src early) bound)
  have two:=DescentResetNodeBooks.any (v.scalarEnd base) base v.names v.nodes v.hosts v.groups v.bits v.lanes
    (v.contents base src m) le_rfl room
  refine ⟨one.then two.1,?_,v.cheap base w src⟩
  intro u away
  apply (two.2 _ (away.imp_left (fun lo=>lo.trans_le (Nat.le_add_right ..)))).trans
  have after : u<base ∨ base+terms.length*v.rows≤u:=by
    rw [length_];exact away.imp_right (hi.trans ·)
  exact ProbeStage.Native.columns_frame terms m after

theorem issued (base : ℕ) (src : v.Input) (m : Memory w) (early : ∀f x n,(src f x n).Fits w base)
    (room : v.endAddress base<2^w) (X : Fin 2→Fin v.blocks→Fin v.nodes→Fin v.hosts→Fin v.groups→Cell v.bits)
    (observed : ∀f x n, Source (src f x n) (X f x n) v.lanes m) (f : Fin 2) (x : Fin v.blocks) :
    Reads (v.bank base f x) (fun h g=>encode v.bits v.nodes (fun n=>X f x n h g)) v.lanes (v.image base src m) :=by
  let Y:=fun (p : Fin v.names) (n : Fin v.nodes)=>X (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 n
  let terms:=List.ofFn (v.gather src)
  have len : terms.length=v.jobs:=List.length_ofFn
  have raw (p : Fin v.names) (n : Fin v.nodes) :
      Reads (DescentResetNodeBooks.scalar base v.nodes v.hosts v.groups v.lanes p.val n) (Y p n) v.lanes (v.contents base src m) :=by
    intro r
    let j:=finProdFinEquiv (p,n)
    have jFits : j.val<terms.length:=by rw [len];exact j.isLt
    have word:=ProbeStage.Native.columns_read terms m (le_refl base) (v.inputs_fit base src early) j.val jFits (row _ _ _ r)
    have live : terms[j.val]=src (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 n:=by
      simp only [terms,List.getElem_ofFn]
      change v.gather src j=src (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 n
      simp only [gather,j,Equiv.symm_apply_apply]
    rw [live] at word
    have atIndex : j.val=p.val*v.nodes+n.val:=by simp [j,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
    rw [atIndex] at word
    exact word.trans (observed _ _ _ r)
  have final:=DescentResetNodeBooks.posted (v.scalarEnd base) base v.names v.nodes v.hosts v.groups v.bits v.lanes
    (v.contents base src m) le_rfl room Y raw (v.slot f x)
  change Reads (v.bank base f x) (fun h g=>encode v.bits v.nodes (fun n=>Y (v.slot f x) n h g)) v.lanes (v.image base src m) at final
  simpa only [Y,slot,Equiv.symm_apply_apply] using final

theorem valid (base : ℕ) (room : v.endAddress base<2^w) (f : Fin 2) (x : Fin v.blocks) :
    (v.bank base f x).Fits w (v.endAddress base) ∧ v.rows≤(v.bank base f x).size :=
  DescentResetNodeBooks.placed (v.scalarEnd base) v.names v.nodes v.hosts v.groups v.bits v.lanes (v.slot f x) room

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
