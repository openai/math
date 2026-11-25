import OAI.Hierarchy.TaggedWidePadding

namespace OAI
/-! # Unique data-dependent compaction mask from the true width field of every role -/

noncomputable section
namespace Hierarchy.Probe.ApertureMask
open ThreeFlat Routing Diagonal TraceWords TracePair
open Computability.VPVNP.BurstRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open scoped Classical BigOperators Fin.CommRing

abbrev Pins (n d b : ℕ) := (Fin n×Fin b) ⊕ Fin (n*d)

def col {n d : ℕ} (i : Fin (n*d)) := (finProdFinEquiv.symm i : Fin n×Fin d).2
def role {n d : ℕ} (i : Fin (n*d)) := (finProdFinEquiv.symm i : Fin n×Fin d).1

def test (n d b : ℕ) (i : Fin (n*d)) : Expr (Pins n d b) :=
  let lt:=lessWord (fun j=>.const (bits ((col i).val:Word b) j)) (fun j=>.input (.inl (role i,j)))
  let on:=Expr.input (.inr i : Pins n d b)
  .or (.and on lt) (.and (.not on) (.not lt))

def network (F : Type*) [Zero F] [One F] (n d b : ℕ) : BitNetwork F (Fintype.card (Pins n d b)) :=
  TraceCircuit.localNetwork (fun i=>formulaPacket (test n d b i)) (Fintype.equivFin _)
    (fun _ v=>if v then 1 else 0)

variable {n d b : ℕ}
def mask (width : Fin n→ℕ) (i : Fin (n*d)) := decide ((col i).val<width (role i))
def pins (width : Fin n→ℕ) (m : Fin (n*d)→Bool) : Pins n d b→Bool :=
  Sum.elim (fun p=>bits (width p.1:Word b) p.2) m

theorem eval (F : Type*) [CommRing F] (width : Fin n→ℕ) (m : Fin (n*d)→Bool)
    (small : ∀i,width i≤d) (room : d<2^b) :
    TypedWiring.value (network F n d b) (pins width m)=if m=mask width then 1 else 0 := by
  have one (i : Fin (n*d)) : (test n d b i).eval (pins width m)=true ↔ m i=mask width i := by
    have cmp:=lessWord_at (fun j=>Expr.const (bits ((col i).val:Word b) j))
      (fun j=>Expr.input (.inl (role i,j) : Pins n d b)) (pins width m)
      ((col i).val:Word b) (width (role i):Word b) (fun _=>rfl) (fun _=>rfl)
    have hi : (col i).val<2^b := (col i).isLt.trans room
    have hw : width (role i)<2^b := (small _).trans_lt room
    have comp : (((col i).val:Word b)<(width (role i):Word b)) ↔ (col i).val<width (role i) := by
      change (((col i).val:Word b).val<(width (role i):Word b).val) ↔ _
      rw [Fin.val_cast_of_lt hi,Fin.val_cast_of_lt hw]
    simp only [pins] at cmp
    cases flag:m i <;> by_cases inRange:(col i).val<width (role i) <;>
      simp [test,Expr.eval,cmp,comp,pins,mask,flag,inRange]
  simp only [network,TypedWiring.value,TraceCircuit.localNetwork_eval,formulaPacket_eval,
    Function.comp_def,Equiv.symm_apply_apply,Fintype.prod_boole,one]
  congr 1
  exact propext funext_iff.symm

theorem cost (F : Type*) [Zero F] [One F] (n d b : ℕ) :
    (network F n d b).cells+(network F n d b).internal ≤ (n*d)*(500*b+501) := by
  let packet:=fun i=>formulaPacket (test n d b i)
  have per (i : Fin (n*d)) : (packet i).1≤250*b+250 := by
    have cmp:=lessWord_size (fun j : Fin b=>(Expr.const (bits ((col i).val:Word b) j) : Expr (Pins n d b)))
      (fun j=>.input (.inl (role i,j))) (s:=1) (fun _=>le_rfl) (fun _=>le_rfl)
    change (formulaPacket (test n d b i)).1≤_
    apply (formulaPacket_size_le (test n d b i)).trans
    simp only [test,Expr.size]
    omega
  have total : (∑i,(packet i).1)≤(n*d)*(250*b+250) := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>per i)
  have internal : (network F n d b).internal=∑i,(packet i).1:=TraceCompose.gather_size packet
  rw [internal,network,TraceCircuit.localNetwork_cells]
  change (∑i,(packet i).1)+n*d+(∑i,(packet i).1)≤_
  calc
    _ ≤ (n*d)*(250*b+250)+n*d+(n*d)*(250*b+250) := by omega
    _ = _ := by ring

end Hierarchy.Probe.ApertureMask
end

end OAI
