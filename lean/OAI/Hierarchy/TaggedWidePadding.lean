import OAI.ThreeFlat.Diagonal.TraceWordOrder
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket
import OAI.ThreeFlat.Diagonal.TraceLocalNetwork
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Canonical zeros for unused ordinary site and stack payload bits -/

noncomputable section
namespace Hierarchy.Tagged.WidePadding
open ThreeFlat Routing Diagonal TraceWords TracePair
open Computability.VPVNP.BurstRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open scoped BigOperators Classical

variable {F V : Type*} {b n : ℕ} [Fintype V]

/-- Each physical bit has a public absolute column in its original port,
an immutable payload pin, and read pins for the port activity and true
width. The width needs only enough low bits for that port's maximum width. -/
structure Ports (V : Type*) (n b : ℕ) where
  col : Fin n → Word b
  live : Fin n → V
  width : Fin n → Fin b → V
  payload : Fin n → V

def Ports.check (p : Ports V n b) (i : Fin n) : Expr V :=
  .or (.not (.input (p.payload i))) (.and (.input (p.live i))
    (lessWord (fun j=>.const (bits (p.col i) j)) (fun j=>.input (p.width i j))))

def Ports.network [Zero F] [One F] (p : Ports V n b) : BitNetwork F (Fintype.card V) :=
  TraceCircuit.localNetwork (fun i=>formulaPacket (p.check i)) (Fintype.equivFin V)
    (fun _ z=>if z then 1 else 0)

theorem Ports.eval [CommRing F] (p : Ports V n b) (x : V → Bool) (width : Fin n → Word b)
    (reads : ∀ i j,x (p.width i j)=bits (width i) j) :
    TypedWiring.value (p.network (F:=F)) x =
      if ∀ i,x (p.payload i)=true → x (p.live i)=true ∧ p.col i<width i then 1 else 0 := by
  have hit (i : Fin n) : (p.check i).eval x = true ↔
      (x (p.payload i)=true → x (p.live i)=true ∧ p.col i<width i) := by
    have ord := lessWord_at (fun j=>Expr.const (bits (p.col i) j)) (fun j=>Expr.input (p.width i j))
      x (p.col i) (width i) (fun _=>rfl) (reads i)
    cases hd : x (p.payload i) <;> cases hl : x (p.live i) <;>
      simp [Ports.check,Expr.eval,ord,hd,hl]
  simp [Ports.network,TypedWiring.value,TraceCircuit.localNetwork_eval,formulaPacket_eval,
    Function.comp_def,Fintype.prod_boole,hit]

theorem Ports.cost [Zero F] [One F] (p : Ports V n b) :
    (p.network (F:=F)).cells+(p.network (F:=F)).internal ≤ n*(200*b+65) := by
  let packet := fun i=>formulaPacket (p.check i)
  have bound (i : Fin n) : (packet i).1 ≤ 100*b+32 := by
    have ord := lessWord_size (fun j : Fin b=>(Expr.const (bits (p.col i) j) : Expr V))
      (fun j=>Expr.input (p.width i j)) (s:=1) (fun _=>le_rfl) (fun _=>le_rfl)
    have h := formulaPacket_size_le (p.check i)
    simp only [Ports.check,Expr.size] at h
    change (formulaPacket (p.check i)).1 ≤ _
    unfold Ports.check
    omega
  have total : (∑ i,(packet i).1) ≤ n*(100*b+32) := by
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>bound i)
  have internal : (p.network (F:=F)).internal = ∑ i,(packet i).1 :=
    TraceCompose.gather_size packet
  rw [internal,Ports.network,TraceCircuit.localNetwork_cells]
  change ((∑ i,(packet i).1)+n)+(∑ i,(packet i).1) ≤ _
  calc
    _ ≤ (n*(100*b+32)+n)+n*(100*b+32) := Nat.add_le_add (Nat.add_le_add_right total n) total
    _ = _ := by ring

/-- Extending an active data assignment by zeros creates exactly the
physically padded port word. This includes all trailing high bits of the
final partial subslot. -/
def pad (used : Fin n → Prop) (x : {i // used i} → Bool) (i : Fin n) : Bool :=
  if h : used i then x ⟨i,h⟩ else false

theorem sum_padded [CommSemiring F] (used : Fin n → Prop) (φ : (Fin n → Bool) → F) :
    (∑ x : Fin n→Bool, if ∀ i,x i=true → used i then φ x else 0) =
      ∑ a : {i // used i}→Bool, φ (pad used a) := by
  classical
  let emb : ({i // used i} → Bool) ↪ (Fin n → Bool) :=
    ⟨pad used,fun a c eqn=>funext fun i=>by simpa [pad,i.property] using congrFun eqn i.val⟩
  let weight (x : Fin n → Bool) := if ∀ i,x i=true → used i then φ x else 0
  have admissible (a : {i // used i}→Bool) (i : Fin n) : emb a i=true → used i := by
    change pad used a i=true → used i
    by_cases h : used i <;> simp [pad,h]
  have covered (x : Fin n → Bool) (ok : ∀ i,x i=true → used i) : x ∈ Finset.univ.map emb := by
    refine Finset.mem_map.mpr ⟨fun i=>x i.val,Finset.mem_univ _,funext fun i=>?_⟩
    change pad used (fun i=>x i.val) i = x i
    by_cases h : used i
    · simp [pad,h]
    · have blank : x i=false := by cases hx : x i <;> simp_all
      simp [pad,h,blank]
  change (∑ x,weight x)=_
  calc
    _ = ∑ x ∈ Finset.univ.map emb,weight x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ missing
      exact ite_eq_right (fun ok=>missing (covered x ok))
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro a _
      exact ite_eq_left (admissible a)

end Hierarchy.Tagged.WidePadding

end
end OAI
