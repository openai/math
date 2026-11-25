import OAI.Hierarchy.TaggedShorterGroups
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket
import OAI.ThreeFlat.Diagonal.TraceLocalNetwork

namespace OAI
/-! # Reading fixed-slot occupancy from the native candidate masks -/

noncomputable section
namespace Hierarchy.TaggedShorterMaskOR
open ThreeFlat Routing CallPool Diagonal TraceWords TracePair
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TaggedShorterGroups
open scoped Classical

variable {G : Type} [Fintype G] {D B M : ℕ} {F : Type*}

def arity (D B : ℕ) : Option G → ℕ
  | none => 0
  | some _ => poolBatchCount D B

def masks (mask : Fin (capacity G D B M) × Bool → Fin D → Bool) :
    (g : Option G) → Bool → Fin D → Fin (arity D B g) → Bool
  | none, _, _, j => j.elim0
  | some g, side, x, j => mask (board G D B M ⟨g,j⟩,side) x

def used (size : G → ℕ) (place : ∀g,Bool → Fin (size g) ↪ Fin D) :
    Option G → Bool → Fin D → Bool
  | none,_,_ => false
  | some g,side,x => decide (x ∈ Set.range (place g side))

theorem used_iff (size : G → ℕ) (bound : ∀g,size g≤D) (hb : 0<B) (M : ℕ)
    (place : ∀g,Bool → Fin (size g) ↪ Fin D) (g : Option G) (s : Bool) (x : Fin D) :
    (∃ j,masks (groupMask size bound B M place) g s x j=true) ↔ used size place g s x=true := by
  cases g with
  | none => simp [arity,used]
  | some g =>
    change (∃ j : Fin (poolBatchCount D B),groupMask size bound B M place (board G D B M ⟨g,j⟩,s) x=true) ↔ _
    simp only [used,decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj⟩
      change decide (_ ∈ _) = true at hj
      obtain ⟨⟨⟨k,u⟩,h⟩,e⟩ := of_decide_eq_true hj
      have key : k.1=g := congrArg Sigma.fst ((board G D B M).injective h)
      rcases k with ⟨g',b⟩
      change g'=g at key
      subst g'
      exact ⟨u.val,e⟩
    · rintro ⟨i,rfl⟩
      let k := batchIndex hb g i
      let j := batchAddress B bound k
      refine ⟨j.2,?_⟩
      apply decide_eq_true
      exact ⟨⟨⟨k,⟨i,rfl⟩⟩,rfl⟩,rfl⟩

private def allOff (t : ℕ) : Expr (Option (Fin t)) :=
  allBits (fun j=>.not (.input (some j)))

private def test (t : ℕ) : Expr (Option (Fin t)) :=
  same (.input none) (.not (allOff t))

def network (F : Type*) [Zero F] [One F] (t : ℕ) :
    BitNetwork F (Fintype.card (Option (Fin t))) :=
  TraceCircuit.localNetwork (fun _ : Fin 1=>formulaPacket (test t)) (Fintype.equivFin _)
    (fun _ b=>if b then 1 else 0)

theorem value [CommRing F] (t : ℕ) (x : Option (Fin t) → Bool) :
    TypedWiring.value (network F t) x = if x none=decide (∃j,x (some j)=true) then 1 else 0 := by
  have off : (allOff t).eval x=true ↔ ∀j,x (some j)=false := by simp [allOff,Expr.eval]
  have eff : (test t).eval x=true ↔ x none=decide (∃j,x (some j)=true) := by
    simp only [test,same_true,Expr.eval]
    by_cases yes : ∃ j,x (some j)=true
    · have ne : (allOff t).eval x=false := by
        cases h : (allOff t).eval x with
        | false => rfl
        | true =>
          obtain ⟨j,hj⟩ := yes
          have no := off.mp h j
          simp [hj] at no
      simp [ne,yes]
    · have all : (allOff t).eval x=true := off.mpr (by simpa using yes)
      simp [all,yes]
  simp only [TypedWiring.value,network,TraceCircuit.localNetwork_eval,Fin.prod_univ_one,
    Function.comp_def,Equiv.symm_apply_apply,formulaPacket_eval,eff]

theorem checks [CommRing F] (size : G → ℕ) (bound : ∀g,size g≤D) (hb : 0<B) (M : ℕ)
    (place : ∀g,Bool → Fin (size g) ↪ Fin D) (g : Option G) (s : Bool) (x : Fin D) (flag : Bool) :
    TypedWiring.value (network F (arity D B g))
      (fun p=>p.elim flag (masks (groupMask size bound B M place) g s x)) =
      if flag=used size place g s x then 1 else 0 := by
  rw [value]
  have digit : decide (∃j,masks (groupMask size bound B M place) g s x j=true)=used size place g s x := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using (used_iff size bound hb M place g s x)
  simp only [Option.elim_none,Option.elim_some]
  by_cases ok : flag=used size place g s x
  · exact (ite_eq_left (ok.trans digit.symm)).trans (ite_eq_left ok).symm
  · exact (ite_eq_right (fun h=>ok (h.trans digit))).trans (ite_eq_right ok).symm

theorem cells [Zero F] [One F] (t : ℕ) : (network F t).cells≤24*t+49 := by
  have off := allBits_size_le (fun j : Fin t => (Expr.not (.input (some j)) : Expr (Option (Fin t))))
    (s:=2) (fun _=>Nat.le_refl 2)
  simp only [network,TraceCircuit.localNetwork_cells,Fin.sum_univ_one]
  apply (Nat.add_le_add_right (formulaPacket_size_le (test t)) 1).trans
  simp only [test,same_size,Expr.size,allOff]
  omega

theorem fee [Zero F] [One F] (t : ℕ) :
    (network F t).cells + (network F t).internal ≤ 48*t+98 := by
  have workspace : (network F t).internal ≤ (network F t).cells := by
    change (TraceCompose.gather (fun _ : Fin 1 => formulaPacket (test t))).size ≤
      (TraceCompose.gather (fun _ : Fin 1 => formulaPacket (test t))).size + 1
    omega
  have bound := cells (F:=F) t
  omega

end Hierarchy.TaggedShorterMaskOR

end
end OAI
