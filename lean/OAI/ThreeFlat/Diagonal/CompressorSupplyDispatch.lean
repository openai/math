import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.Diagonal.CompressorSupplySelect
import OAI.ThreeFlat.Diagonal.CompressorDemandPair

namespace OAI
/-! # Typed evaluation of the eight supply-edge tests and four survivor selectors -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast

variable {w n : ℕ} (data : Param → Word w) (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs

theorem supply_digit_eq {k : ℕ} (fit : k≤2^w) (i j : Fin k) :
    (i.val:Word w)=(j.val:Word w) ↔ i=j := by
  simp only [Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans_le fit),Fin.val_cast_of_lt (j.isLt.trans_le fit)]

private theorem choose_at {k : ℕ} (xs : List (Fin k)) (edge : F n) (payload : Fin k → F n)
    (i : Fin k) (fit : k≤2^w) (read : V edge=(i.val:Word w)) (found : i∈xs) :
    V (xs.foldr (fun t tail => Formula.select .eq edge (.lit t.val) (payload t) tail) (.lit 0))=V (payload i) := by
  induction xs with
  | nil => simp at found
  | cons a xs ih =>
    by_cases hit : i=a
    · subst a
      simp [Formula.value,Comparison.test,read,Fin.ofNat_eq_cast]
    · have ne := (supply_digit_eq fit i a).not.mpr hit
      simp only [List.foldr_cons,Formula.value,Comparison.test,read,Fin.ofNat_eq_cast,beq_iff_eq,ne,
        ite_false]
      exact ih ((List.mem_cons.mp found).resolve_left hit)

theorem supply_edge_word (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) (i : Fin 8) (h8 : 8≤2^w) (atEdge : V edge=(i.val:Word w)) (col : Fin 4) :
    V (supplyAddress ptr S lay e party edge j col)=
      V (supplyEdgeAddress ptr S lay e party (supplyWidth ptr S e edge) j i col) :=
  choose_at data mem vs _ edge _ i h8 atEdge (List.mem_finRange _)

private theorem route_at {α β : Type*} [DecidableEq β] (xs : List α) (f : α → β) (body : α→Address n)
    (orig : Address n) (t : α) (inj : Function.Injective f) (has : t∈xs) :
    xs.foldr (fun p rest => if f p=f t then body p else rest) orig=body t := by
  induction xs with
  | nil => simp at has
  | cons p xs ih =>
    by_cases same : p=t
    · simp [same]
    · simp only [List.foldr_cons,inj.eq_iff,same,ite_false]
      exact ih ((List.mem_cons.mp has).resolve_left (Ne.symm same))

private theorem route_local {α β : Type*} [DecidableEq β] (xs : List α) (f : α → β) (body : α→Address n)
    (orig : Address n) (edge : β) (none : ∀t, f t≠edge) :
    xs.foldr (fun p rest => if f p=edge then body p else rest) orig=orig := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simp only [List.foldr_cons,none p,ite_false,ih]

private def routes (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n)) (party width j : F n)
    (i : Fin 8) : Address n :=
  (List.finRange 4).foldr (fun t tail => if ShrinkMotif.survivor lay t=i then
    locate (supplyCopies ptr S lay e party width t) j else tail) ![.lit 3,.lit i.val,j,.lit 0]

private theorem party_select (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party width j : F n) (i : Fin 8) (u : Fin 6) (h8 : 8≤2^w) (hp : V party=(u.val:Word w)) (col : Fin 4) :
    V (supplyEdgeAddress ptr S lay e party width j i col)=
    if u=ShrinkMotif.supplySrc i ∨ u=ShrinkMotif.supplyDst i then V (routes ptr S lay e party width j i col) else 0 := by
  have fit : 6≤2^w := by omega
  have nz : (0:Word w)≠1 := by
    apply ne_of_lt
    change 0 < 1 % (2^w)
    simpa only [Nat.mod_eq_of_lt (show 1<2^w by omega)] using Nat.zero_lt_one
  change (if Comparison.eq.test (if Comparison.eq.test (V party) ((ShrinkMotif.supplySrc i).val:Word w) then 1
    else if Comparison.eq.test (V party) ((ShrinkMotif.supplyDst i).val:Word w) then 1 else 0) 1 then
    V (routes ptr S lay e party width j i col) else 0)=_
  by_cases src : u=ShrinkMotif.supplySrc i <;> by_cases dst : u=ShrinkMotif.supplyDst i <;>
    simp [Comparison.test,hp,supply_digit_eq fit,src,dst,nz]

theorem supply_unused (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) (i : Fin 8) (u : Fin 6) (h8 : 8≤2^w)
    (he : V edge=(i.val:Word w)) (hp : V party=(u.val:Word w))
    (away : ¬(u=ShrinkMotif.supplySrc i ∨ u=ShrinkMotif.supplyDst i)) (col : Fin 4) :
    V (supplyAddress ptr S lay e party edge j col)=0 := by
  rw [supply_edge_word data mem vs _ _ _ _ _ _ _ _ h8 he,party_select data mem vs _ _ _ _ _ _ _ i u h8 hp,ite_eq_right away]

theorem supply_absorbed (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) (i : Fin 8) (u : Fin 6) (h8 : 8≤2^w)
    (he : V edge=(i.val:Word w)) (hp : V party=(u.val:Word w))
    (hit : u=ShrinkMotif.supplySrc i ∨ u=ShrinkMotif.supplyDst i)
    (localEdge : ∀t, ShrinkMotif.survivor lay t≠i) (col : Fin 4) :
    V (supplyAddress ptr S lay e party edge j col)=(![3,(i.val:Word w),V j,0] : Fin 4→Word w) col := by
  rw [supply_edge_word data mem vs _ _ _ _ _ _ _ _ h8 he,party_select data mem vs _ _ _ _ _ _ _ i u h8 hp,ite_eq_left hit]
  unfold routes
  rw [route_local _ _ _ _ _ localEdge]
  fin_cases col <;> rfl

theorem supply_survivor (ptr : F n) (S : Graph.Stage) (lay : Bool) (e : Ends (F n))
    (party edge j : F n) (t : Fin 4) (u : Fin 6) (h8 : 8≤2^w)
    (he : V edge=((ShrinkMotif.survivor lay t).val:Word w)) (hp : V party=(u.val:Word w))
    (hit : u=ShrinkMotif.supplySrc (ShrinkMotif.survivor lay t) ∨ u=ShrinkMotif.supplyDst (ShrinkMotif.survivor lay t))
    (col : Fin 4) : V (supplyAddress ptr S lay e party edge j col)=
      V (locate (supplyCopies ptr S lay e party (supplyWidth ptr S e edge) t) j col) := by
  rw [supply_edge_word data mem vs _ _ _ _ _ _ _ _ h8 he,party_select data mem vs _ _ _ _ _ _ _ _ u h8 hp,ite_eq_left hit]
  unfold routes
  rw [route_at _ _ _ _ t (ShrinkMotif.survivor_distinct lay) (List.mem_finRange _)]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
