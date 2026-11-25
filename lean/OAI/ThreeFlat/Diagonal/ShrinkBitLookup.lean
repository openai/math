import OAI.ThreeFlat.Diagonal.CompressorSupplyOrigins
import OAI.ThreeFlat.Diagonal.CompressorOriginRead
import OAI.ThreeFlat.Diagonal.CompressorResidentInput

namespace OAI
/-! # Selected-stage and endpoint decoder of the installed shrink bit lookup -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {n w : ℕ} {data : Param → Word w} {mem : Memory w} {regs : Fin n → Word w}
local notation "V" => Formula.value data mem regs

theorem finiteField {k : ℕ} (index : Formula n) (fields : Fin k → Formula n)
    (f : Fin k) (sel : V index=(f.val:Word w)) (fit : k≤2^w) (xs : List (Fin k))
    (inside : f∈xs) :
    V (xs.foldr (fun i tail=>.select .eq index (.lit i.val) (fields i) tail) (.lit 0))=V (fields f) := by
  induction xs with
  | nil=>simp at inside
  | cons a l ih=>
    by_cases eq : f=a
    · subst a;simp [Formula.value,RAM.DescriptorExpr.Comparison.test,sel]
    · have ne : (f.val:Word w)≠(a.val:Word w) := by
        intro e;apply eq;apply Fin.ext
        simpa only [Fin.val_cast_of_lt (f.isLt.trans_le fit),Fin.val_cast_of_lt (a.isLt.trans_le fit)] using
          congrArg Fin.val e
      have tl : f∈l := (List.mem_cons.mp inside).resolve_left eq
      simp only [List.foldr_cons,Formula.value,RAM.DescriptorExpr.Comparison.test,sel,beq_iff_eq]
      exact (ite_eq_right ne).trans (ih tl)

/-- The four fetched cells are selected on the old stage's elected layout. -/
theorem lookup_word (S : Graph.Stage) (sup lay : Bool)
    (ptr incident party edge j field : Formula n) (f : Fin 4)
    (valF : V field=(f.val:Word w)) (fit : 4≤2^w)
    (mode : V (atField (Demand.formulaOps n) ptr selected)=(if lay then 1 else 0)) :
    V (lookup S sup ptr incident party edge j field) =
      V ((if sup then supplyAddress ptr S lay (oldArc ptr S (.load incident)) party edge j
                 else demandAddress ptr S lay (oldArc ptr S (.load incident)) party edge j) f) := by
  unfold lookup
  rw [finiteField _ _ f valF fit _ (List.mem_finRange f)]
  rw [Demand.eval_choose]
  have ne : (0:Word w)≠1 := by
    apply ne_of_lt
    change 0 < 1 % (2^w)
    simpa only [Nat.mod_eq_of_lt (show 1<2^w by omega)] using Nat.zero_lt_one
  cases lay <;> simp [mode,Formula.value,ne]

/-- The actual formula has thirteen registers, and addresses its field as a literal. -/
theorem lookup_compiled (S : Graph.Stage) (sup lay : Bool) (f : Fin 4)
    (mem : Memory w) (r : Fin 13 → Word w) (fit : 4≤2^w)
    (mode : Formula.value (fun _=>0) mem r (atField (Demand.formulaOps 13) (.reg 0) selected)=
      (if lay then 1 else 0)) :
    (((lookup S sup (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit f.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) mem r) =
      Formula.value (fun _=>0) mem r
        ((if sup then supplyAddress (.reg 0) S lay (oldArc (.reg 0) S (.load (.reg 2))) (.reg 3) (.reg 4) (.reg 5)
          else demandAddress (.reg 0) S lay (oldArc (.reg 0) S (.load (.reg 2))) (.reg 3) (.reg 4) (.reg 5)) f) := by
  rw [Formula.eval_compile]
  exact lookup_word S sup lay _ _ _ _ _ _ f rfl fit mode


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
