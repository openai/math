import OAI.ThreeFlat.Diagonal.TickPhaseModel
import OAI.ThreeFlat.Diagonal.TickPhysicalOrder

namespace OAI
/-! # Reading the local team value as a physical matrix entry -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer RotatedChunkGuards
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} (B : Data R c)

/-- The entry on physical pins after multiplying the team, with the inactive
chunk coordinates still supplied by the uniform template. -/
def localValue (t : ℕ) (x y old new : Aux a) : F :=
  let ph := c.phase t
  let g := c.group t
  let sample := if ph=.opening then new else old
  (if old=(fun _=>false) ∧ new=(fun _=>false) ∧ x=y then 1 else 0) +
    (decode P E bits R.base sample).elim 0 (fun v =>
      if (layout B v g).accepts ph true old new then
        if ph=.scan then
          if guard (B.code v g (chunk c t)) (atIndex (before B v g old)) (atIndex (after B v g old)) x y then 1 else 0
        else if x=y then if ph=.evaluate then B.weight v g (before B v g old) (after B v g old) t else 1 else 0
      else 0)

theorem local_entry (t : ℕ) (x y : Ext c a) (oa na : Aux a) :
    (if ∀ j,j≠chunk c t → x j=y j then localValue B t (x (chunk c t)) (y (chunk c t)) oa na else 0) =
    step B t (x,oa) (y,na) := by
  by_cases out : ∀ j, j ≠ chunk c t → x j = y j
  · have extEq : x=y ↔ x (chunk c t)=y (chunk c t) := by
      refine ⟨fun eq => congrFun eq _,fun localEq => funext (fun j => ?_)⟩
      by_cases same : j=chunk c t
      · simpa only [same] using localEq
      · exact out j same
    simp only [localValue,step,ite_eq_left out,extEq,scanKernel,chunkKernel,Finset.mem_singleton,
      Finset.prod_singleton,entry_eq]
  · have ne : x≠y := fun eq => out (fun j _ => congrFun eq j)
    simp only [localValue,step,ite_eq_right out,ne,and_false,ite_false,zero_add,scanKernel,
      chunkKernel,Finset.mem_singleton]
    cases decode P E bits R.base (if c.phase t=.opening then na else oa) <;> simp

theorem physical {I : Type*} [Fintype I] [DecidableEq I] (order : Fin c.chunks ≃ Bool × I) (t : ℕ) :
    (physicalTick (order (chunk c t)).1 (order (chunk c t)).2 (localValue B t)).submatrix
      (TickPhysicalOrder.state order) (TickPhysicalOrder.state order) = step B t := by
  ext ⟨x,oa⟩ ⟨y,na⟩
  exact (TickPhysicalOrder.entry order (chunk c t) (localValue B t) x y oa na).trans
    (local_entry B t x y oa na)

private theorem restrict_prod {U V I : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (e : U ≃ V) (l : List I) (M : I → Matrix V V F) :
    (l.map (fun i => (M i).submatrix e e)).prod = (l.map M).prod.submatrix e e := by
  induction l with
  | nil => simp [Matrix.submatrix_one_equiv]
  | cons i is ih => simp only [List.map_cons,List.prod_cons,ih,Matrix.submatrix_mul_equiv]

/-- Actual template evaluation under the common local team value. Both
endpoints have the physical AUX register set to zero. -/
theorem template {I : Type*} [Fintype I] [DecidableEq I] {n blocks p teams : ℕ}
    (N : BitNetwork F p) (order : Fin c.chunks ≃ Bool × I)
    (slot : Fin blocks → Fin n → I) (active : Fin blocks → Bool)
    (pins : Fin blocks → Fin n → Fin teams → Aux a → Aux a → Aux a → Aux a → Fin p → Bool)
    (duration : blocks*n=c.last+1) (visited : ∀ (i : Fin blocks) (j : Fin n),
      (active i,slot i j)=order (chunk c (i.val*n+j.val)))
    (scalar : ∀ (i : Fin blocks) (j : Fin n) x y oa na,
      teamTick N (pins i) j x y oa na=localValue B (i.val*n+j.val) x y oa na)
    (x y : Ext c a) :
    templateRun N (List.ofFn id) slot active pins (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y) =
      ((List.range (c.last+1)).map (step B)).prod (x,fun _=>false) (y,fun _=>false) := by
  let e := TickPhysicalOrder.state (D:=Aux a) (A:=Aux a) order
  let M t := physicalTick (order (chunk c t)).1 (order (chunk c t)).2 (localValue B t)
  have shape (i : Fin blocks) (j : Fin n) : physicalTick (active i) (slot i j) (teamTick N (pins i) j) =
      M (i.val*n+j.val) := by
    have eq := visited i j
    have team : teamTick N (pins i) j=localValue B (i.val*n+j.val) :=
      funext (fun x => funext (fun y => funext (fun oa => funext (scalar i j x y oa))))
    simp only [M,team,← congrArg Prod.fst eq,← congrArg Prod.snd eq]
  rw [TickPhysicalOrder.template N slot active pins M shape,duration]
  change (((List.range (c.last+1)).map M).prod.submatrix e e) (x,fun _=>false) (y,fun _=>false) = _
  rw [← restrict_prod]
  simp only [e,M,physical]


end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
