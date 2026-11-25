import OAI.Hierarchy.DescentTerminalLeafPrice
import OAI.Hierarchy.DescentTerminalLeafFold
import OAI.Hierarchy.DescentTerminalHeaderScatter
import OAI.Hierarchy.DescentTerminalChronologicalIssue

namespace OAI
/-! # The bounded sparse control word stream in true paid-row, owner and operand order -/
namespace Hierarchy.DescentTerminalLeafFold
open DescentTerminalPrintedFields DescentTerminalLeafDigits DescentTerminalChronologicalBooks
open DescentTerminalRowBooks DescentKernelHistory DescentTerminalRecipeRows
open scoped Classical BigOperators
noncomputable section
variable {q t V H N A w pool cap : ℕ}
local notation "C" => Control q t H N A w V
variable (tape : Fin pool→Option (Control q t H N A w V))

def rank : Leaves tape ↪ ℕ where
  toFun a:=(finProdFinEquiv (a.1,fieldsOrder V H N A a.2.2.val)).val
  inj' := by
    rintro ⟨i,⟨c,h⟩,⟨k,live⟩⟩ ⟨j,⟨b,f⟩,⟨z,ok⟩⟩ bound
    have eq:=finProdFinEquiv.injective (Fin.ext bound)
    have ij : i=j := congrArg Prod.fst eq
    subst j
    have co := congrArg Prod.snd eq
    obtain rfl: c=b:=Option.some.inj (h.symm.trans f)
    obtain rfl: k=z:=(fieldsOrder V H N A).injective co
    rfl

def ord := DescentTerminalChronologicalBooks.ordinal (rank tape)
def chosen (i : Fin cap) := if h : i.val<Fintype.card (Leaves tape) then some ((ord tape).symm ⟨i.val,h⟩) else none

theorem choose_unique (size : Fintype.card (Leaves tape) ≤ cap) (z : Leaves tape) :
    ∃!i : Fin cap,chosen tape i=some z := by
  let k:=ord tape z
  refine ⟨k.castLE size,?_,?_⟩
  · have inside : (k.castLE size).val<Fintype.card (Leaves tape) := k.isLt
    change (if hk : (k.castLE size).val<Fintype.card (Leaves tape) then
      some ((ord tape).symm ⟨(k.castLE size).val,hk⟩) else none)=some z
    rw [dite_eq_left inside]
    exact congrArg some ((ord tape).symm_apply_apply z)
  intro i atPos
  unfold chosen at atPos
  split at atPos
  next h=>
    have back:=congrArg (ord tape) (Option.some.inj atPos)
    exact Fin.ext (by simpa [k] using congrArg Fin.val back)
  next=>contradiction

private theorem occupied_count (o : Option (Control q t H N A w V)) (tidy : ∀c,o=some c → Tidy c) :
    Fintype.card ((c : {x : Control q t H N A w V // o=some x}) ×
      {j : Coord V H N A // (digit (emit c.val) j).val≠0}) ≤ (o.map expense).getD 0 := by
  classical
  cases o with
  | none=>
    let : IsEmpty {x : Control q t H N A w V // (none : Option _) = some x} :=
      ⟨fun x=>Option.some_ne_none x.val x.property.symm⟩
    simp []
  | some c=>
    let cc : {x : Control q t H N A w V // some c = some x} := ⟨c,rfl⟩
    rw [Fintype.card_sigma,Finset.sum_eq_single_of_mem cc (Finset.mem_univ cc)]
    · exact sparse_count c (tidy c rfl)
    · intro j _ ne
      exact (ne (Subtype.ext (Option.some.inj j.property).symm)).elim

theorem event_count (tidy : ∀i c,tape i=some c → Tidy c) :
    Fintype.card (Leaves tape) ≤ ∑i : Fin pool,((tape i).map expense).getD 0 := by
  unfold Leaves
  rw [Fintype.card_sigma]
  exact Finset.sum_le_sum fun i _=>occupied_count (tape i) (tidy i)

section Archive
variable {t0 : Site} (qp : 0<q) (h : ∀v : Fin t0.nodes,Recipe (Fin t) (Fin (t0.arity v)))
 (birth : Birth h) (hH : ∀v,Fintype.card (h v).Hidden ≤ H) (hN : ∀v,Fintype.card (h v).Node ≤ N)
 (hA : ∀v u,(h v).arity u≤A) (hw : ∀v x,(h v).width x≤w) (hV : t0.nodes≤V)
local notation "ctl" => DescentTerminalChronologicalBooks.control qp h birth hH hN hA hw hV
theorem chronological_tidy (r : Fin (t0.rows q)) : Tidy (ctl r) := by
  intro v k a n f eq j late
  let host:=((owner qp r).symm v).val
  let node:=(ordinal (birth.atom host)).symm k
  change some ((h host).tag node,⟨(h host).arity node,Nat.lt_succ_of_le (hA host node)⟩,_) = some (a,n,f) at eq
  cases eq
  have outside : ¬j.val<(h host).arity node := Nat.not_lt.mpr late
  change (if within : j.val<(h host).arity node then
    some (Sum.map (fun x=>(Site.target qp ⟨host,x⟩).2) (ordinal (birth.hidden host))
      ((h host).operand node ⟨j.val,within⟩)) else none) = none
  exact dite_eq_right outside

theorem chronological_expense (r : Fin (t0.rows q)) :
    expense (ctl r)=1+∑ v : {v : Fin t0.nodes // t0.descriptor qp v=r},
      (2+Fintype.card (h v.val).Hidden+∑u : (h v.val).Node,(2+(h v.val).arity u)) := by
  unfold expense
  congr 1
  rw [←(owner qp r).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  let v:=((owner qp r).symm i).val
  let rank:=ordinal (birth.atom v)
  let cost (u : (h v).Node) : ℕ := 2 + (h v).arity u
  exact congrArg (fun total : ℕ => 2 + Fintype.card (h v).Hidden + total)
    (rank.symm.sum_comp cost)

end Archive
end
end Hierarchy.DescentTerminalLeafFold

end OAI
