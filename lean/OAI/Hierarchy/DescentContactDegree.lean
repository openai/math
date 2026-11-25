import OAI.Hierarchy.DescentBinaryContact

namespace OAI
/-! # Three physical port roles and the exact size of the fallback router -/

namespace Hierarchy.DescentContactTree.Physical
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {I : Type} [Fintype I] (dest : I→ℕ→Bool) (wt : I→ℕ) {D h : ℕ}
private abbrev Inc (h : ℕ) := Terminal h ⊕ (Edge h × Bool)

private def owns : Inc h → Site h
  | .inl (.inl _) => ⟨0,finZeroElim⟩
  | .inl (.inr v) => ⟨Fin.last h,v⟩
  | .inr (⟨k,v⟩,true) => ⟨k.succ,v⟩
  | .inr (⟨k,v⟩,false) => ⟨k.castSucc,fun i=>v i.castSucc⟩

private def role : Inc h → Option Bool
  | .inl (.inl _) => none
  | .inl (.inr _) => some false
  | .inr (_,true) => none
  | .inr (⟨k,v⟩,false) => some (v (Fin.last k.val))

private def readInput (k : Fin (h+1)) : Node k.val → Inc h :=
  Fin.cases (fun _=>.inl (.inl ())) (fun j v=>.inr (⟨j,v⟩,true)) k

private def readOutput (k : Fin (h+1)) (b : Bool) : Node k.val → Inc h :=
  Fin.lastCases (fun v=>.inl (.inr v)) (fun j v=>.inr (⟨j,Fin.lastCases b v⟩,false)) k

private def reconstruct (s : Site h) : Option Bool → Inc h
  | none => readInput s.1 s.2
  | some b => readOutput s.1 b s.2

private theorem whole {k : ℕ} (v : Node (k+1)) :
    Fin.lastCases (v (Fin.last k)) (fun i=>v i.castSucc)=v := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i <;> simp

private theorem faithful (p : Inc h) : reconstruct (owns p) (role p)=p := by
  rcases p with (⟨⟩|v)|⟨⟨k,v⟩,(_|_)⟩ <;> simp [owns,role,reconstruct,readInput,readOutput,whole] <;> rfl

private theorem degree_eq (v : Site h) : (graph dest wt D h).bitDegree v =
    Fintype.card {p : Inc h // owns p=v} := by
  let g := graph dest wt D h
  let attached : Inc h → Site h :=
    Sum.elim g.attach (fun eb => if eb.2 then g.dst eb.1 else g.src eb.1)
  have same (p : Inc h) : attached p = owns p := by
    rcases p with (⟨⟩|q)|⟨⟨k,q⟩,(_|_)⟩ <;> rfl
  unfold Network.bitDegree
  refine (Fintype.card_of_subtype _ (p := fun p : Inc h => owns p=v) ?_).symm
  intro p
  constructor
  · intro mem
    exact (same p).symm.trans (Finset.mem_filter.mp mem).2
  · intro eqv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(same p).trans eqv⟩

theorem degree (v : Site h) : (graph dest wt D h).bitDegree v≤3 := by
  rw [degree_eq]
  have inj : Function.Injective (fun p : {p : Inc h // owns p=v}=>role p.val) := by
    intro p q same
    apply Subtype.ext
    calc
      p.val = reconstruct (owns p.val) (role p.val) := (faithful p.val).symm
      _ = reconstruct (owns q.val) (role q.val) :=
        congrArg₂ reconstruct (p.property.trans q.property.symm) same
      _ = q.val := faithful q.val
  simpa using Fintype.card_le_of_injective _ inj

private theorem sum_nodes (k : ℕ) : (∑j : Fin k,2^j.val)+1=2^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Fin.sum_univ_castSucc,pow_succ];simpa using (by omega :
      (∑ j : Fin k,2^j.val)+2^k+1=2^k*2)

theorem sites : Fintype.card (graph dest wt D h).Site+1=2^(h+1) := by
  change Fintype.card (Site h)+1=_
  simp only [Site,Node,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  exact sum_nodes (h+1)

theorem edges : Fintype.card (graph dest wt D h).Edge+2=2^(h+1) := by
  change Fintype.card (Edge h)+2=_
  simp only [Edge,Node,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  simp_rw [pow_succ,←Finset.sum_mul]
  have sum := sum_nodes h
  omega

/-- Includes every edge of the physical network, the input root and all
padded destination pins, each charged according to its actual word length. -/
theorem all_wires : (∑e,(graph dest wt D h).width e)+(∑p : Terminal h,terminalWidth dest wt h p)=
    (h+2)*(∑i,wt i) := by rw [wire_cost,port_cost];ring

end
end Hierarchy.DescentContactTree.Physical

end OAI
