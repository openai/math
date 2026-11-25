import OAI.ThreeFlat.RAM.HistoryStageBounds
import OAI.ThreeFlat.RAM.ExpressionArgumentReads

namespace OAI
/-! # Physical scratch-bank writes preserve the source words of the stage formula -/

namespace ThreeFlat.RAM.HistoryStageBounds

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr HistoryPartyBatchExec
open HistoryStageRoot HistoryStageBody
open scoped Fin.CommRing
noncomputable section
variable {W : ℕ} (A : HistoryGatherBody.Layout) (cap : ℕ)
    (S : Input) (mem : Memory W) (b : Bank)

/-- The only nonconstant destination expression selects the current cache record and
loads the chronological cursor to obtain its address. -/
private theorem destination_outside (slots : BankCells A cap S mem b) (p : Word W) :
    ∀ x ∈ (destination A cap b).reads Fin.elim0 mem (fun _=>p),
      BankOutside A cap S mem b x := by
  intro x hx
  cases b <;> try { simp [destination,l] at hx }
  have bound := slots.cursor rfl
  have hc : x∈(nodeId A).reads Fin.elim0 mem (fun _=>p) := by
    simpa [destination,cache,a,times,l] using hx
  let addr : Term W 0 1 := l A.nodePorts.cursor
  change x∈(cut addr.load (l 1)).reads Fin.elim0 mem (fun _=>p) at hc
  have same : x=A.nodePorts.cursor := by
    simpa [cut,addr,l,Term.reads_select,Term.reads_binary,Term.reads_load,Fin.val_cast_of_lt bound.1] using hc
  rw [same]
  exact bound.2

/-- Each emitted index selects the true row and column of its bank. The range proof
controls every eager operand read before invoking the certified body on those registers. -/
theorem formula_checks
    (header : ∀ f : Fin 11,numeric mem (args A+f.val)=S.words f)
    (atDest : ∀ a : Word W,(destination A cap b).eval Fin.elim0 mem (fun _=>a)=(bankBase A cap S b:Word W))
    (space : bankBase A cap S b+bankSize S (numeric mem) b<2^W)
    (children : childCount S (numeric mem)≤cap) (capFit : cap<2^W) (wide : 11<2^W)
    (slots : BankCells A cap S mem b) :
    Protected (fieldProgram A cap W b) mem (bankBase A cap S b) (bankSize S (numeric mem) b) ∧
    ∀ i : Fin (rowCount (childCount S (numeric mem)) b), ∀ j : Fin b.width,
      (formula cap b).Fits W (fun _=>0) (numeric mem) (regs (args A) (b.width*i.val+j.val)) := by
  have checked:=bank_checked A cap S mem b header space children capFit wide slots
  constructor
  · intro p hp hhi x hx
    let dest:=bankBase A cap S b
    let key:=p.val-dest
    have positive : 0<b.width := by cases b <;> decide
    have range : key<b.width*rowCount (childCount S (numeric mem)) b := by
      change p.val<dest+b.width*rowCount (childCount S (numeric mem)) b at hhi
      change dest≤p.val at hp
      dsimp [key];omega
    let i : Fin (rowCount (childCount S (numeric mem)) b) :=
      ⟨key/b.width,(Nat.div_lt_iff_lt_mul positive).mpr (by simpa [Nat.mul_comm] using range)⟩
    let j : Fin b.width := ⟨key%b.width,Nat.mod_lt _ positive⟩
    have pieces : b.width*i.val+j.val=key := Nat.div_add_mod key b.width
    let operand : Fin 13 → Term W 0 1 := fun z=>
      if z=0 then l (args A) else if z=5 then cut (.result 0) (destination A cap b) else l 0
    change x∈((HeaderScan.closed (formula cap b)).instantiate operand).reads Fin.elim0 mem (fun _=>p) at hx
    rw [Term.reads_instantiate,List.mem_append] at hx
    rcases hx with inputs|body
    · obtain ⟨xs,found,get⟩:=List.mem_flatten.mp inputs
      obtain ⟨z,rfl⟩:=List.mem_ofFn.mp (List.mem_reverse.mp found)
      by_cases first : z=0
      · simp [operand,first,l] at get
      by_cases five : z=5
      · have dst : x∈(destination A cap b).reads Fin.elim0 mem (fun _=>p) := by
          have pure : (Term.result (0 : Fin 1) : Term W 0 1).reads Fin.elim0 mem (fun _=>p)=[] := rfl
          simpa [operand,first,five,cut,l,pure] using get
        exact destination_outside A cap S mem b slots p x dst
      · simp [operand,first,five,l] at get
    · have valid : dest<2^W := by dsimp [dest];omega
      have leq : ¬p<(dest:Word W) := by
        change ¬p.val<(dest:Word W).val
        rw [Fin.val_cast_of_lt valid]
        exact Nat.not_lt.mpr hp
      have addrEq : ((dest+key:ℕ):Word W)=p := by
        rw [show dest+key=p.val from Nat.add_sub_of_le hp]
        exact Fin.cast_val_eq_self p
      have diff : p-(dest:Word W)=(key:Word W) := by
        rw [←addrEq,Nat.cast_add];ring
      have eq : (fun z=> (operand z).eval Fin.elim0 mem (fun _=>p))=
          (fun z=>(regs (args A) (b.width*i.val+j.val) z : Word W)) := by
        funext z
        rw [pieces]
        dsimp only [operand]
        by_cases zero : z = 0
        · simp only [ite_eq_left zero, regs, l, Term.eval_literal]
        by_cases five : z = 5
        · have cursor : (Term.result 0 : Term W 0 1).eval Fin.elim0 mem (fun _ => p) = p := rfl
          have atBase : (destination A cap b).eval Fin.elim0 mem (fun _ => p) = (dest : Word W) :=
            atDest p
          simpa only [ite_eq_right zero, ite_eq_left five, regs, cut, Term.eval_select, Term.eval_binary,
            cursor, atBase, Comparison.test, BinaryOp.eval, decide_eq_true_eq, ite_eq_right leq] using diff
        · simp only [ite_eq_right zero, ite_eq_right five, regs, l, Term.eval_literal]
      rw [eq] at body
      exact (checked i j).reads x body
  · exact fun i j=>(checked i j).fits


end
end ThreeFlat.RAM.HistoryStageBounds

end OAI
