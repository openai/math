import OAI.Hierarchy.TraceReceiverGridWindow
import OAI.Hierarchy.TraceReceiverTaskReads
import OAI.Hierarchy.TraceReceiverCommands

namespace OAI
/-! # Genuine reads of the seven-word receiver command writer -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Commands
open ThreeFlat RAM Diagonal HistoryCommandTable
open Computability.VPVNP.BurstRAM PrivateRAM TraceReceiverTasks
open scoped Fin.CommRing BigOperators

variable {w u n : ℕ}

/-- The physical divide-by-seven returns the ordinal of the active command
even when the caller provides its address as a machine word. -/
private theorem task_at {W commands tasks count : ℕ} (wide : 7<2^W) (a : Word W)
    (low : commands≤a.val) (high : a.val<commands+7*count) :
    ∃ i : Fin count,address (tasks:Word W) (commands:Word W) a=((tasks+5*i.val:ℕ):Word W) := by
  let i : Fin count:=⟨(a.val-commands)/7,by omega⟩
  have commandVal : (commands:Word W).val=commands := Fin.val_cast_of_lt (low.trans_lt a.isLt)
  have wordLow : (commands:Word W) ≤ a := by
    change (commands:Word W).val ≤ a.val
    rwa [commandVal]
  have delta : (a-(commands:Word W)).val=a.val-commands := by
    rw [Fin.sub_val_of_le wordLow,commandVal]
  have seven : (7:Word W).val=7 := Fin.val_cast_of_lt wide
  have quotient : BinaryOp.eval .div (a-(commands:Word W)) 7=(i.val:Word W) := by
    change Fin.ofNat _ (_/_) = _
    rw [delta,seven]; rfl
  refine ⟨i,?_⟩
  simp only [address,quotient,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

/-- Each of the command writer's five task fields and four parent/child
fields lies below its output stream. Only the two actual node pointers are
used to establish safety. -/
theorem separate_grid (large : 7≤w) (age : u^10≤5*w) (jobs : 5*n≤GridReceiverBanks.gap w)
    (ranged : Memory (64*w)) (node : Fin n→ℕ)
    (nodes : ∀ i,node i+4≤TickWorkspace.base u 14)
    (fields : ∀ i : Fin n,let t:=readTask ranged (((GridReceiverBanks.tasks w).tasks+5*i.val:ℕ):Word (64*w))
      t.child=(node i:Word (64*w)) ∧ t.parent=((GridReceiverBanks.tasks w).parent:Word (64*w))) :
    Separate (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.commands w) n ranged := by
  let B:=GridReceiverBanks.base w
  let G:=GridReceiverBanks.gap w
  let cmd:=GridReceiverBanks.commands w
  let task:=(GridReceiverBanks.tasks w).tasks
  have cmdAt : cmd=B+9*G := rfl
  have taskAt : task=B+G := rfl
  obtain ⟨old,roof,gap⟩:=Gather.grid_window large age
  have room:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have word : 7<2^(64*w) := by omega
  constructor
  · intro a low high j
    obtain ⟨i,index⟩:=task_at (tasks:=task) word a low high
    have root:=i.isLt
    have col:=j.isLt
    change (address (task:Word (64*w)) (cmd:Word (64*w)) a+(j.val:Word (64*w))).val<cmd ∨ _
    left
    rw [index,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    omega
  · intro a low high j
    obtain ⟨i,index⟩:=task_at (tasks:=task) word a low high
    have final:=nodes i
    have col:=j.isLt
    change ((readTask ranged (address (task:Word (64*w)) (cmd:Word (64*w)) a)).child+(j.val:Word (64*w))).val<cmd ∨ _
    left
    rw [index,(fields i).1,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    omega
  · intro a low high j
    obtain ⟨i,index⟩:=task_at (tasks:=task) word a low high
    have col:=j.isLt
    have parentAt : (GridReceiverBanks.tasks w).parent=B+16 := rfl
    change ((readTask ranged (address (task:Word (64*w)) (cmd:Word (64*w)) a)).parent+(j.val:Word (64*w))).val<cmd ∨ _
    left
    rw [index,(fields i).2,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    omega

/-- Every task word produced by the amounts and prefix passes survives both
the intervening map loops and the final seven-word range header. -/
theorem separate_after_maps (large : 7≤w) (age : u^10≤5*w) (jobs : 5*n≤GridReceiverBanks.gap w)
    (count cap : ℕ) (width : Fin 3→ℕ) (mounted mapped : Memory (64*w))
    (room : BeforeBounds (GridReceiverBanks.tasks w) count cap width n (64*w))
    (apart : ColumnSeparation (GridReceiverBanks.tasks w) width n)
    (cache : ∀ j (i : Fin n), let D:=GridReceiverBanks.tasks w
      (amountAddress D.selected D.first D.results j mounted (i.val:Word (64*w))).val<D.current)
    (small : ∀ j,∑ i : Fin n,cacheAmount (GridReceiverBanks.tasks w) mounted j i.val≤cap)
    (nodes : ∀ i : Fin n,let D:=GridReceiverBanks.tasks w
      D.results+8*((mounted D.first).val+(mounted (D.selected+i.val)).val)+4≤TickWorkspace.base u 14)
    (held : ∀ a,(GridReceiverBanks.tasks w).tasks≤a→a<(GridReceiverBanks.tasks w).maps→
      mapped a=beforeImage (GridReceiverBanks.tasks w) count cap width n mounted a) :
    Separate (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.commands w) n
      (rangeImage (GridReceiverBanks.tasks w).current count (GridReceiverBanks.commands w) 0 7 mapped) := by
  let D:=GridReceiverBanks.tasks w
  let B:=GridReceiverBanks.base w
  let G:=GridReceiverBanks.gap w
  let cmd:=GridReceiverBanks.commands w
  let prepared:=beforeImage D count cap width n mounted
  let ranged:=rangeImage D.current count cmd 0 7 mapped
  let source (i : Fin n):=D.results+8*((mounted D.first).val+(mounted (D.selected+i.val)).val)
  obtain ⟨_,roof,gap⟩:=Gather.grid_window large age
  have origin : D.tasks=B+G := rfl
  have baseAt : D.current=B := rfl
  have finish : D.maps=B+2*G := rfl
  apply separate_grid large age jobs ranged source nodes
  intro i
  let base:=D.tasks+5*i.val
  have root:=i.isLt
  have same (k : Fin 5) : ranged (((base:Word (64*w))+(k.val:Word (64*w))).val)=
      prepared (((base:Word (64*w))+(k.val:Word (64*w))).val) := by
    have col:=k.isLt
    have fits : base+k.val<2^(64*w) := by dsimp only [base];omega
    rw [←Nat.cast_add,Fin.val_cast_of_lt fits]
    have src : D.tasks≤base+k.val := by dsimp only [base];omega
    have endTask : base+k.val<D.maps := by dsimp only [base];omega
    have clear : ¬(D.current≤base+k.val ∧ base+k.val<D.current+7) := by omega
    exact (show ranged (base+k.val)=mapped (base+k.val) by
      simp only [ranged,rangeImage,fillSegment,ite_eq_right clear]).trans (held _ src endTask)
  have written:=prepared_task D count cap width n room apart mounted cache small i
  have c : (readTask prepared (base:Word (64*w))).child=
      (D.results:Word (64*w))+8*(mounted D.first+mounted (D.selected+i.val)) := congrArg Task.child written
  have p : (readTask prepared (base:Word (64*w))).parent=(D.parent:Word (64*w)) := congrArg Task.parent written
  have child : (readTask ranged (base:Word (64*w))).child=(source i:Word (64*w)) := by
    have pointer : (readTask ranged (base:Word (64*w))).child=(readTask prepared (base:Word (64*w))).child := same 0
    rw [pointer,c]
    simp only [source,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Fin.cast_val_eq_self]
  have parent : (readTask ranged (base:Word (64*w))).parent=(D.parent:Word (64*w)) :=
    (show (readTask ranged (base:Word (64*w))).parent=(readTask prepared (base:Word (64*w))).parent from same 1).trans p
  exact ⟨child,parent⟩

end Hierarchy.TraceFactorReceiver.Commands

end
end OAI
