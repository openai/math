import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # The padded core and acquired rows of the actual seven-field geometry -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing
variable {W : ℕ}

/-- All inputs are indexed by the original core catalogue ordinal. Live CT data
supplies positive-core endpoints, already decoded to global physical site ordinals. -/
structure CoreSource where
  group : Expr
  left : Expr
  right : Expr
  lengthCode : Expr
  menu : Expr

/-- All inputs are indexed by the fixed chronological acquisition candidate. Its
length is one independently of its true selection flag, and its birth width is zero. -/
structure BoughtSource where
  group : Expr
  left : Expr
  right : Expr
  flag : Expr
  menu : Expr

def CoreSource.fromBanks (group left right length menu : Bank) : CoreSource :=
  ⟨.lookup group .row,.lookup left .row,.lookup right .row,.lookup length .row,.lookup menu .row⟩

def BoughtSource.fromBanks (group left right flag menu : Bank) : BoughtSource :=
  ⟨.lookup group .row,.lookup left .row,.lookup right .row,.lookup flag .row,.lookup menu .row⟩

/-- Only the source addresses are public here. The loaded values come from the
real input/permutation-dependent CT records or the archived purchase decision. -/
def indirect (history address : Bank) := Expr.lookup history (.lookup address .row)

def CoreSource.fromDirectory (history group left right length menu : Bank) : CoreSource :=
  ⟨indirect history group,indirect history left,indirect history right,indirect history length,indirect history menu⟩

def BoughtSource.fromDirectory (history group left right flag menu : Bank) : BoughtSource :=
  ⟨indirect history group,indirect history left,indirect history right,indirect history flag,indirect history menu⟩

structure Board where
  coreRows : ℕ
  boughtRows : ℕ
  idBase : ℕ
  core : CoreSource
  bought : BoughtSource

def Board.rows (b : Board) := b.coreRows+b.boughtRows

def Board.select (b : Board) (old new : Expr) :=
  Expr.branch .lt .row (.lit b.coreRows) old (new.atRow (.op .sub .row (.lit b.coreRows)))

def low (left right : Expr) := Expr.branch .lt left right left right
def high (left right : Expr) := Expr.branch .lt left right right left

def Board.geometry (b : Board) : Fin 7→Expr :=
  let l := b.select b.core.left b.bought.left
  let r := b.select b.core.right b.bought.right
  ![b.select b.core.group b.bought.group,low l r,high l r,.op .add (.lit b.idBase) .row,.lit 0,
    b.select b.core.lengthCode (.lit 1),
    b.select b.core.menu (.branch .eq b.bought.flag (.lit 0) (.lit 0) b.bought.menu)]

theorem low_eval (l r : Expr) (m : Memory W) (i : Word W) :
    ((low l r).eval m i).val=min (l.eval m i).val (r.eval m i).val := by
  by_cases h : (l.eval m i).val<(r.eval m i).val
  · simp [low,Expr.eval,Comparison.test,Fin.lt_def,h,min_eq_left h.le]
  · simp [low,Expr.eval,Comparison.test,Fin.lt_def,h,min_eq_right (Nat.le_of_not_gt h)]

theorem high_eval (l r : Expr) (m : Memory W) (i : Word W) :
    ((high l r).eval m i).val=max (l.eval m i).val (r.eval m i).val := by
  by_cases h : (l.eval m i).val<(r.eval m i).val
  · simp [high,Expr.eval,Comparison.test,Fin.lt_def,h,max_eq_right h.le]
  · simp [high,Expr.eval,Comparison.test,Fin.lt_def,h,max_eq_left (Nat.le_of_not_gt h)]

theorem Board.select_core (b : Board) (m : Memory W) (old new : Expr) (i : Fin b.coreRows)
    (room : b.rows<2^W) : (b.select old new).eval m (i.val:Word W)=old.eval m (i.val:Word W) := by
  have h1 : i.val<2^W := by have := i.isLt;unfold rows at room;omega
  have h2 : b.coreRows<2^W := by unfold rows at room;omega
  simp [select,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt h1,Fin.val_cast_of_lt h2,i.isLt]

theorem Board.select_bought (b : Board) (m : Memory W) (old new : Expr) (i : Fin b.boughtRows)
    (room : b.rows<2^W) :
    (b.select old new).eval m ((b.coreRows+i.val:ℕ):Word W)=new.eval m (i.val:Word W) := by
  have h1 : b.coreRows+i.val<2^W := by have := i.isLt;unfold rows at room;omega
  have h2 : b.coreRows<2^W := by unfold rows at room;omega
  have diff : ((b.coreRows+i.val:ℕ):Word W)-(b.coreRows:Word W)=(i.val:Word W) := by rw [Nat.cast_add];abel
  simp only [select,Expr.eval,Comparison.test,Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt h1,Fin.val_cast_of_lt h2,
    show ¬b.coreRows+i.val<b.coreRows by omega,ite_false,eval_atRow,RowOp.opcode,BinaryOp.eval,diff]

/-- Measured underlying endpoints in their original orientation; the observed rows
are sorted only at the very end for thermal pruning. -/
structure View where
  group : ℕ
  left : ℕ
  right : ℕ
  lengthCode : ℕ
  menu : ℕ

def CoreSource.view (s : CoreSource) (m : Memory W) (i : Word W) : View :=
  ⟨(s.group.eval m i).val,(s.left.eval m i).val,(s.right.eval m i).val,(s.lengthCode.eval m i).val,(s.menu.eval m i).val⟩

def BoughtSource.view (s : BoughtSource) (m : Memory W) (i : Word W) : View :=
  ⟨(s.group.eval m i).val,(s.left.eval m i).val,(s.right.eval m i).val,1,
    if s.flag.eval m i=0 then 0 else (s.menu.eval m i).val⟩

def View.fields (v : View) (id : ℕ) : Fin 7→ℕ :=
  ![v.group,min v.left v.right,max v.left v.right,id,0,v.lengthCode,v.menu]

def Board.coreIndex (b : Board) (i : Fin b.coreRows) : Fin b.rows := ⟨i.val,by unfold rows;omega⟩
def Board.boughtIndex (b : Board) (i : Fin b.boughtRows) : Fin b.rows := ⟨b.coreRows+i.val,by unfold rows;omega⟩

theorem Board.core_read (b : Board) (m : Memory W) (i : Fin b.coreRows) (room : b.idBase+b.rows<2^W) (k : Fin 7) :
    ((b.geometry k).eval m ((b.coreIndex i).val:Word W)).val=(b.core.view m (i.val:Word W)).fields (b.idBase+i.val) k := by
  have sz : b.rows<2^W := by omega
  have fits : b.idBase+i.val<2^W := by have := (b.coreIndex i).isLt;change i.val<b.rows at this;omega
  let L := b.select b.core.left b.bought.left
  let R := b.select b.core.right b.bought.right
  let row : Word W := i.val
  have left := congrArg Fin.val (b.select_core m b.core.left b.bought.left i sz)
  have right := congrArg Fin.val (b.select_core m b.core.right b.bought.right i sz)
  fin_cases k
  · exact congrArg Fin.val (b.select_core m _ _ i sz)
  · exact (low_eval L R m row).trans (congrArg₂ min left right)
  · exact (high_eval L R m row).trans (congrArg₂ max left right)
  · change ((b.idBase:Word W)+(i.val:Word W)).val=b.idBase+i.val
    rw [←Nat.cast_add,Fin.val_cast_of_lt fits]
  · rfl
  · exact congrArg Fin.val (b.select_core m _ _ i sz)
  · exact congrArg Fin.val (b.select_core m _ _ i sz)

theorem Board.bought_read (b : Board) (m : Memory W) (i : Fin b.boughtRows) (room : b.idBase+b.rows<2^W)
    (wide : 1<2^W) (k : Fin 7) :
    ((b.geometry k).eval m ((b.boughtIndex i).val:Word W)).val=
      (b.bought.view m (i.val:Word W)).fields (b.idBase+(b.coreRows+i.val)) k := by
  have sz : b.rows<2^W := by omega
  have fits : b.idBase+(b.coreRows+i.val)<2^W := by have := (b.boughtIndex i).isLt;change b.coreRows+i.val<b.rows at this;omega
  let L := b.select b.core.left b.bought.left
  let R := b.select b.core.right b.bought.right
  let row : Word W := ((b.coreRows+i.val : ℕ):Word W)
  have left := congrArg Fin.val (b.select_bought m b.core.left b.bought.left i sz)
  have right := congrArg Fin.val (b.select_bought m b.core.right b.bought.right i sz)
  fin_cases k
  · exact congrArg Fin.val (b.select_bought m _ _ i sz)
  · exact (low_eval L R m row).trans (congrArg₂ min left right)
  · exact (high_eval L R m row).trans (congrArg₂ max left right)
  · change ((b.idBase:Word W)+((b.coreRows+i.val:ℕ):Word W)).val=b.idBase+(b.coreRows+i.val)
    rw [←Nat.cast_add,Fin.val_cast_of_lt fits]
  · rfl
  · exact (congrArg Fin.val (b.select_bought m b.core.lengthCode (.lit 1) i sz)).trans (Fin.val_cast_of_lt wide)
  · let menu := Expr.branch .eq b.bought.flag (.lit 0) (.lit 0) b.bought.menu
    apply (congrArg Fin.val (b.select_bought m b.core.menu menu i sz)).trans
    change (menu.eval m (i.val:Word W)).val=if b.bought.flag.eval m (i.val:Word W)=0 then 0 else _
    by_cases off : b.bought.flag.eval m (i.val:Word W)=0 <;> simp [menu,Expr.eval,Comparison.test,beq_iff_eq,off]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
