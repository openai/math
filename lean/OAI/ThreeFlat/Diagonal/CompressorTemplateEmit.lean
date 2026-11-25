import OAI.ThreeFlat.Diagonal.CompressorUniformRows
import OAI.ThreeFlat.Diagonal.CompressorOpsMap

namespace OAI
/-! # Linking width-independent templates to the word-level coloring and ranking proofs -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement
open scoped Fin.NatCast
variable {w : ℕ} (cell : Word w)
local notation "e" => emit cell

theorem emitOps : OpMap o (terms w 1 1) (emit cell) := ⟨fun _ => rfl,fun _ _ _ => rfl,fun _ => rfl,fun _ _ _ _ => rfl⟩
@[simp] theorem emit_lit (i : ℕ) : e (.lit i) = .literal (i : Word w) := rfl
@[simp] theorem emit_op (op : BinaryOp) (a b : F) : e (.op op a b) = .binary op (e a) (e b) := rfl
@[simp] theorem emit_select (c : Comparison) (a b u v : F) :
    e (.select c a b u v) = .select c (e a) (e b) (e u) (e v) := rfl
@[simp] theorem emit_load (u : F) : e (.load u)=.load (e u) := rfl
@[simp] theorem emit_reg (i : Fin 1) : e (.reg i)=.result i := rfl
@[simp] theorem emit_ptr : e ptr=.literal cell := by simp [emit,bindCurrent,Formula.compile]
@[simp] theorem emit_header (i : ℕ) : e (f i) = (termField cell) i := by
  change _ = Term.load (.binary .add (.load (.literal cell)) (.literal (i:Word w)))
  simp [f,atField,Demand.formulaOps]
@[simp] theorem emit_oldRead (d : ℕ) (col v : F) (i : Fin d) :
    e (oldRead d col v i) = readSlot (e col) (e v) d i := rfl

theorem emit_member (a : F) (xs : List F) :
    e (member a xs)=Rank.contains (e a) (xs.map e) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Nat.cast_one,member,List.foldr_cons,emit_select,emit_lit,List.map_cons,Rank.contains] at ih ⊢
    rw [ih]

private theorem emit_memberLit (a : ℕ) (xs : List F) :
    e (member (.lit a) xs)=Native.member (a:Word w) (xs.map e) := by
  rw [emit_member,emit_lit]
  generalize xs.map e=ys
  induction ys <;> simp [Native.member,Rank.contains, *]

theorem emit_free (xs : List F) (n : ℕ) :
    e (firstFree xs n)=Native.firstFree (xs.map e) 0 (List.ofFn fun i : Fin n => (i.val:Word w)) := by
  unfold firstFree
  rw [show (List.ofFn fun i : Fin n => (i.val:Word w))=(List.finRange n).map (fun i => (i.val:Word w)) by
    simp [←List.ofFn_id,List.map_ofFn]]
  generalize List.finRange n = ys
  induction ys with
  | nil => rfl
  | cons a ys ih => simp only [Nat.cast_one,List.foldr_cons,emit_select,emit_memberLit,emit_lit,List.map_cons,Native.firstFree,ih]

theorem emit_below (k : F) (xs : List F) : e (below k xs)=Rank.rank (e k) (xs.map e) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [Nat.cast_zero,Nat.cast_one,below,emit_op,emit_select,emit_lit,emit_member,List.map_cons,Rank.rank,Rank.contribution,ih]

private theorem emit_pickAux (k : F) (ids ys : List F) :
    e (ys.foldr (fun a tail =>
      let ok := Formula.select .eq a (.lit 0) (.lit 0) (.select .eq (below a ids) k (.lit 1) (.lit 0))
      .select .eq ok (.lit 1) a tail) (.lit 0)) =
      Rank.pick (e k) (ids.map e) (ys.map e) := by
  induction ys with
  | nil => rfl
  | cons a ys ih =>
    simp only [Nat.cast_zero,Nat.cast_one,List.foldr_cons,emit_select,emit_lit,emit_below,List.map_cons,Rank.pick,ih]

theorem emit_pick (k : F) (ids : List F) : e (pick k ids)=Rank.pick (e k) (ids.map e) (ids.map e) :=
  emit_pickAux cell k ids ids

theorem emit_color (d : ℕ) : e (color d)=ShrinkStage.color cell d := by
  simp [color,ShrinkStage.color,emit_free,colorRow,colorBans,readRow,oldColumns,column,termOps,
    Placement.row,Demand.formulaOps,oldRead,readSlot,slotAddr,termField,atField,terms,g,f,o,
    ←List.ofFn_id,List.map_ofFn,Function.comp_def]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
