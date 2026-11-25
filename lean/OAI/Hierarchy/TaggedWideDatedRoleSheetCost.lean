import OAI.Hierarchy.TaggedWideDatedEmitters

namespace OAI
/-! # Work and contiguous space of each immutable dated metadata replay -/
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets
open ProtocolRAM RoleProgram
variable (n : ℕ) (chart : Chart) (sock : Bool→Socket) (table : Bank) (size number : Expr)
local notation "sz" => DatedRows.each n size size
local notation "idWord" => DatedRows.each n number number
local notation "self" => DatedRows.split n sock false
local notation "peer" => DatedRows.split n sock true

structure InputWork (B : ℕ) : Prop where
  size : (sz).work≤B
  id : (idWord).work≤B
  atSite : (socketSite chart self).work≤B
  code : (socketCode chart self).work≤B
  otherSite : (socketSite chart peer).work≤B

variable {B : ℕ} (small : InputWork n chart sock size number B)
include small

theorem word_work (f : Fin 3) : (word n chart sock size number f).work≤2*B+3 := by
  have a:=small.size;have b:=small.id;have c:=small.otherSite
  unfold word
  cases role f <;> simp only [RoleField.expr,Expr.work] <;> omega

theorem dest_work (start L : ℕ) (f : Fin 3) :
    (dest n chart sock table size number start L f).work≤4*B+14 := by
  have a:=word_work n chart sock size number small f
  have b:=small.atSite;have d:=small.code
  simp only [dest,RoleWidths.destination,RoleWidths.offset,Expr.work];omega

theorem leaf_work (start L : ℕ) (f : Fin 3) : leafWork n chart sock table size number start L f≤
    15+6*L+(n+n)*(12*B+52) := by
  have a:=word_work n chart sock size number small f
  have b:=dest_work n chart sock table size number small start L f
  let x:=(dest n chart sock table size number start L f).work
  let y:=(word n chart sock size number f).work
  change (4+6*L)+((4+(n+n)*(2*x+4))+(4+(n+n)*(2*y+4))+(3+10*(n+n)))≤_
  have c : (2*x+2*y+18)≤12*B+52 := by dsimp [x,y];omega
  calc _ = 15+6*L+(n+n)*(2*x+2*y+18) := by ring
       _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ c) _

theorem work_bound (start L : ℕ) : work n chart sock table size number start L≤3*(15+6*L+(n+n)*(12*B+52)) := by
  have a:=leaf_work n chart sock table size number small start L 0
  have b:=leaf_work n chart sock table size number small start L 1
  have c:=leaf_work n chart sock table size number small start L 2
  change leafWork n chart sock table size number start L 0 +
    (leafWork n chart sock table size number start L 1 + leafWork n chart sock table size number start L 2) ≤ _
  omega

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRoleSheets

end OAI
