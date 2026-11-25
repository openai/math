import OAI.Hierarchy.DescentTerminalPlacedLiteral
import OAI.Hierarchy.DescentTerminalVertexFields

namespace OAI
/-! # Scalar decoder and ordinal tables in the original fixed instruction image -/
namespace Hierarchy.DescentTerminalEmitter.Compact.ScalarLiterals
open DescentTerminalSiteShelves DescentTerminalVertexFields DescentTerminalPrintedFields
noncomputable section
set_option quotPrecheck false
variable (q t H N A p V W B pool:ℕ)
local notation "menu" => alphabet V W B
local notation "book" => (capacity q t H N A p V).total

def columns (other:Columns) : Columns := fun j=>
  if j=37 then .literal (2*pool) else if j=39 then .literal pool else
  if j=41 then .literal menu else if j=42 then .literal book else other j

variable (qp:0<q) (other:Columns) (value:Fin 43→ℕ→ℕ)
local notation "cols" => columns q t H N A p V W B pool other
/-- Each scalar table reads its public format. The prior columns retain their supplied
literal values; the attained columns have zero literal length. -/
def data : Literals cols := fun j u=>
  if j=37 then u.val/2 else if j=39 then u.val else
  if j=41 then if h:u.val< menu then entryBy (DescentTerminalVertexFields.decode
    (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p)) qp (⟨u.val,h⟩:Fin (alphabet V W B)) else 0
  else if j=42 then (headerTable q t H N A p V)[u.val]?.getD 0 else value j u.val

theorem priced {h : ℕ} (prior:∀j,need (other j)≤2^(h/2)+4*pool)
    (short:menu≤2^(h/2)) (small:book≤2^(h/2)) (j:Fin 43) :
    need (cols j)≤2^(h/2)+4*pool := by
  by_cases v:j=37
  · simp only [columns,ite_eq_left v,need];omega
  by_cases x:j=39
  · simp only [columns,ite_eq_right v,ite_eq_left x,need];omega
  by_cases y:j=41
  · simp only [columns,ite_eq_right v,ite_eq_right x,ite_eq_left y,need];omega
  by_cases k:j=42
  · simp only [columns,ite_eq_right v,ite_eq_right x,ite_eq_right y,ite_eq_left k,need];omega
  simpa [columns,v,x,y,k] using prior j

theorem half (u:Fin (size (cols 37))) :
    data q t H N A p V W B pool qp other value 37 u=u.val/2 := by simp [data]
theorem identity (u:Fin (size (cols 39))) :
    data q t H N A p V W B pool qp other value 39 u=u.val := by norm_num [data]
theorem decoder (u:Fin (size (cols 41))) (small:u.val< menu) :
    data q t H N A p V W B pool qp other value 41 u=entryBy (DescentTerminalVertexFields.decode
      (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p)) qp (⟨u.val,small⟩:Fin (alphabet V W B)) := by
  norm_num [data,small]
theorem header (u:Fin (size (cols 42))) (small:u.val<book) :
    data q t H N A p V W B pool qp other value 42 u=
      (headerTable q t H N A p V)[u.val]'(by simpa [headerTable] using small) := by
  have k:u.val<(headerTable q t H N A p V).length:=by simpa [headerTable] using small
  norm_num [data,List.getElem?_eq_getElem k]

end
end Hierarchy.DescentTerminalEmitter.Compact.ScalarLiterals

end OAI
