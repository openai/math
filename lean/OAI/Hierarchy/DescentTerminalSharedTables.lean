import OAI.Hierarchy.DescentTerminalRowStorage
import OAI.Hierarchy.DescentTerminalChronologicalBooks
import OAI.Hierarchy.DescentTerminalPositionAlphabet
import OAI.Hierarchy.DescentTerminalPrintedFields

namespace OAI
/-! # Literal decoder and scalar-key widths on the common terminal page -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalControlBits DescentTerminalPrintedFields DescentTerminalSiteShelves DescentTerminalChronologicalBooks
noncomputable section
variable (q t H N A p V W B h:ℕ)
local notation "s" => span q t H N A p
local notation "tag" => Nat.clog 2 (t+1)
local notation "r" => rowBits q tag H N A p V
local notation "num" => DescentTerminalScalarHeader.range q t H N A p V

theorem shared_tables (roles:0<t) (page:V*s≤B) (small:32*B≤h) (width:32*W≤h)
    (packed:16*(q*p)≤h) (large:10≤h) :
    DescentTerminalSiteShelves.alphabet V W B≤2^(h/2) ∧ (capacity q t H N A p V).total≤2^(h/2) ∧
      num+1≤2^(h/2) ∧ Keys q t H N A p V p≤2^(h/2) := by
  have sg:0 < s:=by rw [size];omega
  have count:V≤B:=(Nat.le_mul_of_pos_right V sg).trans page
  have log₁ (x:ℕ):Nat.clog 2 (x+1)≤x:=(Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self
  have log₂:Nat.clog 2 B≤B:=Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have vlen:=log₁ V;have wlen:=log₁ W
  have rlen:=row_storage q t H N A p V roles
  have rsize:r+1≤h/2:=by omega
  have fits:r+q*p≤h/2:=by omega
  have tags:t≤2^tag:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have rank:=DescentTerminalScalarHeader.header_room q t H N A p V tag tags
  have extra:num+1≤2^(r+1):=by rw [pow_succ];have:=Nat.two_pow_pos r;omega
  exact ⟨alphabet_bound h (by omega),
    (table_room q t H N A p V tag tags).trans (Nat.pow_le_pow_right (by decide) (by omega)),
    extra.trans (Nat.pow_le_pow_right (by decide) rsize),
    DescentTerminalChronologicalBooks.alphabet q t H N A p V p tag h tags fits⟩

end
end Hierarchy.DescentTerminalVertexFields

end OAI
