import OAI.Hierarchy.DescentTerminalSiteControlBanks

namespace OAI
/-! # One bill for the primitive header controls, including all public tables -/
namespace Hierarchy.DescentTerminalControlProgram
open DescentTerminalLocalPortBook DescentDyadicSpan DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
noncomputable section

theorem fees (x : Plan) (w : ℕ) (values : ℕ→ℕ) (parts : Book.Parts) :
    let e:=Book.expression parts
    x.time e+7*names (x.program w values e) ≤
      4096*(1+x.sites+x.codeWords+x.shape.limit) := by
  intro e
  have work : (x.lookup e).work=82 := rfl
  have row : Expr.row.work=2 := rfl
  have bound := span_le x.shape.limit
  have sz : x.shape.size=1+4*span x.shape.limit := rfl
  simp only [Plan.program,names_seq,names_scan,names_mount,Plan.time,work,row]
  omega

theorem width_fee (x : Plan) (w h T rate money : ℕ) (values : ℕ→ℕ) (parts : Book.Parts)
    (smallBook : x.codeWords≤2^(h/2)) (rates : x.shape.limit≤2^(h/2))
    (sourceRows : x.sites*w*T ≤ rate*money) (static : 2^(h/2)*w*T ≤ rate*money) :
    (x.time (Book.expression parts)+7*names (x.program w values (Book.expression parts)))*w*T
      ≤16384*rate*money := by
  have floor : 1≤2^(h/2) := Nat.two_pow_pos _
  have c:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right w smallBook)
  have r:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right w rates)
  have one:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right w floor)
  have scaled:=Nat.mul_le_mul_right T (Nat.mul_le_mul_right w (fees x w values parts))
  calc
    _ ≤4096*(1+x.sites+x.codeWords+x.shape.limit)*w*T := scaled
    _ = 4096*(1*w*T+x.sites*w*T+x.codeWords*w*T+x.shape.limit*w*T) := by ring
    _ ≤ 4096*(rate*money+rate*money+rate*money+rate*money) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (one.trans static) sourceRows)
        (c.trans static)) (r.trans static))
    _ = _ := by ring

end
end Hierarchy.DescentTerminalControlProgram

end OAI
