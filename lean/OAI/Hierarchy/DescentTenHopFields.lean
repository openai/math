import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Reading a fixed sequence of old neighbor slots from the actual shared roster -/
namespace Hierarchy.DescentTenHopRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentHaloWalkRAM DescentIssuedTerminalId
open scoped Fin.CommRing

variable {H D w : ℕ}

def move (bank : Bank) (H D : ℕ) (x : Expr) (j : Fin (D+1)) : Expr :=
  if j.val<D then .branch .eq x (.lit H) (.lit H)
    (.lookup bank (.op .add (times x D) (.lit j.val))) else x

def walkExpr (bank : Bank) (H D : ℕ) (ds : List (Fin (D+1))) (x : Expr) :=
  ds.foldl (move bank H D) x

theorem move_read (bank : Bank) (near : Fin H→Fin D→Option (Fin H)) (m : Memory w)
    (size : H*D≤bank.size) (wide : bank.size<2^w) (sentinel : H<2^w)
    (data : ∀v j,m (bank.base+v.val*D+j.val)=(number (near v j):Word w))
    (row : Word w) (x : Expr) (u : Option (Fin H)) (hx : x.eval m row=(number u:Word w)) (j : Fin (D+1)) :
    (move bank H D x j).eval m row=(number (step near u j):Word w) := by
  by_cases hit : j.val<D
  · cases u with
    | none=>simp [move,hit,step,Expr.eval,DescriptorExpr.Comparison.test,hx,number]
    | some v=>
      have diff : (v.val:Word w)≠(H:Word w) := by
        intro eqn
        have h:=congrArg Fin.val eqn
        rw [Fin.val_cast_of_lt (v.isLt.trans sentinel),Fin.val_cast_of_lt sentinel] at h
        exact v.isLt.ne h
      have p : v.val*D+j.val<H*D :=
        (Nat.add_lt_add_left hit _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
      have ind : (Expr.op .add (times x D) (.lit j.val)).eval m row=((v.val*D+j.val:ℕ):Word w) := by
        change (times x D).eval m row+(j.val:Word w)=_
        rw [times_at,hx];change (D:Word w)*(v.val:Word w)+(j.val:Word w)=_
        push_cast;ring
      have read := (lookup_nat bank m row _ _ ind (p.trans_le size) wide).trans
        (show m (bank.base+(v.val*D+j.val))=(number (near v ⟨j.val,hit⟩):Word w) by
          simpa only [Nat.add_assoc] using data v (⟨j.val,hit⟩:Fin D))
      change x.eval m row=(v.val:Word w) at hx
      simpa only [move,ite_eq_left hit,Expr.eval,DescriptorExpr.Comparison.test,hx,beq_iff_eq,ite_eq_right diff,
        step,dite_eq_left hit,Option.bind] using read
  · simpa only [move,ite_eq_right hit,step,dite_eq_right hit] using hx

theorem walk_read (bank : Bank) (near : Fin H→Fin D→Option (Fin H)) (m : Memory w)
    (size : H*D≤bank.size) (wide : bank.size<2^w) (sentinel : H<2^w)
    (data : ∀v j,m (bank.base+v.val*D+j.val)=(number (near v j):Word w))
    (ds : List (Fin (D+1))) (row : Word w) (x : Expr) (u : Option (Fin H))
    (hx : x.eval m row=(number u:Word w)) :
    (walkExpr bank H D ds x).eval m row=(number (ds.foldl (step near) u):Word w) := by
  induction ds generalizing x u with
  | nil=>exact hx
  | cons j js ih=>exact ih _ _ (move_read bank near m size wide sentinel data row x u hx j)

theorem walk_fits {bank : Bank} {out : ℕ} (fits : bank.Fits w out)
    (ds : List (Fin (D+1))) (x : Expr) (ok : x.Fits w out) : (walkExpr bank H D ds x).Fits w out := by
  induction ds generalizing x with
  | nil=>exact ok
  | cons j js ih=>
    apply ih
    unfold move
    split
    · exact ⟨ok,trivial,trivial,fits,times_fits ok D,trivial⟩
    · exact ok

theorem walk_work (bank : Bank) (H D : ℕ) (ds : List (Fin (D+1))) (x : Expr) :
    (walkExpr bank H D ds x).work+12 ≤ (x.work+12)*(D+12)^ds.length := by
  induction ds generalizing x with
  | nil=>simp [walkExpr]
  | cons j js ih=>
    have add : (move bank H D x j).work+12≤(x.work+12)*(D+12) := by
      unfold move
      split
      · simp only [Expr.work,times_work];nlinarith
      · nlinarith
    exact (ih (move bank H D x j)).trans (by
      rw [List.length_cons,pow_succ]
      simpa only [Nat.mul_assoc,Nat.mul_comm (D+12) ((D+12)^js.length)] using
        Nat.mul_le_mul_right ((D+12)^js.length) add)

end Hierarchy.DescentTenHopRAM

end OAI
