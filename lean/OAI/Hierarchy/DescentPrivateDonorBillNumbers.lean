import Mathlib

namespace OAI
/-! # A single age's packed donor installation, execution and hardware costs -/

namespace Hierarchy.DescentCompiler.TerminalScale

/-- Row count of the dyadic venue tape on which the actual match publisher runs. -/
def hostRows (homes : ℕ) := 2^(Nat.clog 2 homes)

theorem hostPad (homes : ℕ) : homes≤hostRows homes := Nat.le_pow_clog (by decide) _

theorem hostRows_double {homes : ℕ} (live : 0<homes) : hostRows homes≤2*homes := by
  by_cases one:homes=1
  · simp [one,hostRows]
  have wide : 1<homes := by omega
  have low:=Nat.pow_pred_clog_lt_self (by decide : 1<(2:ℕ)) wide
  have tall:=Nat.clog_pos (by decide : 1<(2:ℕ)) wide
  unfold hostRows
  generalize height:Nat.clog 2 homes=n at *
  cases n with
  | zero=>omega
  | succ n=>simp only [Nat.pred_succ] at low;rw [pow_succ];omega

theorem pad_bill {homes work unit : ℕ} (live : 0<homes) :
    hostRows homes*work*unit ≤ homes*work*(2*unit) := calc
  _ ≤ (2*homes)*work*unit :=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hostRows_double live))
  _ = _ :=by ring

/-- Roots, owner and rank geometry are charged to this same dyadic input page. -/
theorem donor_venue_bill {H groups radix h amount K work u v prior geom grade : ℕ}
    (live : 0<radix) (expr : work≤u)
    (old : prior≤H*h*(K*(1274+6*grade))+H*(groups*radix)*(K*(4*amount*(342+2*grade))))
    (gate : geom≤16384*K*((H*h+H*groups*amount)*(work+1)+H*h*v)) :
    let g:=16384*(u+1+v)
    prior+geom≤H*h*(K*(1274+6*(grade+g)))+H*(groups*radix)*(K*(4*amount*(342+2*(grade+g)))) := by
  let g:=16384*(u+1+v)
  have slots : H*groups≤H*(groups*radix) := by
    exact Nat.mul_le_mul_left H (Nat.le_mul_of_pos_right _ live)
  have path : geom≤H*h*(K*g)+H*(groups*radix)*(K*(amount*g)) := calc
    _ ≤ 16384*K*((H*h+H*groups*amount)*(u+1)+H*h*v) :=gate.trans (by gcongr)
    _ = H*h*(K*g)+H*groups*(K*(amount*(16384*(u+1)))) :=by dsimp [g];ring
    _ ≤ _ :=by gcongr; dsimp [g]; omega
  apply (Nat.add_le_add old path).trans
  dsimp [g]
  ring_nf
  omega

/-- The four addends are the six-field gather's clock, its controller, the packed
private meter's clock including the committed header, and its literal controller.
Both the installed tables and the width of the current grain are paid once per date. -/
theorem donor_row_bill {H groups amount h K W b X f radix gather text meter names : ℕ}
    (hosts : 0<H) (block : 0<radix) (word : W≤K*h) (grain : b≤H) (pages : X≤H)
    (rg : gather≤K*(8*h+(H*h+4*H*groups*amount)*(2*f+158)))
    (rt : text≤(322+4*f)*W)
    (rm : meter≤K*((131+4*b)*h+124*(H*h+4*H*groups*amount)+20*X*h)+11*W)
    (rn : names≤K*((398+8*b+30*X)*h+60*(H*h+4*H*groups*amount))) :
    gather+text+meter+names ≤ H*h*(K*(1274+6*f))+
      H*(groups*radix)*(K*(4*amount*(342+2*f))) := by
  have rows : 870+12*b+50*X+4*f≤(932+4*f)*H :=calc
    _ ≤ 870*H+12*H+50*H+(4*f)*H :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_mul_of_pos_right _ hosts)
        (Nat.mul_le_mul_left _ grain)) (Nat.mul_le_mul_left _ pages)) (Nat.le_mul_of_pos_right _ hosts)
    _ = _ := by ring
  calc
    _ ≤ K*(8*h+(H*h+4*H*groups*amount)*(2*f+158))+(322+4*f)*(K*h)+
        (K*((131+4*b)*h+124*(H*h+4*H*groups*amount)+20*X*h)+11*(K*h))+
        K*((398+8*b+30*X)*h+60*(H*h+4*H*groups*amount)) :=by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add rg (rt.trans (Nat.mul_le_mul_left _ word)))
        (rm.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ word) _))) rn
    _ = K*((870+12*b+50*X+4*f)*h+(H*h+4*H*groups*amount)*(342+2*f)) := by ring
    _ ≤ K*(((932+4*f)*H)*h+(H*h+4*H*groups*amount)*(342+2*f)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ rows) _)
    _ = H*h*(K*(1274+6*f))+H*groups*(K*(4*amount*(342+2*f))) := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ block))) _

end Hierarchy.DescentCompiler.TerminalScale

end OAI
