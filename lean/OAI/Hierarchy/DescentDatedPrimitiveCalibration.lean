import OAI.Hierarchy.DescentDatedPrimitivePitch
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! Public degree and occupancy budgets for the ordinary primitive archive's work and return pitches. -/
namespace Hierarchy.DescentOrdinaryPalette.Configuration
open DescentCompiler.TerminalScale
noncomputable section

theorem units_le (D k cap old nodes bits a : ℕ) (blocks : 2^k≤a) (oldRoom : old≤a)
    (newRoom : nodes≤a) (bitRoom : bits≤a) (halo : (D+1)^4*2^k≤a)
    (pool : (D+1)^4*2^k*(old+cap*6)≤a) :
    workUnit D k cap old nodes bits≤4*(a+1)^3 ∧ returnUnit bits nodes≤(a+1)^2:=by
  let r:=2^k
  let P:=(D+1)^4*r
  let N:=P*(old+cap*6)
  let R : DescentOrdinaryRefsROM.Chart:=⟨0,D,k,old,nodes,cap,bits,0,0,1⟩
  have actors : R.actors≤2*a:=by
    change P*(1+cap*6)≤2*a
    have capRoom : P*(cap*6)≤a:=(Nat.mul_le_mul_left P (Nat.le_add_left _ _)).trans pool
    rw [Nat.mul_add,Nat.mul_one,two_mul]
    exact Nat.add_le_add halo capRoom
  have keys : R.keyBits≤2*(a+1)^2:=by
    simp only [DescentOrdinaryRefsROM.Chart.keyBits,Nat.max_le,Nat.zero_mul,
      Nat.add_zero,Nat.one_mul,R]
    have nodeRoom : R.nodes≤a:=pool
    have bitNodes : bits*R.nodes≤a*a:=Nat.mul_le_mul bitRoom nodeRoom
    change 0≤_ ∧ (R.actors≤_ ∧ (R.nodes+bits*R.nodes≤_ ∧ bits*R.nodes+bits≤_))
    constructor
    · omega
    · exact ⟨by nlinarith only [actors],by nlinarith only [bitNodes,nodeRoom],by nlinarith only [bitNodes,bitRoom]⟩
  have logRoom : Nat.clog 2 (N+1)≤a+1:=(Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    (by exact (Nat.succ_le_succ pool).trans (Nat.lt_two_pow_self.le : a+1≤2^(a+1)))
  have keyBlock : R.keyBits*r≤(2*(a+1)^2)*a:=Nat.mul_le_mul keys blocks
  have oldBlock : bits*old*r≤a*a*a:=Nat.mul_le_mul (Nat.mul_le_mul bitRoom oldRoom) blocks
  have poolBlock : bits*N*r≤a*a*a:=Nat.mul_le_mul (Nat.mul_le_mul bitRoom pool) blocks
  have choose : Nat.clog 2 (N+1)*nodes+bits*N≤(a+1)*a+a*a:=
    Nat.add_le_add (Nat.mul_le_mul logRoom newRoom) (Nat.mul_le_mul bitRoom pool)
  have packed : bits*nodes≤a*a:=Nat.mul_le_mul bitRoom newRoom
  change max 1 (max r (max (bits*old*r) (max (R.keyBits*r) (max (bits*N*r)
    (max (Nat.clog 2 (N+1)*nodes+bits*N) (bits*nodes))))))≤_ ∧ max 1 (bits*nodes)≤_
  simp only [Nat.max_le]
  have blockRoom : r≤a:=blocks
  repeat' apply And.intro
  all_goals nlinarith only [keyBlock,oldBlock,poolBlock,choose,packed,blockRoom]

theorem units_rate (D k cap old nodes bits J c : ℕ) (blocks : 2^k≤ scale J c) (oldRoom : old≤ scale J c)
    (newRoom : nodes≤ scale J c) (bitRoom : bits≤ scale J c) (halo : (D+1)^4*2^k≤ scale J c)
    (pool : (D+1)^4*2^k*(old+cap*6)≤ scale J c) :
    4*workUnit D k cap old nodes bits≤ scale J (8+3*c) ∧
    4*returnUnit bits nodes≤ scale J (8+3*c):=by
  let a:=scale J c
  obtain ⟨work,ret⟩:=units_le D k cap old nodes bits a blocks oldRoom newRoom bitRoom halo pool
  have pos : 1≤a:=Nat.two_pow_pos _
  have sh : a+1≤2*a:=by omega
  have square : a^2≤a^3:=by rw [pow_succ a 2]; exact Nat.le_mul_of_pos_right _ pos
  have amount : 2^8*a^3≤ scale J (8+3*c):=by
    calc 2^8*a^3=2^(8+3*(c*(J+1))):=by simp only [a,scale,Nat.pow_add,←pow_mul];congr 2; ring
         _ ≤ _ :=Nat.pow_le_pow_right (by decide : 0<2) (by nlinarith : 8+3*(c*(J+1))≤(8+3*c)*(J+1))
  exact ⟨(by nlinarith only [work,Nat.pow_le_pow_left sh 3] : 4*workUnit D k cap old nodes bits≤2^8*a^3).trans amount,
    (by nlinarith only [ret,Nat.pow_le_pow_left sh 2,square] : 4*returnUnit bits nodes≤2^8*a^3).trans amount⟩

end
end Hierarchy.DescentOrdinaryPalette.Configuration

end OAI
