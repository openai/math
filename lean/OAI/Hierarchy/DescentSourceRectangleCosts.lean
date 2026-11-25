import OAI.Hierarchy.DescentOperandPathPriceNumbers
import OAI.Hierarchy.DescentArgumentWordRectangle

namespace OAI
/-! # Public rectangular costs for the original host paths and the fifteen retained fields -/
namespace Hierarchy.DescentArgumentWordRectangle
open DescentDatedSourcePathDirectory DescentHaloWalkRAM

def columnRate (K : ℕ) :=109+K*(85+30*K)

theorem path_column (n H ops h ratio Z K : ℕ) (count : n≤K) (work : ops≤K)
    (fixed : h≤Z) (rows : H*h≤Z) :
    columnCost n H ops h ratio≤columnRate K*ratio*Z :=by
  unfold columnCost columnRate
  calc
    _≤ratio*((109+K*(81+28*K))*Z+K*(2*K+4)*Z):=by gcongr
    _=_:=by ring

def pathRate (K : ℕ) :=columnRate K+109+115*(4*(1+4*K)+3+2*(2*(K+1)+1))

theorem physical_path {H G D u h ratio Z K : ℕ} (origin : h≤Z) (old : H*h≤Z)
    (rows : H*G≤Z) (padding : (h+1)*h≤Z) (unit : u≤K) (branch : breadth D≤K)
    (ports : breadth D*(D+1)≤K)
    (loop : (breadth D+1)*(30+4*breadth D+4*(breadth D*breadth D))≤K) :
    pathCharge H G D h (4*u) ratio≤pathRate K*ratio*Z :=by
  have host : hostCost H D h ratio≤columnRate K*ratio*Z:=path_column _ _ _ _ _ _ _ ports loop origin old
  have idH : (3+2*(h+1)*(2*(breadth D+1)+1))*h=3*h+2*(2*(breadth D+1)+1)*((h+1)*h):=by ring
  unfold pathCharge
  rw [idH]
  calc
    _≤columnRate K*ratio*Z+ratio*(109*Z+115*(4*(Z+Z*(4*K))+(3*Z+2*(2*(K+1)+1)*Z))):=by gcongr
    _=_:=by unfold pathRate;ring

def depotRate (K : ℕ) :=2048*(K+1)*(3+4*K)+2048*(1+2*K+8*K*K)+4096

theorem depot {N H G u a h ratio Z K : ℕ} (fields : N≤K) (unit : u≤K) (next : a≤K)
    (origin : h≤Z) (host : H*h≤Z) (grid : H*G≤Z) (small : 2^(h/2)*h≤Z)
    (pages : (h+1)^2*2^(h/2)*h≤Z) :
    2048*ratio*(N+1)*(h+H*h+H*G*(4*u))+2048*ratio*(N+1)*2^(h/2)*h+
      2048*ratio*(h+2*(N*H)*h+(N*H)*G*(4*u+4*a))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h≤
      depotRate K*ratio*Z :=by
  have pc : 2048*ratio*(N+1)*2^(h/2)*h=2048*ratio*(N+1)*(2^(h/2)*h):=by ring
  have final : (2048*ratio)*(2*(h+1)^2*2^(h/2))*h=4096*ratio*((h+1)^2*2^(h/2)*h):=by ring
  have hh : 2*(N*H)*h=2*N*(H*h):=by ring
  have gg : (N*H)*G=N*(H*G):=Nat.mul_assoc ..
  rw [pc,final,hh,gg]
  calc
    _≤2048*ratio*(K+1)*(Z+Z+Z*(4*K))+2048*ratio*(K+1)*Z+
      2048*ratio*(Z+2*K*Z+K*Z*(4*K+4*K))+4096*ratio*Z:=by gcongr
    _=_:=by unfold depotRate;ring

end Hierarchy.DescentArgumentWordRectangle

end OAI
