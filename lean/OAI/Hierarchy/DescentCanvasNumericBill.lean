import OAI.Hierarchy.DescentCanvasPricePolynomial
import OAI.Hierarchy.DescentPackedCanvasHardware
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # Runtime and instruction words of the physically mounted reset canvas -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentSIMDLookup DescentPackedFlowPublication DescentPackedRectangle
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentStaticWordColumn
noncomputable section

/-- The first summand pays a physical host and its packed slabs. The last
summand pays all common exponential tables once, including the front gate book. -/
theorem numeric (H D R k c u l b short batch h : ℕ)
    (host : 0<H) (batchSize : chunks R batch=2^u) (lanes : 2^l=2^k*batch)
    (small : short≤b*2^k) (key : bigKey l b≤h/2) :
    totalWork H D R u l b short batch k c +7*allText H D u l b short batch k c ≤
      canvasCoeff D*(((u+l)+1)*(2^k*(c+1))*(H*2^u)+((u+l)+1)*2^k*2^(h/2)) :=by
  let y:=2^u
  let r:=2^k
  let Q:=2^(h/2)
  have hy : 0<y:=Nat.two_pow_pos _
  have hrow : 0<H*y:=Nat.mul_pos host hy
  have pg : page H u≤4*(H*y):=by
    unfold page rowBits
    rw [pow_succ]
    have a:=Nat.pow_log_le_self 2 (Nat.succ_ne_zero (H*2^u))
    change 2 ^ Nat.log 2 (H*2^u+1) ≤ H*2^u+1 at a
    change 0<H*2^u at hrow
    dsimp only [y]
    omega
  have ix : 2^(Book.pitchBits H u)≤4*(H*y):=by
    have p:=Placement.pad_le H
    change 2^Nat.clog 2 H≤2*(H+1) at p
    have hp:2^Nat.clog 2 H≤4*H:=by omega
    rw [Book.pitchBits,pow_add]
    exact (Nat.mul_le_mul_right _ hp).trans_eq (by dsimp [y];ring)
  have wk : smallKey l b≤bigKey l b:=by unfold smallKey bigKey;rw [Nat.add_mul];omega
  have wk₁ : 2^(smallKey l b)≤Q:=Nat.pow_le_pow_right (by decide) (wk.trans key)
  have wk₂ : 2^(bigKey l b)≤Q:=Nat.pow_le_pow_right (by decide) key
  have gate : Book.width b r short*batch≤bigKey l b:=by
    have s:short≤b*r:=small
    rw [Book.width,max_eq_right (Nat.add_le_add_left s _),bigKey,lanes]
    change (b*r+b*r)*batch≤1+(b+b)*(r*batch)
    calc
      _ = (b+b)*(r*batch):=by ring
      _ ≤ 1+(b+b)*(r*batch):=Nat.le_add_left ..
  have gk : 2^(Book.width b r short*batch)≤Q:=Nat.pow_le_pow_right (by decide) (gate.trans key)
  rw [totalWork,batchSize]
  change account H D (u+l) y r c (page H u) (2^(Book.pitchBits H u))
    (4^(Nat.clog 2 D)) (2^(smallKey l b)) (2^(bigKey l b)) (2^(Book.width b r short*batch))≤_
  refine le_trans ?_ (polynomials H D (u+l) y r c (4^(Nat.clog 2 D)) Q host hy (Nat.two_pow_pos _))
  dsimp only [account]
  gcongr

/-- This value is measured from the supplied physical CPU and its two native clocks. -/
structure Date (k c : ℕ) where
  tokens : Tokens k c
  roster : Bank
  src : Bank
  count : Bank
  floor : ℕ
  f : ℕ
  bound : ℕ
  quota : ℕ
  grain : ℕ
  δ : ℕ
  out : ℕ

def Date.cpu {k c : ℕ} (X : Date k c) (H D R u l b short batch w : ℕ) :=
  let C:=core X.tokens X.roster H D u l b short batch X.floor X.f X.bound X.quota X.grain
  let p:=plan X.tokens X.roster H D u l b short batch X.floor X.f X.bound X.quota X.grain
  (prep X.tokens X.roster H D u l b short batch X.floor X.f X.bound X.quota X.grain X.src R w).seq
    (p.prepare C X.count k X.δ R batch w X.out)

def Date.fee {k c : ℕ} (X : Date k c) (H D R u l b short batch w : ℕ) :=
  let C:=core X.tokens X.roster H D u l b short batch X.floor X.f X.bound X.quota X.grain
  let p:=plan X.tokens X.roster H D u l b short batch X.floor X.f X.bound X.quota X.grain
  (ticks H D u l b short batch X.floor X.f X.bound X.quota k R+p.prepareTicks C k X.δ R batch w+
    7*names (X.cpu H D R u l b short batch w))*w

theorem Date.measured {k c : ℕ} (X : Date k c) (H D R u l b short batch h w : ℕ)
    (host : 0<H) (batchSize : chunks R batch=2^u) (lanes : 2^l=2^k*batch)
    (small : short≤b*2^k) (key : bigKey l b≤h/2) :
    X.fee H D R u l b short batch w ≤
      (canvasCoeff D*(((u+l)+1)*(2^k*(c+1))*(H*2^u)+((u+l)+1)*2^k*2^(h/2)))*w :=by
  have rt:=full_runtime X.tokens X.roster H D R u l b short batch X.floor X.f X.bound X.quota X.grain X.δ w batchSize
  have code_:= (full_hardware X.tokens X.roster X.src X.count H D R u l b short batch X.floor X.f X.bound X.quota X.grain X.δ w X.out).2
  exact Nat.mul_le_mul_right w ((Nat.add_le_add rt (Nat.mul_le_mul_left 7 code_)).trans
    (numeric H D R k c u l b short batch h host batchSize lanes small key))

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
