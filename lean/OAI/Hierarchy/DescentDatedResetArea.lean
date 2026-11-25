import OAI.Hierarchy.DescentDatedResetPrice

namespace OAI
/-! # Public numeric addresses for every phase after the reset estimator -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGLPacked DescentGLNielsen DescentGLControlCode ProtocolRAM
noncomputable section

def controlSize (h l : ℕ) :=
  let d:=h+l
  keys d+Count d+Count d*keys d+d*2^h

def chart (origin H h l b : ℕ) : Chart :=
  let input : Bank:=⟨origin+4*(controlSize h l+1),Nat.clog 2 (H*2^h)⟩
  let flags:=input.base+input.size
  ⟨flags+Count (h+l),chartBits H h l b,input,flags⟩

def endAddress (origin H h l b : ℕ) :=
  let C:=chart origin H h l b
  C.heap (h+l)+(Count (h+l)+1)*C.page

theorem rounded (s : ℕ) : 2^(Nat.clog 2 s)≤2*(s+1) := by
  cases eq:Nat.clog 2 s with
  | zero=>simp only [pow_zero]; omega
  | succ t=>
    have lt : t<Nat.clog 2 s := by omega
    have pow:=Nat.pow_lt_of_lt_clog lt
    rw [pow_succ]
    omega

theorem extent (origin H h l b : ℕ) :
    endAddress origin H h l b=origin+4*(controlSize h l+1)+2^(Nat.clog 2 (H*2^h))+Count (h+l)+
      (7*Count (h+l)+1)*2^chartBits H h l b := by
  dsimp [endAddress,chart,Chart.heap,Chart.base,Chart.page,Bank.size,Count]
  ring

theorem origin_le_endAddress (origin H h l b : ℕ) : origin ≤ endAddress origin H h l b := by
  simp only [extent, Nat.add_assoc]
  exact Nat.le_add_right ..

theorem sized (origin H h l b w : ℕ) (space : endAddress origin H h l b<2^w) :
    let C:=chart origin H h l b
    Size C H h l b w ∧ wordEnd origin h l≤C.input.base ∧ C.input.base+C.input.size≤C.flags ∧
    (powers origin (h+l)).Fits w C.input.base ∧ (cols origin (h+l)).offsets.Fits w C.input.base ∧
    (cols origin (h+l)).switches.Fits w C.input.base ∧
    ∀j:Fin (h+l),(Original.bank (l:=l) (plane origin (h+l)) h j).Fits w C.input.base := by
  let C:=chart origin H h l b
  let d:=h+l
  have order:C.start≤endAddress origin H h l b := by
    change C.start≤(C.start+6*(schedule d).length*C.page)+(Count d+1)*C.page
    omega
  have start:C.start<2^w:=order.trans_lt space
  have gap : C.input.base+C.input.size≤C.flags:=le_rfl
  have next : C.flags+Count d≤C.start:=le_rfl
  have endword : wordEnd origin h l≤C.input.base:=by
    dsimp [C,chart,wordEnd,controlSize,plane]
    omega
  have previous : C.input.base<2^w:=by omega
  have old (B : Bank) (fits : B.base+B.size≤C.input.base) : B.Fits w C.input.base :=
    ⟨Nat.two_pow_pos _,by omega,fits⟩
  have inSize : H*2^h≤C.input.size:=Nat.le_pow_clog (by decide) _
  have inFit : C.input.Fits w C.start := ⟨Nat.two_pow_pos _,by omega,by omega⟩
  refine ⟨size_of C rfl inFit inSize next space,endword,gap,?_,?_,?_,?_⟩
  · apply old
    have keep:=rounded (keys d)
    dsimp [powers,Bank.size,C,chart,controlSize,d] at *
    omega
  · apply old
    have keep:=rounded (Count d)
    dsimp [cols,Bank.size,C,chart,controlSize,d] at *
    omega
  · apply old
    have keep:=rounded (Count d*keys d)
    dsimp [cols,Bank.size,C,chart,controlSize,d] at *
    omega
  · intro j
    apply old
    have p:=Nat.mul_le_mul_right (2^h) j.isLt
    rw [Nat.succ_mul] at p
    change plane origin (h+l)+j.val*2^h+2^h≤_
    dsimp only [wordEnd] at endword
    omega

theorem paid_extent (origin H h l b payload : ℕ)
    (width : (b+b)*2^l≤payload/2) (square : (h+l)*(h+l)≤payload/2) :
    let m:=h+l
    let n:=Count m
    let root:=2^(payload/2)
    endAddress origin H h l b≤origin+4*((1+n)*root+n+m*2^h+1)+2*(H*2^h+1)+n+
      (7*n+1)*(2*(H*2^h+1)+root) := by
  let d:=h+l
  let n:=Count d
  have values:keys d≤2^(payload/2):=by
    rw [keys,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) square
  have codes:=Nat.mul_le_mul_left n values
  have ctrl : controlSize h l≤(1+n)*2^(payload/2)+n+d*2^h := by
    rw [Nat.add_mul,Nat.one_mul]
    change keys d+n+n*keys d+d*2^h≤_
    omega
  have rowBound:=rounded (H*2^h)
  have tables:=Nat.mul_le_mul_left (7*n+1) (pages H h l b payload width)
  rw [extent]
  dsimp only [n,d] at ctrl tables ⊢
  omega

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI
