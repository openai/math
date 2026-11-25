import OAI.Hierarchy.DescentPackedWalshRAM

namespace OAI
/-! # Literal Walsh controller headers and one ordered working page per chronological layer -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

def rowBits (H u : ℕ) := Nat.log 2 (H*2^u+1)+1
def page (H u : ℕ) := 2^(rowBits H u)
def smallKey (l b : ℕ) := b*2^l
def bigKey (l b : ℕ) := 1+(b+b)*2^l

def span (H u l b : ℕ) := 3*page H u+2^(smallKey l b)+2^(bigKey l b)

def shelf (root first t H u l b : ℕ) : Banks :=
  let offset:=root+t*span H u l b
  let bits:=rowBits H u
  let P:=page H u
  ⟨⟨first+t*P,bits⟩,⟨offset,bits⟩,⟨offset+P,bits⟩,⟨offset+2*P,bits⟩,
    ⟨offset+3*P,smallKey l b⟩,⟨offset+3*P+2^(smallKey l b),bigKey l b⟩⟩

theorem rows_le (H u : ℕ) : H*2^u≤page H u := by
  exact (Nat.le_succ _).trans (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _))

def outPage (first H u t : ℕ) := first+(t+1)*page H u

theorem room {w : ℕ} (root first t H u l b : ℕ) (prefixBound : root+(t+1)*span H u l b≤first)
    (limit : first+(t+2)*page H u<2^w) :
    Room (shelf root first t H u l b) (outPage first H u t) H u l b w := by
  have pagePositive:=Nat.two_pow_pos (rowBits H u)
  have shiftPositive:=Nat.two_pow_pos (smallKey l b)
  have tabPositive:=Nat.two_pow_pos (bigKey l b)
  have rows:=rows_le H u
  change root+(t+1)*(3*page H u+2^(smallKey l b)+2^(bigKey l b))≤first at prefixBound
  have progress : (t+1)*page H u=t*page H u+page H u := Nat.succ_mul _ _
  have last : (t+2)*page H u=(t+1)*page H u+page H u := Nat.succ_mul _ _
  rw [Nat.succ_mul] at prefixBound
  constructor
  all_goals simp only [shelf,outPage,Bank.Fits,Bank.size,span,page,smallKey,bigKey] at *
  all_goals repeat' apply And.intro
  all_goals omega

/-- One header has three ordinary index columns and the two actual contents of the short ROMs. -/
def headerWord {w u l : ℕ} (H b : ℕ) (a : Axis u l) (off : ℕ) : Word w :=
  let P:=page H u
  let L:=smallKey l b
  let U:=bigKey l b
  if _h : off<3*P then
    let ix:=off%P
    if live : ix<H*2^u then
      let p:=unrow ⟨ix,live⟩
      if off<P then (row p.1 (above a p.2 false)).val
      else if off<2*P then (row p.1 (above a p.2 true)).val
      else 2^((b+b)*2^l)*(upperSign a p.2).toNat
    else 0
  else if _s : off-3*P<2^L then 2^L*(off-3*P)
  else if k : off-(3*P+2^L)<2^U then
    (dictionary (b:=b) a ⟨off-(3*P+2^L),k⟩).val
  else 0

def mounted {w u l : ℕ} (H b root : ℕ) (axes : List (Axis u l)) (m : Memory w) (z : ℕ) : Word w :=
  if root≤z then
    let block:=span H u l b
    match axes[(z-root)/block]? with
    | some a=>headerWord H b a ((z-root)%block)
    | none=>m z
  else m z

theorem mounted_at {w u l : ℕ} (H b root : ℕ) (axes : List (Axis u l)) (m : Memory w)
    (t : Fin axes.length) (j : Fin (span H u l b)) :
    mounted H b root axes m (root+t.val*span H u l b+j.val)=headerWord H b axes[t.val] j.val := by
  have positive : 0<span H u l b:=by unfold span;positivity
  have outer : root≤root+t.val*span H u l b+j.val := by omega
  have delta : root+t.val*span H u l b+j.val-root=t.val*span H u l b+j.val := by omega
  have div : (t.val*span H u l b+j.val)/span H u l b=t.val := by
    rw [Nat.mul_comm t.val,Nat.mul_add_div positive,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have rem : (t.val*span H u l b+j.val)%span H u l b=j.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  simp [mounted,outer,delta,div,rem,t.isLt]

end
end Hierarchy.DescentPackedWalsh

end OAI
