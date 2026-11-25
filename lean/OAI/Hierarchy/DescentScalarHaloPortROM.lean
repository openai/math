import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Address pages for a packed sorted halo roster -/
namespace Hierarchy.DescentScalarHaloPortROM
open DescentSIMDLookup ProtocolRAM DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (H G M P : ℕ)
local notation "n"=>H*chunks G M
abbrev Item:=(Fin P×Row H G M)⊕(Fin H⊕(Row H G M⊕(Fin H×Fin P)))
def length:=P*n+(H+(n+H*P))
def index : Item H G M P≃Fin (length H G M P):=
  ((((Equiv.refl _).prodCongr (row H G M)).trans finProdFinEquiv).sumCongr (((Equiv.refl _).sumCongr (((row H G M).sumCongr finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

def word : Item H G M P→ℕ
  | .inl (s,p)=>p.1.val*P+s.val
  | .inr (.inl h)=>chunks G M*h.val
  | .inr (.inr (.inl p))=>p.2.val
  | .inr (.inr (.inr (_,s)))=>s.val

def literal (j:ℕ):=if hi:j<length H G M P then word H G M P ((index H G M P).symm ⟨j,hi⟩) else 0

def chart (base : ℕ) (rank : Bank) : Ports P:=⟨fun s=>⟨base+s.val*n,Nat.clog 2 n⟩,rank,⟨base+P*n,Nat.clog 2 H⟩,⟨base+P*n+H,Nat.clog 2 n⟩⟩
def slot (base : ℕ) : Bank:=⟨base+P*n+H+n,Nat.clog 2 (H*P)⟩
def pad:=2^(Nat.clog 2 (max (H*P) (max n H)+1))
def stop (base : ℕ):=base+length H G M P+pad H G M P

def program (w base : ℕ) :=DescentStaticWordColumn.program w base (literal H G M P) (length H G M P)
def image (base : ℕ) (m : Memory w) :=DescentStaticWordColumn.image base (literal H G M P) m (length H G M P)

private theorem byIndex (base : ℕ) (m : Memory w) (j : Item H G M P) : image H G M P base m (base+((index H G M P) j).val)=(word H G M P j:Word w):=by
  have read:=DescentStaticWordColumn.read base (length H G M P) (literal H G M P) m ((index H G M P) j).isLt
  refine read.trans ?_
  unfold literal
  rw [dite_eq_left ((index H G M P) j).isLt]
  change ((word H G M P ((index H G M P).symm ((index H G M P) j)) : ℕ):Word w)=_
  rw [Equiv.symm_apply_apply]

structure Shape (base : ℕ) (rank : Bank) (m : Memory w) : Prop where
  ids : ∀s (p : Row H G M),m (((chart H G M P base rank).ids s).base+(row H G M p).val)=((p.1.val*P+s.val:ℕ):Word w)
  offsets : ∀h:Fin H,m ((chart H G M P base rank).offsets.base+h.val)=((chunks G M*h.val:ℕ):Word w)
  chunks : ∀p:Row H G M,m ((chart H G M P base rank).chunks.base+(row H G M p).val)=(p.2.val:Word w)
  slots : ∀(h:Fin H)(s:Fin P),m ((slot H G M P base).base+(h.val*P+s.val))=(s.val:Word w)

theorem mount (base : ℕ) (rank : Bank) (m : Memory w) (fit : base+length H G M P<2^w) :
    let o:=image H G M P base m
    (program H G M P w base).Exec m o (4+10*length H G M P) ∧ Shape H G M P base rank o ∧
      (∀j,j<base ∨ base+length H G M P≤j → o j=m j) ∧ CheapCode (program H G M P w base):=by
  intro o
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ fit,⟨?_,?_,?_,?_⟩,
    DescentStaticWordColumn.frame base (length H G M P) (literal H G M P) m,?_⟩
  · intro s p
    refine Eq.trans ?_ (byIndex H G M P base m (.inl (s,p)))
    apply congrArg o
    change base+s.val*n+(row H G M p).val=base+((row H G M p).val+n*s.val)
    ring
  · intro h
    refine Eq.trans ?_ (byIndex H G M P base m (.inr (.inl h)))
    apply congrArg o
    change base+P*n+h.val=base+(P*n+h.val)
    omega
  · intro p
    refine Eq.trans ?_ (byIndex H G M P base m (.inr (.inr (.inl p))))
    apply congrArg o
    change base+P*n+H+(row H G M p).val=base+(P*n+(H+(row H G M p).val))
    omega
  · intro h s
    refine Eq.trans ?_ (byIndex H G M P base m (.inr (.inr (.inr (h,s)))))
    apply congrArg o
    change base+P*n+H+n+(h.val*P+s.val)=base+(P*n+(H+(n+(s.val+P*h.val))))
    ring
  · exact @DescentStaticWordColumn.cheap w base (literal H G M P) (length H G M P)

private theorem bankBudget {base out : ℕ} (hi : stop H G M P base≤out) (room : out<2^w) (v size : ℕ) (start : v≤base+length H G M P)
    (sizeFit : size ≤ max (H*P) (max n H)+1) : (⟨v,Nat.clog 2 size⟩ : Bank).Fits w out ∧ size≤(⟨v,Nat.clog 2 size⟩:Bank).size:=by
  have wide:2^Nat.clog 2 size≤pad H G M P:=Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right _ sizeFit)
  have end_:v+2^Nat.clog 2 size≤out:=(Nat.add_le_add start wide).trans hi
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt room),end_⟩,Nat.le_pow_clog (by decide) _⟩

theorem statics (base out : ℕ) (rank : Bank) (early : stop H G M P base≤out) (room : out<2^w) :
    let c:=chart H G M P base rank
    (∀s,(c.ids s).Fits w out ∧ n≤(c.ids s).size) ∧ (c.offsets.Fits w out ∧ H≤c.offsets.size) ∧
      (c.chunks.Fits w out ∧ n≤c.chunks.size) ∧ (slot H G M P base).Fits w out ∧ H*P≤(slot H G M P base).size:=by
  intro c
  let cap_:=max (H*P) (max n H)
  have ncap:n≤cap_+1:=(le_max_left ..).trans ((le_max_right ..).trans (Nat.le_succ _))
  have hcap:H≤cap_+1:=(le_max_right ..).trans ((le_max_right ..).trans (Nat.le_succ _))
  have pcap:H*P≤cap_+1:=(le_max_left ..).trans (Nat.le_succ _)
  have ids(s:Fin P):=((bankBudget H G M P early room (base+s.val*n) n (by have t:=Nat.mul_le_mul_right n s.isLt.le;dsimp [length];omega) ncap))
  have off:=bankBudget H G M P early room (base+P*n) H (by dsimp [length];omega) hcap
  have ch:=bankBudget H G M P early room (base+P*n+H) n (by dsimp [length];omega) ncap
  have sl:=bankBudget H G M P early room (base+P*n+H+n) (H*P) (by dsimp [length];omega) pcap
  exact ⟨ids,off,ch,sl⟩

theorem geometry (base out : ℕ) (rank src : Bank) (early : stop H G M P base≤out) (room : out<2^w)
    (rr : rank.Fits w out) (rs : H*P≤rank.size) (sr : src.Fits w out) (ss : n≤ src.size) :
    Accessible (chart H G M P base rank) src H G M w out ∧ (slot H G M P base).Fits w out ∧ H*P≤(slot H G M P base).size:=by
  obtain ⟨ids,off,ch,sl⟩:=statics H G M P base out rank early room
  exact ⟨⟨fun i=>(ids i).1,fun i=>(ids i).2,rr,rs,off.1,off.2,ch.1,ch.2,sr,ss⟩,sl⟩

end
end Hierarchy.DescentScalarHaloPortROM

end OAI
