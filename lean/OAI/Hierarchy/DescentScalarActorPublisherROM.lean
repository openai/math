import OAI.Hierarchy.DescentScalarActorPublisher
import OAI.Hierarchy.DescentZipBook

namespace OAI
/-! # Literal shape tables project original owner registers and six-party head fields -/
namespace Hierarchy.DescentScalarVenueMask.Publisher.ROM
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r D cap d slots raw H G M w : ℕ}
local notation "K"=>1+cap*6
local notation "N"=>2*(r*K)
local notation "regSize"=>((Owners.digits r D d*3)*r)
local notation "headsSize"=>Owners.outputBits r D (2*cap) d

def gate (D d slots raw : ℕ) (c : choice r cap) : Book.Gate:=
  (finSumFinEquiv.symm c.2.2).elim (fun _:Fin 1=>⟨1*r,((Owners.digits r D d*3)*r),_,oldFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) c.1 c.2.1⟩)
    (fun z:Fin (cap*6)=>let u:=finProdFinEquiv.symm z;⟨1*r,Owners.outputBits r D (2*cap) d,_,bornFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) c.1 c.2.1 u.1 u.2⟩)

def entries (r D cap d slots raw : ℕ) (i : Fin (2*(r*(1+cap*6)))):=gate D d slots raw ((index r cap).symm i)
def unit (r D cap d : ℕ):=1*r+max ((Owners.digits r D d*3)*r) (Owners.outputBits r D (2*cap) d)
def size (r D cap d M : ℕ):=2*(r*(1+cap*6))*(2*2^(unit r D cap d*M))

def chart (D d slots raw M base : ℕ) (mask old born : Bank) : Chart r cap:=
  ⟨mask,old,born,fun c=>Book.tables (entries r D cap d slots raw) (unit r D cap d) M base (index r cap c)⟩

theorem width (i : Fin N) : let g:=entries r D cap d slots raw i;g.left+g.right≤unit r D cap d:=by
  unfold entries gate;cases finSumFinEquiv.symm ((index r cap).symm i).2.2 <;> simp [unit]

theorem mounted (base out : ℕ) (mask old born : Bank) (m : Memory w)
    (active : Fin H→Fin G→Cell (1*r)) (prior : Fin H→Fin G→Owners.Register r D d) (heads : Fin H→Fin G→Cell headsSize)
    (separation : base+size r D cap d M≤out) (space : out<2^w)
    (mfit : mask.Fits w base) (ofit : old.Fits w base) (bfit : born.Fits w base)
    (mroom : H*chunks G M≤ mask.size) (oroom : H*chunks G M≤old.size) (broom : H*chunks G M≤born.size)
    (masked : Reads mask active M m) (prior_ : Reads old prior M m) (issued : Reads born heads M m) :
    let f:=entries r D cap d slots raw;let length:=unit r D cap d;let mid:=Book.image f length M base m
    (Book.install f length M w base).Exec m mid (4+10*size r D cap d M) ∧
    Publisher.Mounted (chart D d slots raw M base mask old born) D d slots raw H G M out mid active prior heads ∧
      (∀a,a<base ∨ base+size r D cap d M≤a→mid a=m a) ∧ CheapCode (Book.install f length M w base) :=by
  intro f length mid
  have mounted_:=Book.mount f length M base m (fun j=>width j) (separation.trans_lt space)
  have eqn (u:choice r cap) : f (index r cap u)=gate D d slots raw u:=by simp [f,entries]
  have staticAt (u : choice r cap) (g : Book.Gate) (same : gate D d slots raw u = g) : Static (Book.tables f length M base (index r cap u))
      g.eval M mid := by
    let property (g : Book.Gate) := Static (Book.tables f length M base (index r cap u)) g.eval M mid
    change property g
    exact ((eqn u).trans same) ▸ (show property (f (index r cap u)) from mounted_.2.1 (index r cap u))
  have banks (u : choice r cap) :=Book.geometry f length M base (index r cap u) separation space (width _)
  have before : base≤out:=(Nat.le_add_right ..).trans separation
  have lift (B:Bank) (h:B.Fits w base):B.Fits w out:=⟨h.1,h.2.1,h.2.2.trans before⟩
  have keep {n : ℕ} (B:Bank) (data_:Fin H→Fin G→Cell n) (fits:B.Fits w base) (cap_:H*chunks G M≤B.size) (read:Reads B data_ M m):Source (.lookup B .row) data_ M mid:=by
    apply source_column B out (lift B fits) mid data_ cap_;intro j
    exact (mounted_.2.2.1 _ (.inl ((Nat.add_lt_add_left ((row H G M j).isLt.trans_le cap_) _).trans_le fits.2.2))).trans (read j)
  refine ⟨mounted_.1,⟨keep _ _ mfit mroom masked,keep _ _ ofit oroom prior_,keep _ _ bfit broom issued,?_,?_,?_,?_⟩,mounted_.2.2⟩
  · intro f' x;let u:choice r cap:=(f',x,finSumFinEquiv (Sum.inl (0:Fin 1)))
    refine ⟨⟨lift mask mfit,trivial⟩,⟨lift old ofit,trivial⟩,(banks u).1,(banks u).2,?_,?_⟩ <;> simp [chart,Book.tables,entries,gate,Equiv.symm_apply_apply]
  · intro f' x z;let u:choice r cap:=(f',x,finSumFinEquiv (Sum.inr z))
    refine ⟨⟨lift mask mfit,trivial⟩,⟨lift born bfit,trivial⟩,(banks u).1,(banks u).2,?_,?_⟩ <;> simp [chart,Book.tables,entries,gate,Equiv.symm_apply_apply]
  · intro f' x;let u:choice r cap:=(f',x,finSumFinEquiv (Sum.inl (0:Fin 1)))
    apply staticAt u ⟨1*r,regSize,_,oldFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) f' x⟩
    simp [gate,u]
  · intro f' x z;let u:choice r cap:=(f',x,finSumFinEquiv (Sum.inr z))
    apply staticAt u ⟨1*r,headsSize,_,bornFunction (D:=D) (d:=d) (slots:=slots) (raw:=raw) f' x
      (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2⟩
    simp [gate,u]

end
end Hierarchy.DescentScalarVenueMask.Publisher.ROM

end OAI
