import OAI.Hierarchy.DescentColonyNativeBatch
import OAI.Hierarchy.DescentColonyPermutationRAM
import OAI.Hierarchy.DescentColonyPhysicalCensus

namespace OAI
/-! # Pulling all site loads through a candidate multiplier and finding its census -/

noncomputable section
namespace Hierarchy.DescentColonies.SiteRAM
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open NativeBatch
open DescentGL (Bits Nonzero)
open scoped Fin.CommRing

variable {w H k : ℕ}

def bank (k base t : ℕ) := base+t*2^k

private theorem bank_mono (k base : ℕ) {s t : ℕ} (st : s≤t) : bank k base s ≤ bank k base t :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ st) _

private theorem bank_succ (k base i : ℕ) : bank k base (i+1)=bank k base i+2^k := by
  simp [bank,Nat.succ_mul,Nat.add_assoc]

def transfer (w k base : ℕ) (p : Fin H→ℕ) (a μ : Bits k) (i : Fin H) : Code w :=
  let dest := bank k base i.val
  let e := PermutationRAM.expr (p i) a μ
  ⟨scan w dest (2^k) e, image dest (2^k) e, 4+2^k*(2*e.work+4)⟩

def rearrange (w k base : ℕ) (p : Fin H→ℕ) (a μ : Bits k) : Code w :=
  Code.seq (transfer w k base p a μ) H le_rfl

private theorem start (k base n : ℕ) : base≤bank k base n := Nat.le_add_right _ _

theorem transfer_bound (k base : ℕ) (i : Fin H) :
    bank k base i.val+2^k≤bank k base H := (bank_succ _ _ _).symm.le.trans (bank_mono _ _ i.isLt)

private theorem transfer_exec (base : ℕ) (p : Fin H→ℕ) (a μ : Bits k) (i : Fin H)
    (old : ∀i,p i+2^k≤base) (room : bank k base H<2^w) : (transfer w k base p a μ i).exec := by
  intro m labels registers slots machine
  have lt := (transfer_bound k base i).trans_lt room
  exact scan_exec _ _ _ m (PermutationRAM.fits a μ
    ⟨Nat.two_pow_pos _,by change 2^k < 2^w; omega,(old i).trans (start _ _ _)⟩) lt machine

theorem rearrange_exec (base : ℕ) (p : Fin H→ℕ) (a μ : Bits k)
    (old : ∀i,p i+2^k≤base) (room : bank k base H<2^w) : (rearrange w k base p a μ).exec :=
  Code.exec_seqAll _ (fun i=>transfer_exec base p a μ i old room) _ _

theorem rearrange_below (base : ℕ) (p : Fin H→ℕ) (a μ : Bits k) (m : Memory w) (z : ℕ)
    (before : z<base) : (rearrange w k base p a μ).after m z=m z :=
  Code.frame_seq _ z (fun i m=>ProtocolRAMGeneratedWrite.frame_image _ _ _ m z
    (Or.inl (before.trans_le (start k base i.val)))) m _ _

theorem rearrange_read (base : ℕ) (p : Fin H→ℕ) (a μ : Bits k) (m : Memory w)
    (weight : Fin H→Block k→ℕ) (old : ∀i,p i+2^k≤base) (room : bank k base H<2^w)
    (loads : ∀i (x : Block k),m (p i+x.val)=(weight i x:Word w))
    (i : Fin H) (x : Block k) : (rearrange w k base p a μ).after m (bank k base i.val+x.val)=
      (multiplierLoad weight a μ i x:Word w) := by
  let Init := fun M : Memory w=>∀i (x : Block k),M (p i+x.val)=(weight i x:Word w)
  let Claim := fun i : Fin H=>fun M : Memory w=>∀x : Block k,M (bank k base i.val+x.val)=
      (multiplierLoad weight a μ i x:Word w)
  have stable (j : Fin H) (M : Memory w) (ok : Init M) : Init ((transfer w k base p a μ j).after M) := by
    intro v x
    apply Eq.trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl ?_)) (ok v x)
    exact ((Nat.add_lt_add_left x.isLt _).trans_le (old v)).trans_le (start _ _ _)
  have now (j : Fin H) (M : Memory w) (ok : Init M) : Claim j ((transfer w k base p a μ j).after M) := by
    intro y
    have roomj := (transfer_bound k base j).trans_lt room
    have h := PermutationRAM.run (base:=p j) (out:=bank k base j.val) M a μ (weight j)
      ⟨Nat.two_pow_pos _,by change 2^k < 2^w; omega,(old j).trans (start _ _ _)⟩ roomj (ok j)
    exact h.2.2.1 y
  have preserve (i j : Fin H) (lt : i<j) (M : Memory w) (ok : Claim i M) :
      Claim i ((transfer w k base p a μ j).after M) := by
    intro y
    apply Eq.trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl ?_)) (ok y)
    have prior := (Nat.add_lt_add_left y.isLt (bank k base i.val))
    rw [←bank_succ] at prior
    exact prior.trans_le (bank_mono _ _ lt)
  exact (Code.read_seq _ Init stable Claim now preserve m loads H le_rfl).2 i i.isLt x

def scoreAt (H k base : ℕ) := PhysicalCensus.output H k (bank k base H)

def groupCode (w k base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap : ℕ) (a μ : Bits k) : Code w :=
  let q := bank k base H
  let mapped := fun v : Fin H=>bank k base v.val
  (rearrange w k base p a μ).thenDo
    ⟨PhysicalCensus.program w k q incoming mapped D cap,PhysicalCensus.after k q incoming mapped D cap,
      PhysicalCensus.ticks k q incoming mapped D cap⟩

theorem score_ge (H k base : ℕ) : bank k base H≤ scoreAt H k base := Nat.le_add_right _ _

theorem run (base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap : ℕ) (a μ : Bits k)
    (old : ∀i,p i+2^k≤base) (room : scoreAt H k base+1<2^w) :
    (groupCode w k base incoming p D cap a μ).exec :=
  Code.exec_seq (rearrange_exec _ _ _ _ old ((score_ge _ _ _).trans_lt (by omega)))
    (fun _=>PhysicalCensus.run _ _ _ _ _ _ (fun i=>transfer_bound _ _ i) room)

theorem below (base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap : ℕ) (a μ : Bits k)
    (m : Memory w) (z : ℕ) (earlier : z<base) :
    (groupCode w k base incoming p D cap a μ).after m z=m z := by
  have layer := earlier.trans_le (start k base H)
  have score := layer.trans_le (score_ge H k base)
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl score)).trans
    ((LayerRAM.below _ layer).trans (rearrange_below base p a μ m z earlier))

theorem published (base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap : ℕ) (a μ : Bits k)
    (m : Memory w) (weight : Fin H→Block k→ℕ) (old : ∀i,p i+2^k≤base)
    (room : scoreAt H k base+1<2^w) (bits : 2^k≤2^w) (cf : cap<2^w)
    (loads : ∀i (x : Block k),m (p i+x.val)=(weight i x:Word w))
    (sumRoom : ∀d<k,∀v x,(Scan.readWeights (multiplierLoad weight a μ) d v x).sum<2^w) :
    (groupCode w k base incoming p D cap a μ).after m (scoreAt H k base)=
      (Scan.leafScore incoming (multiplierLoad weight a μ) D cap:Word w) := by
  rw [← Scan.FinRows.score_eq_leafScore]
  exact PhysicalCensus.published _ _ _ _ _ _ _ (fun v=>transfer_bound _ _ v) room cf bits
    (rearrange_read base p a μ m weight old ((score_ge _ _ _).trans_lt (by omega)) loads) sumRoom

def stepBound (H k deg : ℕ) := (4+H*(4+2^k*(2*(10*2^k+10)+4)))+
      ((4+k*H*(4+2^k*(2*SplitRAM.workBound k deg+4)))+(4+1*(2*CensusRAM.workBound H k+4)))

theorem ticks_le (base : ℕ) (incoming : Fin H→List (Fin H)) (p : Fin H→ℕ) (D cap deg : ℕ)
    (a μ : Bits k) (degree : ∀i,(incoming i).length≤deg) :
    (groupCode w k base incoming p D cap a μ).ticks≤ stepBound H k deg := by
  apply Nat.add_le_add _ (PhysicalCensus.ticks_le _ _ _ _ _ deg degree)
  apply Code.clock_seq
  intro i
  simp [transfer,PermutationRAM.work]

end Hierarchy.DescentColonies.SiteRAM

end
end OAI
