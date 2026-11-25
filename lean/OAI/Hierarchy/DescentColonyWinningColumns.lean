import OAI.Hierarchy.DescentColonyRetainedBanks
import OAI.Hierarchy.DescentColonySelectionRAM
import OAI.Hierarchy.DescentGLPermutationRAM

namespace OAI
/-! # Selecting the winning split rows and pulling genuine outgoing amounts -/

noncomputable section
namespace Hierarchy.DescentColonies.WinningColumns
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open DescentGL (Bits Nonzero)
open scoped Fin.CommRing

variable {w k H G : ℕ}

def winnerPtr (G H k base : ℕ) := AllSeedsRAM.winningBase G H k base+(2^k-1-1)

def header (p : ℕ) : Expr := .lookup ⟨p,0⟩ (.lit 0)

def select (p : ℕ) (row : Fin (2^k-1)→Expr) := chooseField (2^k-1) 1 row (header p)

theorem select_eval (p : ℕ) (row : Fin (2^k-1)→Expr) (m : Memory w) (r : Word w)
    (bits : 2^k≤2^w) (μ : Nonzero k) (found : m p=(MultiplierMinimumRAM.key μ:Word w)) :
    ∃ i : Fin (2^k-1),seedAt k i=μ ∧ (select p row).eval m r=(row i).eval m r := by
  obtain ⟨i,chosen⟩ := List.mem_ofFn.mp (show μ∈List.ofFn (seedAt k) from mem_nonzeroWords μ)
  subst μ
  refine ⟨i,rfl,eval_chooseField _ _ _ _ _ _ _ (by have := Nat.two_pow_pos k;omega) ?_⟩
  have fits : MultiplierMinimumRAM.key (seedAt k i)<2^w :=
    (seedCode (seedAt k i).val).isLt.trans_le bits
  calc
    ((header p).eval m r).val = (m p).val := by simp [header,Expr.eval,Bank.read,Bank.size]
    _ = MultiplierMinimumRAM.key (seedAt k i) := by rw [found,Fin.val_cast_of_lt fits]
    _ = 1+i.val := (seedAt_code i).trans (Nat.add_comm i.val 1)

theorem select_fits (p out : ℕ) (row : Fin (2^k-1)→Expr) (wide : 1<2^w) (hp : p<out)
    (inputs : ∀i,(row i).Fits w out) : (select p row).Fits w out :=
  DescentGLPermutationRAM.fits_choose _ _ _ _ ⟨⟨Nat.two_pow_pos _,wide,hp⟩,trivial⟩ inputs

theorem select_work (p : ℕ) (row : Fin (2^k-1)→Expr) (c : ℕ) (h : ∀i,(row i).work=c) :
    (select p row).work=1+(2^k-1)*(c+8) := by
  rw [select,DescentGLPermutationRAM.work_choose _ _ _ _ c h]
  simp only [header,Expr.work]
  ring

def column (base : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :=
  select (winnerPtr G H k base) fun i=>.lookup ⟨AllSeedsRAM.retainedBank base i g v layer,k⟩ .row

def outgoing (G H k base raw : ℕ) (a : Bits k) :=
  select (winnerPtr G H k base) fun i=>PermutationRAM.expr raw a (seedAt k i).val

theorem column_eval (base : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) (m : Memory w)
    (income : Fin H→List (Fin H)) (weight : Fin H→Block k→ℕ) (D cap : ℕ) (a : Bits k)
    (bits : 2^k≤2^w) (μ : Nonzero k) (found : m (winnerPtr G H k base)=(MultiplierMinimumRAM.key μ:Word w))
    (retained : ∀i (x : Block k),m (AllSeedsRAM.retainedBank base i g v layer+x.val)=
      (SiteRAM.retainedValue income (multiplierLoad weight a (seedAt k i).val) D cap layer v x:Word w))
    (x : Block k) :
    (column base g v layer).eval m (x.val:Word w)=
      (SiteRAM.retainedValue income (multiplierLoad weight a μ.val) D cap layer v x:Word w) := by
  obtain ⟨i,rfl,eqn⟩ := select_eval _ (fun i=>Expr.lookup ⟨AllSeedsRAM.retainedBank base i g v layer,k⟩ .row)
    m (x.val:Word w) bits μ found
  apply eqn.trans
  simpa [Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (x.isLt.trans_le bits),Nat.mod_eq_of_lt x.isLt] using retained i x

theorem outgoing_eval (G H base raw : ℕ) (a : Bits k) (m : Memory w) (amount : Block k→ℕ)
    (bits : 2^k<2^w) (μ : Nonzero k) (found : m (winnerPtr G H k base)=(MultiplierMinimumRAM.key μ:Word w))
    (loads : ∀ x : Block k,m (raw+x.val)=(amount x:Word w)) (x : Block k) :
    (outgoing G H k base raw a).eval m (x.val:Word w)=
      (multiplierLoad (fun _ : Unit=>amount) a μ.val () x:Word w) := by
  obtain ⟨i,rfl,eqn⟩ := select_eval _ (fun i=>PermutationRAM.expr raw a (seedAt k i).val) m (x.val:Word w) bits.le μ found
  exact eqn.trans (by rw [←bufferedLoad_eq];exact PermutationRAM.eval m _ _ _ bits loads x)

theorem column_work (base : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) :
    (column base g v layer).work=1+(2^k-1)*15 := select_work _ _ 7 (fun _=>rfl)

theorem outgoing_work (G H base raw : ℕ) (a : Bits k) :
    (outgoing G H k base raw a).work=1+(2^k-1)*(10*2^k+18) := by
  simpa [outgoing,Nat.add_assoc] using select_work (winnerPtr G H k base)
    (fun i=>PermutationRAM.expr raw a (seedAt k i).val) _ (fun _=>PermutationRAM.work ..)

theorem column_fits (base out : ℕ) (g : Fin G) (v : Fin H) (layer : Option (Fin k)) (bits : 2^k<2^w)
    (hp : winnerPtr G H k base<out) (old : ∀i,AllSeedsRAM.retainedBank base i g v layer+2^k≤out) :
    (column base g v layer).Fits w out := by
  apply select_fits _ _ _ (by have := Nat.two_pow_pos k;omega) hp
  intro i
  exact ⟨⟨Nat.two_pow_pos _,bits,old i⟩,trivial⟩

theorem outgoing_fits (G H base raw out : ℕ) (a : Bits k) (bits : 2^k<2^w)
    (hp : winnerPtr G H k base<out) (old : raw+2^k≤out) : (outgoing G H k base raw a).Fits w out :=
  select_fits _ _ _ (by have := Nat.two_pow_pos k;omega) hp (fun _=>PermutationRAM.fits _ _ ⟨Nat.two_pow_pos _,bits,old⟩)

/-- A single native column pass, including its output words and actual operation count. -/
theorem publish (dest : ℕ) (e : Expr) (m : Memory w) (safe : e.Fits w dest) (room : dest+2^k<2^w)
    (expected : Block k→Word w) (computed : ∀x : Block k,e.eval m (x.val:Word w)=expected x) :
    (scan w dest (2^k) e).Exec m (ProtocolRAM.image dest (2^k) e m) (4+2^k*(2*e.work+4)) ∧
      (∀x : Block k,ProtocolRAM.image dest (2^k) e m (dest+x.val)=expected x) ∧
      ∀z<dest,ProtocolRAM.image dest (2^k) e m z=m z :=
  ⟨scan_exec _ _ _ _ safe room,fun x=>(ProtocolRAMGeneratedWrite.read_image _ _ _ _ x).trans (computed x),
    fun _ h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl h)⟩

end Hierarchy.DescentColonies.WinningColumns

end
end OAI
