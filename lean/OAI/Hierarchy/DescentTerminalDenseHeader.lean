import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentTerminalDenseCableFetch

namespace OAI
/-! # Shared header table for the actual clipped lengths in one terminal port row -/

namespace Hierarchy.DescentTerminalDenseHeader
open DescentTerminalDenseWindow ProtocolRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section

abbrev Profile (q p : ℕ) := Fin q → Fin (p+1)
def encode (q p : ℕ) : Profile q p ≃ Fin (profiles q p) := finFunctionFinEquiv

def slotPrefix {q p : ℕ} (a : Profile q p) (j : ℕ) := pref (fun s=>(a s).val) j
def mass {q p : ℕ} (a : Profile q p) := slotPrefix a q

theorem prefix_le {q p : ℕ} (a : Profile q p) (j : ℕ) : slotPrefix a j ≤ j*p := by
  simpa [slotPrefix,pref] using delta (fun s=>(a s).val) (fun s=>Nat.le_of_lt_succ (a s).isLt) 0 j

theorem mass_le {q p : ℕ} (a : Profile q p) : mass a ≤ q*p := prefix_le a q

def rowProfile {n q p : ℕ} (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (r : ℕ) : Profile q p :=
  fun s=>⟨lengthAt len (r*q+s.val),by
    unfold lengthAt
    split <;> first | exact Nat.lt_succ_of_le (small _) | omega⟩

theorem prefix_row {n q p : ℕ} (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (r j : ℕ) (bound : j ≤ q) :
    pref len (r*q+j)=pref len (r*q)+slotPrefix (rowProfile (q:=q) len small r) j := by
  induction j with
  | zero => simp [slotPrefix,pref]
  | succ j ih =>
    have prev:=ih (by omega)
    rw [Nat.add_succ,pref,prev]
    simp [slotPrefix,pref,lengthAt,show j<q by omega,rowProfile,Nat.add_assoc]

theorem mass_row {n q p : ℕ} (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (r : ℕ) :
    pref len ((r+1)*q)=pref len (r*q)+mass (rowProfile (q:=q) len small r) := by
  simpa [Nat.succ_mul,mass] using prefix_row len small r q (le_refl q)

def control {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) : Format q p :=
  fun s=>(⟨rem.val+slotPrefix a s.val,by
    have less:=rem.isLt
    have h:=(prefix_le a s.val).trans (Nat.mul_le_mul_right p (Nat.le_of_lt s.isLt))
    omega⟩,a s)

theorem control_row {n q p : ℕ} (len : Fin n→ℕ) (small : ∀i,len i ≤ p) (pos : 0<q*p) (base r : ℕ) :
    control (rowProfile (q:=q) len small r) ⟨(first len q base r)%(q*p),Nat.mod_lt _ pos⟩=
      format len pos small base r := by
  funext s
  apply Prod.ext
  · apply Fin.ext
    simp [control,format,DescentTerminalDenseWindow.begin,first,prefix_row len small r s.val s.isLt.le]
    omega
  · rfl

def priorBits {q p k : ℕ} (widths : Fin k→Profile q p) (i : ℕ) :=
  pref (fun s=>mass (widths s)) i

theorem prior_zero {q p k : ℕ} (widths : Fin k→Profile q p) : priorBits widths 0=0 := rfl
theorem prior_next {q p k : ℕ} (widths : Fin k→Profile q p) (i : Fin k) :
    priorBits widths (i.val+1)=priorBits widths i.val+mass (widths i) := by
  simp [priorBits,pref,lengthAt,i.isLt]

/-- This transition only touches the current short residue. The total bit
count can exceed the machine address range. -/
def residue {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) := (rem.val+mass a)%(q*p)
def carry {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) := (rem.val+mass a)/(q*p)

theorem carry_le {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) : carry a rem ≤ 1 := by
  have b:=mass_le a
  have h:=rem.isLt
  have pos : 0<q*p := by omega
  have small : rem.val+mass a<2*(q*p) := by omega
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pos).mpr small)

theorem residue_step {q p : ℕ} (pos : 0<q*p) (u : ℕ) (a : Profile q p) :
    residue a ⟨u%(q*p),Nat.mod_lt _ pos⟩=(u+mass a)%(q*p) := by
  simp [residue,Nat.mod_add_mod]

theorem quotient_step {q p : ℕ} (pos : 0<q*p) (u : ℕ) (a : Profile q p) :
    u/(q*p)+carry a ⟨u%(q*p),Nat.mod_lt _ pos⟩=(u+mass a)/(q*p) := by
  have eqn:=Nat.div_add_mod u (q*p)
  change u/(q*p)+(u%(q*p)+mass a)/(q*p)=(u+mass a)/(q*p)
  conv_rhs => rw [←eqn]
  rw [Nat.add_assoc,Nat.mul_add_div pos]

def key {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) : Fin (profiles q p*(q*p)) :=
  finProdFinEquiv (encode q p a,rem)

theorem key_val {q p : ℕ} (a : Profile q p) (rem : Fin (q*p)) :
    (key a rem).val=(encode q p a).val*(q*p)+rem.val := by change rem.val+q*p*(encode q p a).val=_;ac_rfl

/-- The four shared columns are the ordinal-to-row offset, next residue,
single-bit carry, and the actual finite format code. -/
def offsets (bits q p : ℕ) : Vector (Computability.VPVNP.BurstRAM.Word bits) (profiles q p) :=
  Vector.ofFn fun a=>((a.val*(q*p):ℕ):Computability.VPVNP.BurstRAM.Word bits)

def table {q p : ℕ} (bits : ℕ) (f : Profile q p→Fin (q*p)→ℕ) :
    Vector (Computability.VPVNP.BurstRAM.Word bits) (profiles q p*(q*p)) :=
  Vector.ofFn fun i=>
    let pair:=finProdFinEquiv.symm i
    (f ((encode q p).symm pair.1) pair.2 : Computability.VPVNP.BurstRAM.Word bits)

theorem table_key {q p : ℕ} (bits : ℕ) (f : Profile q p→Fin (q*p)→ℕ) (a : Profile q p) (rem : Fin (q*p)) :
    (table bits f)[(key a rem).val]=(f a rem : Computability.VPVNP.BurstRAM.Word bits) := by
  simp only [table,Vector.getElem_ofFn,key,Fin.eta,Equiv.symm_apply_apply]

theorem table_room {q p bits : ℕ} (pos : 0<q*p) (room : formatBits q p+2*(q*p) ≤ bits/2) :
    profiles q p+3*(profiles q p*(q*p)) ≤ 4*2^(bits/2) := by
  have pr : profiles q p ≤ 2^(q*Nat.clog 2 (p+1)) := by
    rw [Nat.mul_comm q,pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
  have b : q*p ≤ 2^(q*p) := Nat.le_of_lt (Nat.lt_two_pow_self)
  have bitsUsed : q*Nat.clog 2 (p+1)+q*p ≤ bits/2 := by
    dsimp [formatBits] at room
    rw [Nat.mul_add] at room
    omega
  have lim := (Nat.mul_le_mul pr b).trans (show 2^(q*Nat.clog 2 (p+1))*2^(q*p) ≤ 2^(bits/2) by
    rw [←pow_add];exact Nat.pow_le_pow_right (by decide) bitsUsed)
  have one : profiles q p ≤ profiles q p*(q*p) := Nat.le_mul_of_pos_right _ pos
  omega

end
end Hierarchy.DescentTerminalDenseHeader

end OAI
