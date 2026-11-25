import OAI.Hierarchy.DescentResetFieldShuffle
import OAI.Hierarchy.DescentResetStencilReaders

namespace OAI
/-! # Reading the high-group-independent original coordinate planes in the reset -/
namespace Hierarchy.DescentGLPacked.BankImage.Original
open DescentGLPacked DescentColonies DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPlainTerminal DescentPlainTerminal.Suffix
open scoped Classical Fin.CommRing
noncomputable section
variable {H h l b w : ℕ}

def bit (pos : 0<b) (d : Fin (h+l)) (x : Block (h+l)) : Cell b :=
  ⟨(x.val.testBit d.val).toNat,(Bool.toNat_le _).trans_lt (Nat.one_lt_two_pow (by omega))⟩

def packed (pos : 0<b) (d : Fin (h+l)) (j : Fin (2^h)) : ℕ :=
  (data (fun (_:Fin 1) x=>bit pos d x) ((0:Fin 1),Fin.cast (chunk_count h l).symm j)).val

def bank (base h : ℕ) (d : Fin (h+l)) : Bank := ⟨base+d.val*2^h,h⟩

/-- One fixed copy of each original-coordinate plane is shared by every old host. -/
def image (base : ℕ) (pos : 0<b) (m : Memory w) : Memory w := fun z=>
  if kept : base≤z ∧ z<base+(h+l)*2^h then
    let i : Fin ((h+l)*2^h):=⟨z-base,by omega⟩
    let p : Fin (h+l) × Fin (2^h):=finProdFinEquiv.symm i
    ((packed pos p.1 p.2:ℕ):Word w)
  else m z

theorem resident (base : ℕ) (pos : 0<b) (m : Memory w) (d : Fin (h+l)) (j : Fin (2^h)) :
    image (h:=h) (l:=l) base pos m ((bank base h d).base+j.val)=(packed pos d j:Word w) := by
  have idx : (finProdFinEquiv (d,j)).val=d.val*2^h+j.val := by
    change j.val+2^h*d.val=_;ring
  have bounded:=(finProdFinEquiv (d,j)).isLt
  rw [idx] at bounded
  have ok : base≤(bank base h d).base+j.val ∧ (bank base h d).base+j.val<base+(h+l)*2^h := by
    change base≤base+d.val*2^h+j.val ∧ _;dsimp only [bank];omega
  simp only [image,dite_eq_left ok]
  have same : (⟨(bank base h d).base+j.val-base,by dsimp only [bank];omega⟩:Fin ((h+l)*2^h))=
      finProdFinEquiv (d,j) := by apply Fin.ext;rw [idx];dsimp [bank];omega
  rw [same,Equiv.symm_apply_apply]

theorem source (base : ℕ) (pos : 0<b) (d : Fin (h+l)) (m : Memory w)
    (rows : H*2^h≤2^w)
    (reads : ∀j : Fin (2^h),m ((bank base h d).base+j.val)=(packed pos d j:Word w)) :
    DescentPackedZip.Source (.lookup (bank base h d) .row)
      (fun (_:Fin H) x=>bit pos d x) (2^l) m := by
  rintro ⟨v,y⟩
  let j:=Fin.cast (chunk_count h l) y
  have bound := lt_of_lt_of_eq (row H (2^(h+l)) (2^l) (v,y)).isLt
    (congrArg (H * ·) (chunk_count h l))
  change m ((bank base h d).base+((row H _ _ (v,y)).val:Word w).val%(bank base h d).size)=_
  rw [Fin.val_cast_of_lt (bound.trans_le rows)]
  have atRow : (row H _ _ (v,y)).val=y.val+chunks (2^(h+l)) (2^l)*v.val := rfl
  have small := lt_of_lt_of_eq y.isLt (chunk_count h l)
  have offset : (row H _ _ (v,y)).val % (bank base h d).size = j.val := by
    rw [atRow]
    change (y.val+chunks (2^(h+l)) (2^l)*v.val) % (2^h) = y.val
    rw [show chunks (2^(h+l)) (2^l)*v.val = 2^h*v.val from
      congrArg (· * v.val) (chunk_count h l), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small]
  rw [offset]
  exact reads j

/-- After the common measured GL sweep, read its short numeric bits in the
binary panel used by the old-order comparison. -/
def narrow (b r : ℕ) (z : Cell (b*2^r)) : Cell (2^r) :=
  PackedOrder.planeCode r (fun x=>finTwoEquiv.symm (decide (0<((encode b (2^r)).symm z x).val)))

theorem narrow_zero (b r : ℕ) : narrow b r 0=0 := by
  simp only [narrow,Readers.zeroDigits,Fin.val_zero,Nat.lt_irrefl,decide_false]
  apply Fin.ext
  simp [PackedOrder.planeCode,encode]; rfl

theorem narrow_original {c : ℕ} (short : c≤h+l) (pos : 0<b) (L : DescentGL.Layout (h+l))
    (j : Block c) (d : Fin (h+l)) :
    narrow b (h+l-c) (encode b (2^(h+l-c))
      (fun x=>bit pos d ((rearrange L).symm (DescentIssuedFallbackPanel.join short j x))))=PackedOrder.panel short L j d := by
  apply congrArg (PackedOrder.planeCode (h+l-c))
  change (fun x=>finTwoEquiv.symm (decide (0<((encode b (2^(h+l-c))).symm _ x).val)))=_
  funext x
  simp only [Equiv.symm_apply_apply]
  have positive (flag : Bool) : decide (0 < flag.toNat) = flag := by cases flag <;> rfl
  exact congrArg finTwoEquiv.symm (positive _)

theorem panel_source {c M : ℕ} (short : c≤h+l) (pos : 0<b) (L : DescentGL.Layout (h+l))
    (d : Fin (h+l)) (op : Expr) (rom : Bank) (out : ℕ) (m : Memory w)
    (fit : rom.Fits w out) (pitch : rom.bits=(b*2^(h+l-c))*M)
    (static : ∀z : Cell ((b*2^(h+l-c))*M),
       m (rom.base+z.val)=((DescentSIMDLookup.table (narrow b (h+l-c)) z).val:Word w))
    (read : DescentPackedZip.Source op (fun (_:Fin H) j=>encode b (2^(h+l-c))
       (fun x=>bit pos d ((rearrange L).symm (DescentIssuedFallbackPanel.join short j x)))) M m) :
    DescentPackedZip.Source (PackedOrder.projected rom op) (fun (_:Fin H) j=>PackedOrder.panel short L j d) M m := by
  simpa only [narrow_original short pos L] using
    (PackedOrder.project rom op out (narrow b (h+l-c)) (narrow_zero ..) m _ fit pitch static read)

end
end Hierarchy.DescentGLPacked.BankImage.Original

end OAI
