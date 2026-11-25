import OAI.Hierarchy.DescentPackedColonyRun
import OAI.Computability.VPVNP.RAMSerialization

namespace OAI
/-! # Concrete public ROMs and the packed bit tariff for one split trial -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a b c H G k M Δ w : ℕ}

def tablesAt (lo a b M : ℕ) : DescentPackedZip.Tables :=
  ⟨⟨lo,a*M⟩,⟨lo+2^(a*M),(a+b)*M⟩⟩

def tableEnd (lo a b M : ℕ) := lo+2^(a*M)+2^((a+b)*M)

/-- An incorrect selector cannot alter any word in either table. -/
def install (lo M : ℕ) (f : Cell a→Cell b→Cell c) (m : Memory w) (x : ℕ) : Word w :=
  if h : lo≤x ∧ x<lo+2^(a*M) then ((2^(b*M)*(x-lo):ℕ):Word w)
  else if h : lo+2^(a*M)≤x ∧ x<tableEnd lo a b M then
    ((DescentPackedZip.table (M:=M) f ⟨x-(lo+2^(a*M)),by unfold tableEnd at h;omega⟩).val:ℕ)
  else m x

theorem install_read (lo M : ℕ) (f : Cell a→Cell b→Cell c) (m : Memory w) :
    DescentPackedZip.Static (tablesAt lo a b M) f M (install lo M f m) := by
  constructor
  · intro i
    have live : lo≤lo+i.val ∧ lo+i.val<lo+2^(a*M) := by have:=i.isLt;omega
    simp [tablesAt,install,live]
  · intro i
    have live : lo+2^(a*M)≤lo+2^(a*M)+i.val ∧ lo+2^(a*M)+i.val<tableEnd lo a b M := by
      have:=i.isLt;unfold tableEnd;omega
    have gone : ¬(lo≤lo+2^(a*M)+i.val ∧ lo+2^(a*M)+i.val<lo+2^(a*M)) := by omega
    simp [tablesAt,install,live]

theorem install_frame (lo M : ℕ) (f : Cell a→Cell b→Cell c) (m : Memory w) {x : ℕ}
    (out : x<lo ∨ tableEnd lo a b M≤x) : install lo M f m x=m x := by
  have mid : lo≤lo+2^(a*M) := Nat.le_add_right ..
  have finalPage : lo+2^(a*M)≤tableEnd lo a b M := Nat.le_add_right ..
  have shift : ¬(lo≤x ∧ x<lo+2^(a*M)) := by
    rintro ⟨first,last⟩
    exact out.elim (fun h=>h.not_ge first) (fun h=>last.not_ge (finalPage.trans h))
  have applyPage : ¬(lo+2^(a*M)≤x ∧ x<tableEnd lo a b M) := by
    rintro ⟨first,last⟩
    exact out.elim (fun h=>h.not_ge (mid.trans first)) (fun h=>last.not_ge h)
  simp [install,shift,applyPage]

theorem tables_fit (lo out : ℕ) (endAt : tableEnd lo a b M≤out) (room : out<2^w) :
    WordRoom (tablesAt lo a b M) a b M w out := by
  have shiftEnd : lo+2^(a*M)≤out := (Nat.le_add_right _ _).trans endAt
  have shiftSize : 2^(a*M)≤out := (Nat.le_add_left _ _).trans shiftEnd
  have applySize : 2^((a+b)*M)≤out := (Nat.le_add_left _ _).trans endAt
  exact ⟨⟨Nat.two_pow_pos _,shiftSize.trans_lt room,shiftEnd⟩,
    ⟨Nat.two_pow_pos _,applySize.trans_lt room,endAt⟩,rfl,rfl⟩

/-- Static addresses and strides use one entry per packed row or one entry per
physical neighbor. The roster itself is the retained native pre-stage roster. -/
def idWord (p : Row H G M) (i : Fin Δ) := p.1.val*Δ+i.val
def offsetWord (v : Fin H) (G M : ℕ) := chunks G M*v.val
def chunkWord (p : Row H G M) := p.2.val

def emptyWord (p : Row H G M) (k : ℕ) :=
  (data (fun _ : Fin H=>fun _ : Fin G=>flags (fun _ : Fin k=>fun _ : Block k=>false)) p).val

theorem empty_rows (k : ℕ) (B : Bank) (m : Memory w)
    (atRow : ∀ p : Row H G M,m (B.base+(row H G M p).val)=(emptyWord p k:Word w))
    (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a μ : Bits k) :
    Reads B (stateAt rs W D cap a μ 0) M m := atRow

def unit (k b : ℕ) := max (width k+width k) (width k+b*2^k)

theorem bit_price (L : Layout Δ) (H G k b w : ℕ) (wide : 2*unit k b≤w) :
    let M:=lanes w (unit k b)
    clock (passes L H G M k)*w≤(4+4*k)*w+
      k*(2*(25+56*Δ)+4)*(H*w+4*H*G*unit k b) := by
  dsimp only
  have positive : 0<unit k b := Nat.lt_of_lt_of_le (by unfold width;omega) (le_max_left _ _)
  have total:=Nat.mul_le_mul_right w (clock_price L H G (lanes w (unit k b)) k)
  have words:=Nat.mul_le_mul_left (k*(2*(25+56*Δ)+4)) (volume H G w (unit k b) positive wide)
  nlinarith only [total,words]

theorem tables_size (k b w : ℕ) :
    let M:=lanes w (unit k b)
    (2^(width k*M)+2^((width k+b*2^k)*M))+
      (2^(width k*M)+2^((width k+width k)*M))≤4*2^(w/2) := by
  dsimp only
  let M:=lanes w (unit k b)
  have scale (t : ℕ) (small : t≤unit k b) : 2^(t*M)≤2^(w/2) := by
    apply Nat.pow_le_pow_right (by decide)
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left M small).trans (lanes_fit w _)
  have max1 : width k + width k≤unit k b:=le_max_left ..
  have max2 : width k+b*2^k≤unit k b:=le_max_right ..
  have one:=scale _ ((Nat.le_add_right _ _).trans max1)
  have two:=scale _ max1
  have three:=scale _ max2
  dsimp only [M] at one two three
  omega

end
end Hierarchy.DescentPackedColony

end OAI
