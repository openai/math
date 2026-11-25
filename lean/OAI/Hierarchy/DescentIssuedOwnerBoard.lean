import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentMaskedLookupBook
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # The resolved old actor venue array from the actual chosen register expression -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners.Board
open DescentSIMDLookup DescentSixParty.PackedCensus ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {r D p d H G M w : ℕ}
def bank (base n : ℕ) : Bank := ⟨base,Nat.clog 2 n⟩
def rom (base n : ℕ) := base+(bank base n).size
def venue (a M base n : ℕ) := rom base n + 2^(a*M) + (bank base n).size

def issue (B profile base : ℕ) (e : Expr) (H G M w r D p d : ℕ) :=
  ((scan w base (H*chunks G M) e).seq (Book.install (render r D p d B profile) H G M w (rom base (H*chunks G M)))).seq
    (DescentSIMDLookup.program (Book.banks (rom base (H*chunks G M)) (inputBits r D p d) H G M (bank base (H*chunks G M)))
      (venue (inputBits r D p d) M base (H*chunks G M)) H G M w)

def issued (B profile base : ℕ) (e : Expr) (H G M r D p d : ℕ) (m : Memory w) :=
  image (venue (inputBits r D p d) M base (H*chunks G M)) (H*chunks G M)
    (DescentSIMDLookup.lookup (Book.banks (rom base (H*chunks G M)) (inputBits r D p d) H G M (bank base (H*chunks G M))))
    (Book.image (render r D p d B profile) H G M (rom base (H*chunks G M)) (image base (H*chunks G M) e m))

def ticks (a H G M : ℕ) (e : Expr) :=
  (4+H*chunks G M*(2*e.work+4))+(4+10*Book.words a H G M)+(4+44*(H*chunks G M))

variable (B profile base : ℕ)
local notation "a" => inputBits r D p d
local notation "b" => (digits r D d*3)*r
local notation "n" => H*chunks G M
local notation "layout" => Book.banks (rom base n) a H G M (bank base n)
local notation "f" => render r D p d B profile

theorem run (e : Expr) (u : Fin H→Fin G→Panel r D p d) (l : Bool) (m : Memory w)
    (fixed : e.Fits w base) (small : M*max a b≤w/2) (total : venue a M base n+n<2^w)
    (read : DescentPackedZip.Source e (fun h g=>register l (u h g)) M m) :
    let out:=issued B profile base e H G M r D p d m
    (issue B profile base e H G M w r D p d).Exec m out (ticks a H G M e) ∧
      (∀x : Row H G M,out (venue a M base n+(row H G M x).val)=
        ((data (fun h g=>f (register l (u h g))) x).val:Word w)) ∧
      (∀j,j<base ∨ venue a M base n+n≤j → out j=m j) ∧ CheapCode (issue B profile base e H G M w r D p d) := by
  intro out
  let old:=image base n e m
  let mid:=Book.image f H G M (rom base n) old
  let y:=venue a M base n
  have pad : n≤(bank base n).size:=Nat.le_pow_clog (by decide) _
  have legal : rom base n + Book.words a H G M ≤ y := by
    change rom base n + (2^(a*M) + n) ≤ (rom base n + 2^(a*M)) + (bank base n).size
    simpa only [Nat.add_assoc] using Nat.add_le_add_left (Nat.add_le_add_left pad (2^(a*M))) (rom base n)
  have order : base+n≤rom base n:=Nat.add_le_add_left pad base
  have start : rom base n≤y := (Nat.le_add_right ..).trans legal
  have lim:y<2^w:=(Nat.le_add_right ..).trans_lt total
  obtain ⟨put,words,kept,code⟩:=Book.mount f H G M (rom base n) (bank base n) old (legal.trans_lt lim)
  have mk (src : Bank) (bound : src.base+src.size≤y) : src.Fits w y :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt lim),bound⟩
  have geometry : Fits layout a b M H G w y := by
    refine ⟨mk _ start,mk _ ?_,mk _ le_rfl,pad,rfl,pad,total,small⟩
    change rom base n + 2^(a*M) ≤ (rom base n + 2^(a*M)) + (bank base n).size
    exact Nat.le_add_right _ _
  let active:=fun h g=>register l (u h g)
  have pins : PinFrame (M:=M) layout f active mid := by
    refine ⟨fun i bit=>congrArg (fun q=>Computability.VPVNP.RAMSerialization.wordBits w q bit) (words i),?_⟩
    intro i
    exact (kept _ (.inl ((Nat.add_lt_add_left (row H G M i).isLt base).trans_le order))).trans
      ((ProtocolRAMGeneratedWrite.read_image base n e m (row H G M i)).trans (read i))
  have finalWork : 4+n*(2*(DescentSIMDLookup.lookup layout).work+4) = 4+44*n := by
    rw [lookup_work, show 2*20+4=44 by decide, Nat.mul_comm n 44]
  have finalScan : (DescentSIMDLookup.program layout y H G M w).Exec mid out (4+44*n) := by
    rw [← finalWork]
    exact scan_exec y n (DescentSIMDLookup.lookup layout) mid
      (by simp [DescentSIMDLookup.lookup,Expr.Fits,geometry.source,geometry.mask,geometry.dictionary]) total
  refine ⟨?_, col_read layout y geometry f active mid pins, ?_,
    cheap_seq (cheap_seq (scan_cheap w base n e) code) (scan_cheap w y n (DescentSIMDLookup.lookup layout))⟩
  · intro P R K machine pc reg pub exit installed advice cfg mem enter same
    exact Procedure.Exec.then (Procedure.Exec.then
      (scan_exec base n e m fixed (order.trans_lt (start.trans_lt lim))) put) finalScan
      machine pc reg pub exit installed advice cfg mem enter same
  · intro j outside
    change j < base ∨ y+n ≤ j at outside
    have base_before : base ≤ rom base n := (Nat.le_add_right base n).trans order
    have q : j < y ∨ y+n ≤ j := outside.imp (fun h => h.trans_le (base_before.trans start)) id
    have t : j < rom base n ∨ rom base n+Book.words a H G M ≤ j :=
      outside.imp (fun h => h.trans_le base_before) (fun h => legal.trans ((Nat.le_add_right y n).trans h))
    have s : j < base ∨ base+n ≤ j :=
      outside.imp id (fun h => order.trans (start.trans ((Nat.le_add_right y n).trans h)))
    exact (ProtocolRAMGeneratedWrite.frame_image y n (DescentSIMDLookup.lookup layout) mid j q).trans
      ((kept j t).trans (ProtocolRAMGeneratedWrite.frame_image base n e m j s))

end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners.Board

end OAI
