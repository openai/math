import OAI.Hierarchy.DescentResetHaloBroadcast
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Original public and private reset digits from the measured compact receiver -/
namespace Hierarchy.DescentResetOriginalZeroHalo
open DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def rows (H G M : ℕ) := H*chunks G M
def pageSize (M b : ℕ) := (M+1)*2^b
def count (H G M b : ℕ) := 3*rows H G M + 3*pageSize M b
def bits (H G M b : ℕ) := Nat.clog 2 (count H G M b+1)
def endAddress (base H G M b : ℕ) :=
  base+3*rows H G M+2*pageSize M b+2^(bits H G M b)

def bank (base H G M b offset : ℕ) : Bank := ⟨base+offset,bits H G M b⟩

def zero (base H G M b x : ℕ) : Expr :=
  if x=0 then .lookup (bank base H G M b (2*rows H G M)) .row else .lit 0

def field (base H G M b : ℕ) (k : Fin 3) (src : Bank) : Expr :=
  let book := bank base H G M b
  .lookup (book (3*rows H G M+k.val*pageSize M b))
    (.op .add (.lookup (book (rows H G M)) .row) (.lookup src (.lookup (book 0) .row)))

def self (base H G M b : ℕ) := field base H G M b 0
def shape (base H G M b : ℕ) := field base H G M b 1
def halo (base H G M b : ℕ) := field base H G M b 2

def outputBits (short haloBits k : ℕ) := if k=2 then haloBits else short
def decoded (D k n : ℕ) := if k=1 then n / (2^Nat.clog 2 (D+2)) else n-1

/-- The last three tables repack the actual old self code or actual joint code. The
second row directory restricts each result to the live lanes of its group chunk. -/
def literal (H G M b z short haloBits D i : ℕ) : ℕ :=
  let N := rows H G M
  let U := pageSize M b
  if h:i<N then ((row H G M).symm ⟨i,h⟩).1.val
  else if h:i-N<N then used G M ((row H G M).symm ⟨i-N,h⟩).2.val*2^b
  else if h:i-2*N<N then
    (data (fun (_ : Fin H) (g : Fin G) => ((decide (g.val=0)).toNat : Cell z))
      ((row H G M).symm ⟨i-2*N,h⟩)).val
  else
    let r := i-3*N
    let k := r/U
    let j := r%U
    DescentResetHaloBroadcast.point (outputBits short haloBits k) M (j/2^b) (decoded D k (j%2^b))

def phase (w base H G M b z short haloBits D : ℕ) : NativePhase w :=
  let f := literal H G M b z short haloBits D
  let n := count H G M b
  ⟨DescentStaticWordColumn.program w base f n,4+10*n,fun m=>DescentStaticWordColumn.image base f m n,
    DescentStaticWordColumn.cheap w base f n⟩

theorem written_le (base H G M b : ℕ) : base+count H G M b ≤ endAddress base H G M b := by
  have enough : count H G M b+1 ≤ 2^bits H G M b := Nat.le_pow_clog (by decide) _
  unfold endAddress count at *
  omega

theorem any {w : ℕ} (base H G M b z short haloBits D : ℕ) (m : Memory w)
    (room : endAddress base H G M b < 2^w) :
    let pgm := phase w base H G M b z short haloBits D
    pgm.Runs m ∧ ∀a,a<base ∨ endAddress base H G M b ≤ a → pgm.image m a=m a := by
  intro pgm
  have le := written_le base H G M b
  let data := literal H G M b z short haloBits D
  exact ⟨DescentStaticWordColumn.mount base (count H G M b) data m (le.trans_lt room),fun a outside=>
    DescentStaticWordColumn.frame base (count H G M b) data m a (outside.imp_right le.trans)⟩

theorem bank_fit {w : ℕ} (base H G M b offset : ℕ)
    (within : offset ≤ 3*rows H G M+2*pageSize M b)
    (roof : endAddress base H G M b < 2^w) :
    (bank base H G M b offset).Fits w (endAddress base H G M b) := by
  unfold endAddress at *
  exact ⟨Nat.two_pow_pos _,by change 2^bits H G M b < 2^w; omega,
    by change base+offset+2^bits H G M b ≤ _; omega⟩

theorem zero_fits {w : ℕ} (base H G M b x : ℕ) (roof : endAddress base H G M b < 2^w) :
    (zero base H G M b x).Fits w (endAddress base H G M b) := by
  unfold zero
  split
  · exact ⟨bank_fit _ _ _ _ _ _ (by omega) roof,trivial⟩
  · trivial

theorem field_fits {w : ℕ} (base H G M b : ℕ) (k : Fin 3) (src : Bank)
    (old : src.Fits w base) (roof : endAddress base H G M b < 2^w) :
    (field base H G M b k src).Fits w (endAddress base H G M b) := by
  have kk : k.val ≤ 2 := by omega
  have bound := Nat.mul_le_mul_right (pageSize M b) kk
  have saved : src.Fits w (endAddress base H G M b) :=
    ⟨old.1,old.2.1,old.2.2.trans ((Nat.le_add_right ..).trans (written_le ..))⟩
  exact ⟨bank_fit _ _ _ _ _ _ (by omega) roof,
    ⟨bank_fit _ _ _ _ _ _ (by omega) roof,trivial⟩,saved,
    bank_fit _ _ _ _ _ _ (by omega) roof,trivial⟩

end
end Hierarchy.DescentResetOriginalZeroHalo

end OAI
