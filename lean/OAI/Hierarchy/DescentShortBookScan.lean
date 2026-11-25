import OAI.Hierarchy.DescentSharedBookScan
import OAI.Hierarchy.DescentSharedLeafLookup

namespace OAI
/-! # Every host directory field fits a short packed score, including padded rows -/
namespace Hierarchy.DescentSharedBookScan
open DescentSIMDLookup DescentSharedLeafLookup
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w a Y D H d : ℕ}
def narrow (n : ℕ) (s : Expr) : Expr := .branch .lt s (.lit (2^n)) s (.lit 0)
def scalar (v : Word w) (n : ℕ) : Cell n := if h:v.val<2^n then ⟨v.val,h⟩ else 0

theorem narrow_read (n : ℕ) (wider : n<w) (e : Expr) (m : Memory w) (p : Word w) :
    (narrow n e).eval m p=((scalar (e.eval m p) n).val:Word w) := by
  have real : 2^n<2^w:=Nat.pow_lt_pow_right (by decide) wider
  simp only [narrow,Expr.eval,DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,
    Fin.val_cast_of_lt real,scalar]
  by_cases fits : (e.eval m p).val < 2^n
  · rw [ite_eq_left fits,dite_eq_left fits]
    exact (Fin.cast_val_eq_self _).symm
  · simp [fits]

def record (B : Chart) (H Δ cap d : ℕ) := narrow d (expr B H Δ cap)
def body (B : Chart) (H Δ cap w d out n : ℕ) := scan w out n (record B H Δ cap d)

def ranks (B : Chart) (cap d : ℕ) (m : Memory w) (h : Fin H) (j : Fin (width a Y D)) :=
  scalar ((expr B H D cap).eval m ((finProdFinEquiv (h,j)).val:Word w)) d

theorem short_rows (B : Chart) (a Y D H cap d out : ℕ) (m : Memory w) (low : d<w)
    (fit : (record B H D cap d).Fits w out) (endFit : out+H*width a Y D<2^w) :
    let L:=width a Y D
    let e:=record B H D cap d
    let m':=image out (H*L) e m
    (body B H D cap w d out (H*L)).Exec m m' (4+(H*L)*(2*e.work+4)) ∧
      ∀h : Fin H,∀j : Fin L,m' (out+(h.val*L+j.val))=((ranks B cap d m h j).val:Word w) := by
  refine ⟨scan_exec _ _ _ m fit endFit,fun h j=>?_⟩
  let r:=finProdFinEquiv (h,j)
  change image out _ _ m (out+(h.val*_+j.val))=_
  rw [show h.val*width a Y D+j.val=r.val by change _=j.val+_*h.val; ac_rfl]
  exact (ProtocolRAMGeneratedWrite.read_image out _ _ m r).trans (narrow_read d low _ m _)

theorem rank_eq_of_raw (B : Chart) (cap d out : ℕ) (m : Memory w) (v : Fin H) (p : Fields a Y D) (amount : ℕ)
    (actual : image out (H*width a Y D) (expr B H D cap) m (out+(absolute v p).val)=(amount:Word w))
    (short : amount<2^d) (fits : d≤w) : (ranks B cap d m v (fieldId p)).val=amount := by
  rw [ProtocolRAMGeneratedWrite.read_image] at actual
  have wordBound:=short.trans_le (Nat.pow_le_pow_right (by decide : 0<2) fits)
  have native:=congrArg Fin.val actual
  rw [Fin.val_cast_of_lt wordBound] at native
  change (scalar ((expr B H D cap).eval m ((absolute v p).val:Word w)) d).val=amount
  simp [scalar,native,short]

end
end Hierarchy.DescentSharedBookScan

end OAI
