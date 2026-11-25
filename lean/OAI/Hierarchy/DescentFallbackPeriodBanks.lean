import OAI.Hierarchy.DescentFallbackWindowSources
import OAI.Hierarchy.DescentSharedBookTariff

namespace OAI
/-! # The authentic wire, self, opposite-stencil, and shared-price operand banks -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedLeafLookup DescentSharedBookScan
open DescentSharedCableNames.Stage DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r field H G M w : ℕ}

def operand (ports : Ports D) (books : Header) (here : Fin L→Expr) (tagged : Fin L→Bank)
    (sign : Fin L→Fin (2*cap)→Expr) : Input D L cap n r→Expr
  | .inl (.inl i)=>here i
  | .inl (.inr (j,i))=>peerExpr ports (tagged i) H j
  | .inr (.inl (i,q))=>sign i q
  | .inr (.inr j)=>source books j

/-- An observed neighbor's shape zero is carried by the positive code one. Missing peers
are zero at the physical branch in peerExpr. The per-host score is read once and broadcast. -/
theorem operands (ports : Ports D) (books : Header) (here : Fin L→Expr) (tagged : Fin L→Bank)
    (sign : Fin L→Fin (2*cap)→Expr) (prior : Fin H→Fin G→Fin L→ℕ)
    (roster : Fin H→Fin D→Option (Fin H)) (signs : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (width r (2^n) D)→ℕ) (out : ℕ) (m : Memory w)
    (addressable : ∀lo,Accessible ports (tagged lo) H G M w out)
    (neighbors : Mounted ports roster m G M)
    (actual : ∀lo,Source (here lo) (fun h g=>(prior h g lo:Cell field)) M m)
    (before : ∀lo,Reads (tagged lo) (fun h g=>((prior h g lo+1:ℕ):Cell field)) M m)
    (old : ∀lo u,Source (sign lo u) (fun h g=>((DescentSignedCableCodec.encode (signs h g lo u)).val:Cell field)) M m)
    (reader : Readable books (width r (2^n) D) H G M field w out)
    (fixed : Fixed books (width r (2^n) D) H G M field m)
    (stored : ∀h j,m (books.ranks.base+(h.val*width r (2^n) D+j.val))=(((rank h j:Cell field).val:ℕ):Word w)) :
    ∀j,Source (operand (H:=H) ports books here tagged sign j) (fun h g=>inputs (field:=field) prior roster signs rank h g j) M m := by
  intro j
  rcases j with (i|⟨k,lo⟩)|(⟨lo,z⟩|i)
  · exact actual i
  · have peer:=peerSource ports (tagged lo) out (addressable lo) roster m neighbors
      (fun h g=>((prior h g lo+1:ℕ):Cell field)) (before lo) k
    have eqn (v : Fin H) (g : Fin G) :
        (roster v k).elim (0:Cell field) (fun h=>((prior h g lo+1:ℕ):Cell field))=
         inputs prior roster signs rank v g (.inl (.inr (k,lo))) := by cases a:roster v k <;> simp [inputs,a]
    simpa only [operand,eqn] using peer
  · exact old lo z
  · exact repeated_source books out m reader fixed (fun h j=>(rank h j:Cell field)) stored i

theorem scalar_prefix (chart : Chart) (books : Header) (Ht H D r n : ℕ)
    (out : ℕ) (m : Memory w) (low : Ht+2<w) (wide : Ht+2≤field)
    (fit : (record chart H D (2^Ht) (Ht+2)).Fits w out) (span : out+H*width r (2^n) D<2^w)
    (linked : books.ranks.base=out) :
    let N:=width r (2^n) D
    let term:=record chart H D (2^Ht) (Ht+2)
    let m':=image out (H*N) term m
    (body chart H D (2^Ht) w (Ht+2) out (H*N)).Exec m m' (4+(H*N)*(2*term.work+4)) ∧
    (∀(h : Fin H) (j : Fin N),m' (books.ranks.base+(h.val*N+j.val))=
      ((((ranks (a:=r) (Y:=2^n) (D:=D) chart (2^Ht) (Ht+2) m h j).val:Cell field).val:Word w))) ∧
    ∀addr,(addr<out ∨ out+H*N≤addr)→m' addr=m addr := by
  obtain ⟨run,read⟩:=short_rows chart r (2^n) D H (2^Ht) (Ht+2) out m low fit span
  refine ⟨run,?_,fun addr away=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ away⟩
  intro h j
  rw [linked,read,Fin.val_cast_of_lt ((ranks (a:=r) (Y:=2^n) (D:=D) chart (2^Ht) (Ht+2) m h j).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) wide))]

end
end Hierarchy.DescentFallbackPeriod

end OAI
