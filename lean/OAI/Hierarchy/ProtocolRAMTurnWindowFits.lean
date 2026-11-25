import OAI.Hierarchy.ProtocolRAMTurnWindow
import OAI.Hierarchy.ProtocolRAMTurnCursor
import OAI.Hierarchy.ProtocolRAMTurnShelf

namespace OAI
/-! # Native lookup bounds for the chronological report's physical allocation -/
namespace Hierarchy.ProtocolRAMTurnWindow.Layout
open Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM ProtocolRAMTurnChart ProtocolRAMTurnItinerary
open ProtocolRAMPackedRanked

variable (L : ProtocolRAMTurnWindow.Layout) {w : ℕ}

private theorem raiseBank {b : Bank} {a c : ℕ} (fits : b.Fits w a) (le : a≤c) :
    b.Fits w c := ⟨fits.1,fits.2.1,fits.2.2.trans le⟩

/-- The three public lookup pages used by the prefix walk and all six used by
the gather are allocated as contiguous, immutable pages. -/
theorem header_fits (header bits : ℕ) (room : L.stop≤2^w)
    (before : header+6*2^bits≤L.floor) (f : Fin 6) :
    (get header bits f).Fits w L.zero := by
  change (⟨header+f.val*2^bits,bits⟩ : Bank).Fits w L.zero ∧ True
  refine ⟨⟨Nat.two_pow_pos _,?_,?_⟩,trivial⟩
  · change 2^bits<2^w
    have h := L.bounds
    omega
  · change header+f.val*2^bits+2^bits≤L.floor+1
    have le := Nat.mul_le_mul_right (2^bits) (show f.val≤5 by omega)
    omega

theorem walk_fits (header bits : ℕ) (d : Data) (edge tail head : Bank)
    (rom : ∀f,(get header bits f).Fits w L.zero)
    (safe : ProtocolRAMTurnCursor.Safe d w L.zero)
    (e : edge.Fits w L.zero) (t : tail.Fits w L.zero) (h : head.Fits w L.zero) :
    ∀p∈ProtocolRAMVisitColumns.terms L.zero (L.zero+1+2*L.rows) (walk header bits d edge tail head),
      p.Fits w L.zero := by
  intro p hp
  simp [ProtocolRAMVisitColumns.terms] at hp
  rcases hp with rfl | rfl
  · simp [ProtocolRAMVisitColumns.ptr,walk,Expr.Fits,rom]
  · simp [ProtocolRAMVisitColumns.total,ProtocolRAMVisitColumns.edge,walk,Expr.Fits,rom,safe.rawSource,e,t,h]

set_option maxRecDepth 8192 in
theorem field_fits (header bits : ℕ) (d : Data) (b : Banks) (room : L.stop≤2^w)
    (rom : ∀f,(get header bits f).Fits w L.zero)
    (safe : ProtocolRAMTurnCursor.Safe d w L.zero) (site : d.site=L.site)
    (low : ∀s∈[b.oldSource,b.oldTarget,b.edge,b.tailSite,b.tailRole,b.headRole,b.starts],s.Fits w L.zero)
    (f : Fin 7) : (field (chart header bits d) b f).Fits w L.src := by
  have bound := L.bounds
  have order : L.zero ≤ L.src := by omega
  have hdr (i : Fin 6) := ProtocolRAMGeneratedWrite.fits_mono _ order (rom i)
  have rawL := raiseBank safe.rawSource order
  have rawR := raiseBank safe.rawTarget order
  have oldW := raiseBank safe.oldWidth order
  have srcRole := raiseBank safe.sourceRole order
  have dstRole := raiseBank safe.targetRole order
  have half := raiseBank safe.half order
  have si : d.site.Fits w L.src := by rw [site]; exact L.site_fit room
  have oldL := raiseBank (low b.oldSource (by simp)) order
  have oldR := raiseBank (low b.oldTarget (by simp)) order
  have edge := raiseBank (low b.edge (by simp)) order
  have tail := raiseBank (low b.tailSite (by simp)) order
  have left := raiseBank (low b.tailRole (by simp)) order
  have right := raiseBank (low b.headRole (by simp)) order
  have rank := raiseBank (low b.starts (by simp)) order
  fin_cases f <;> simp [field,role,start,live,onEnd,occurrence,four,plus,minus,chart,
    direction,seat,Expr.Fits,hdr,rawL,rawR,oldW,srcRole,dstRole,half,si,oldL,oldR,edge,tail,left,right,rank]

private theorem tape_fit (f : ℕ) (hf : f≤6) (room : L.stop≤2^w) :
    (⟨L.src+f*L.rows,L.srcBits⟩ : Bank).Fits w L.base := by
  have h := L.bounds
  have size : L.base=L.src+6*L.rows+2^L.srcBits := rfl
  have le := Nat.mul_le_mul_right L.rows hf
  refine ⟨Nat.two_pow_pos _,?_,?_⟩
  · change 2^L.srcBits<2^w
    omega
  · change L.src+f*L.rows+2^L.srcBits≤L.base
    omega

private theorem table_fit (rom bits : ℕ) (endAt : rom+4*2^bits≤L.floor) (j : Fin 4) (room : L.stop≤2^w) :
    (ProtocolRAMTurnDirectory.bank rom bits j).Fits w L.base := by
  have h := L.bounds
  have le := Nat.mul_le_mul_right (2^bits) (show j.val≤3 by omega)
  refine ⟨Nat.two_pow_pos _,?_,?_⟩
  · change 2^bits<2^w
    omega
  · change rom+j.val*2^bits+2^bits≤L.base
    omega

theorem scatter_fits (rom bits : ℕ) (endAt : rom+4*2^bits≤L.floor) (room : L.stop≤2^w) :
    let A := ProtocolRAMTurnShelf.tables rom bits L.src L.srcBits L.rows
    (ProtocolRAMTurnShelf.addressExpr A L.sink).Fits w L.base ∧ (ProtocolRAMTurnShelf.valueExpr A).Fits w L.base := by
  have table (j : Fin 4) := L.table_fit rom bits endAt j room
  have data := L.tape_fit 0 (by decide) room
  have width := L.tape_fit 4 (by decide) room
  have location := L.tape_fit 5 (by decide) room
  have seat := L.tape_fit 6 (by decide) room
  simp only [Nat.zero_mul,Nat.add_zero] at data
  simp [ProtocolRAMTurnShelf.addressExpr,ProtocolRAMTurnShelf.valueExpr,ProtocolRAMTurnShelf.tables,
    Expr.Fits,table,data,width,location,seat]

end Hierarchy.ProtocolRAMTurnWindow.Layout

end OAI
