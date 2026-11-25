import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetStemKeyReindex

namespace OAI
/-! # One packed-row pointer for every compact host and group chunk -/
namespace Hierarchy.DescentResetTrunkCompactRows
open DescentSIMDLookup DescentDyadicSpan DescentPackedZip DescentSixParty.Chronology
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M b : ℕ}

def rowBase (base H G M : ℕ) := base+DescentResetStemKeyReindex.size H H G M
def endAddress (base H G M : ℕ) := rowBase base H G M + span (H*chunks G M)

def make (base H G M : ℕ) (ports : Bank) : Expr :=
  let n:=H*chunks G M
  let who:=Expr.lookup ports (.lookup (DescentResetStemKeyReindex.actors base H n) .row)
  .branch .lt who (.lit H)
    (.op .add (.lookup (DescentResetStemKeyReindex.chunkIDs base H n) .row)
      (.lookup (DescentResetStemKeyReindex.offsets base H) who)) (.lit n)

private def scanPhase (w rows n : ℕ) (e : Expr) : NativePhase w :=
  ⟨scan w rows n e, 4+n*(2*e.work+4), image rows n e, scan_cheap w rows n e⟩

def phase (w base H G M : ℕ) (ports : Bank) : NativePhase w :=
  (DescentResetStemKeyReindex.phase w base H H G M).seq
    (scanPhase w (rowBase base H G M) (H*chunks G M) (make base H G M ports))

theorem work (base H G M : ℕ) (ports : Bank) : (make base H G M ports).work=40 := rfl

private theorem layout (base H G M : ℕ) (room : endAddress base H G M<2^w) :
    let n:=H*chunks G M
    let stop:=rowBase base H G M
    (DescentResetStemKeyReindex.actors base H n).Fits w stop ∧
      (DescentResetStemKeyReindex.offsets base H).Fits w stop ∧
      (DescentResetStemKeyReindex.chunkIDs base H n).Fits w stop := by
  intro n stop
  change base+(span H+2*span n)+span n<2^w at room
  change (0< span n ∧ span n<2^w ∧ base+span H+span n≤base+(span H+2*span n)) ∧
    (0< span H ∧ span H<2^w ∧ base+span H≤base+(span H+2*span n)) ∧
    (0< span n ∧ span n<2^w ∧ base+span H+span n+span n≤base+(span H+2*span n))
  exact ⟨⟨span_pos _,by omega,by omega⟩,⟨span_pos _,by omega,by omega⟩,
    ⟨span_pos _,by omega,by omega⟩⟩

private theorem make_fits (base H G M : ℕ) (ports : Bank) (portFit : ports.Fits w base)
    (room : endAddress base H G M < 2^w) : (make base H G M ports).Fits w (rowBase base H G M) := by
  obtain ⟨actors, offsets, parts⟩ := layout base H G M room
  have below : base ≤ rowBase base H G M := Nat.le_add_right base _
  have fit : ports.Fits w (rowBase base H G M) :=
    ⟨portFit.1, portFit.2.1, portFit.2.2.trans below⟩
  exact ⟨⟨fit, actors, trivial⟩, trivial, ⟨⟨parts, trivial⟩, offsets, fit, actors, trivial⟩, trivial⟩

theorem any (base : ℕ) (ports : Bank) (m : Memory w) (portFit : ports.Fits w base)
    (room : endAddress base H G M<2^w) :
    let q:=phase w base H G M ports
    q.Runs m ∧ ∀a,a<base ∨ endAddress base H G M≤a→q.image m a=m a := by
  let n := H*chunks G M
  let rows := rowBase base H G M
  let e := make base H G M ports
  let first := DescentResetStemKeyReindex.phase w base H H G M
  let second := scanPhase w rows n e
  have end_ : rows+span n<2^w := room
  have hi : rows<2^w := (Nat.le_add_right rows (span n)).trans_lt end_
  have before : base≤rows := Nat.le_add_right base _
  have actual := DescentResetStemKeyReindex.run (base:=base) (H₀:=H) (H₁:=H) (G:=G) (M:=M) m hi
  have size : rows+n<2^w := (Nat.add_le_add_left (span_ge n) rows).trans_lt end_
  have two : second.Runs (first.image m) :=
    scan_exec rows n e (first.image m) (make_fits base H G M ports portFit room) size
  refine ⟨NativePhase.seq_runs first second m actual.1 two, ?_⟩
  intro a away
  have outRows : a<rows ∨ rows+n≤a :=
    away.imp (fun h => h.trans_le before) (fun h => (Nat.add_le_add_left (span_ge n) rows).trans h)
  have outFirst : a<base ∨ rows≤a :=
    away.imp_right (fun h => (Nat.le_add_right rows (span n)).trans h)
  exact (ProtocolRAMGeneratedWrite.frame_image rows n e (first.image m) a outRows).trans
    (actual.2.2 a outFirst)

private theorem sample (base : ℕ) (ports : Bank) (mid : Memory w) (alt : Fin H → Option (Fin H))
    (measured : DescentResetStemKeyReindex.Fixed base H H G M mid)
    (installed : ∀ h : Fin H, ports.read mid (h.val : Word w) = (((alt h).elim H Fin.val : ℕ) : Word w))
    (nw : H < 2^w) (room : endAddress base H G M < 2^w) (p : Row H G M) :
    (make base H G M ports).eval mid ((row H G M p).val : Word w) =
      (alt p.1).elim ((H*chunks G M : ℕ) : Word w)
        (fun t => ((row H G M (t,p.2)).val : Word w)) := by
  let n := H*chunks G M
  let root := DescentResetStemKeyReindex.actors base H n
  let offsets := DescentResetStemKeyReindex.offsets base H
  let part := DescentResetStemKeyReindex.chunkIDs base H n
  let i : Fin n := row H G M p
  obtain ⟨rf, sf, cf⟩ := layout base H G M room
  have within := i.isLt.trans_le (span_ge n)
  have who : root.read mid (i.val : Word w) = (p.1.val : Word w) :=
    (bank_read root mid within rf).trans (measured.actor p)
  have lane : part.read mid (i.val : Word w) = (p.2.val : Word w) :=
    (bank_read part mid within cf).trans (measured.chunk p)
  have offset (t : Fin H) : offsets.read mid (t.val : Word w) = ((chunks G M*t.val : ℕ) : Word w) :=
    (bank_read offsets mid (t.isLt.trans_le (span_ge H)) sf).trans (measured.offset t)
  change (if decide (ports.read mid (root.read mid (i.val : Word w)) < (H : Word w)) then
      part.read mid (i.val : Word w) + offsets.read mid (ports.read mid (root.read mid (i.val : Word w)))
    else (n : Word w)) = _
  rw [who, installed p.1, lane]
  cases chosen : alt p.1 with
  | none => simp [n]
  | some t =>
    have active : (t.val : Word w) < (H : Word w) := by
      simpa only [Fin.lt_def, Fin.val_cast_of_lt (t.isLt.trans nw), Fin.val_cast_of_lt nw] using t.isLt
    have addr : (row H G M (t,p.2)).val = p.2.val + chunks G M*t.val := rfl
    simp only [Option.elim_some, offset t, addr, Nat.cast_add]
    exact ite_eq_left (decide_eq_true active)

theorem run (base : ℕ) (ports : Bank) (m : Memory w) (alt : Fin H→Option (Fin H))
    (portFit : ports.Fits w base) (count : H≤ports.size)
    (installed : ∀h : Fin H,m (ports.base+h.val)=(((alt h).elim H Fin.val:ℕ):Word w))
    (room : endAddress base H G M<2^w) :
    let n:=H*chunks G M
    let rows:=rowBase base H G M
    let q:=phase w base H G M ports
    q.Runs m ∧ (∀a,a<base ∨ endAddress base H G M≤a→q.image m a=m a) ∧
      (∀p : Row H G M,q.image m (rows+(row H G M p).val)=
        ((alt p.1).elim n (fun h=>(row H G M (h,p.2)).val):Word w)) := by
  intro n rows q
  have frame := any (H:=H) (G:=G) (M:=M) base ports m portFit room
  refine ⟨frame.1, frame.2, ?_⟩
  let first := DescentResetStemKeyReindex.phase w base H H G M
  let mid := first.image m
  have finish : rows+span n<2^w := room
  have top : rows<2^w := (Nat.le_add_right rows (span n)).trans_lt finish
  have done := DescentResetStemKeyReindex.run (base:=base) (H₀:=H) (H₁:=H) (G:=G) (M:=M) m top
  have pointer (h : Fin H) : ports.read mid (h.val : Word w) = (((alt h).elim H Fin.val : ℕ) : Word w) := by
    have low : ports.base+h.val < base :=
      (Nat.add_lt_add_left (h.isLt.trans_le count) ports.base).trans_le portFit.2.2
    exact (bank_read ports mid (h.isLt.trans_le count) portFit).trans
      ((done.2.2 (ports.base+h.val) (.inl low)).trans (installed h))
  intro p
  let i : Fin n := row H G M p
  change ProtocolRAM.image rows n (make base H G M ports) mid (rows+i.val) = _
  exact (ProtocolRAMGeneratedWrite.read_image rows n (make base H G M ports) mid i).trans
    (sample base ports mid alt done.2.1 pointer (count.trans_lt portFit.2.1) room p)

theorem extent (base H G M : ℕ) : endAddress base H G M≤base+(2*H+6*(H*chunks G M)+4) := by
  have a:=DescentResetStemKeyReindex.size_le H H G M
  have c:=span_le (H*chunks G M)
  unfold endAddress rowBase
  omega

end
end Hierarchy.DescentResetTrunkCompactRows

end OAI
