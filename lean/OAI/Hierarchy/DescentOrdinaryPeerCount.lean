import OAI.Hierarchy.DescentOrdinaryPeerRows

namespace OAI
/-! The count published alongside an ordinary adjacency table is the previous
physical count times the full number of local host shapes. -/
namespace Hierarchy.DescentOrdinaryPeerCount
open DescentOrdinaryPeerRows DescentSixParty.Chronology DescentDyadicSpan DescentPackedZip
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H D R E S w : ℕ}

def newCount (base H D R E : ℕ) : Bank := ⟨endAddress base H D R E,0⟩
def roof (base H D R E : ℕ) := endAddress base H D R E+1

def next (base H D R E S : ℕ) (count : Bank) : Expr :=
  let src:=Expr.lookup count (.lit 0)
  let origin:=(DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin
  .branch .lt src (.lit H) (.lookup origin src) (.lit (H*S))

def emit (w base H D R E S : ℕ) (count : Bank) : NativePhase w :=
  let out:=endAddress base H D R E
  let e:=next base H D R E S count
  ⟨scan w out 1 e,4+1*(2*e.work+4),ProtocolRAM.image out 1 e,scan_cheap w out 1 e⟩

def program (w base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) : NativePhase w :=
  (phase w base H D R E count source shapes).seq (emit w base H D R E S count)

private theorem prior (base H D R E : ℕ) : base≤endAddress base H D R E :=
  (Nat.le_add_right base _).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

private theorem origin_fit (base H D R E : ℕ) (room : roof base H D R E<2^w) :
    (DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin.Fits w (endAddress base H D R E):=by
  have upper : (DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin.base+span H≤endAddress base H D R E:=by
    dsimp [DescentOrdinaryPeerChart.tables,endAddress,DescentOrdinaryPeerChart.top,DescentOrdinaryPeerChart.out,DescentOrdinaryPeerChart.length]
    omega
  have hi : endAddress base H D R E<2^w:=(Nat.le_add_right ..).trans_lt room
  exact ⟨span_pos _,(Nat.le_add_left ..).trans_lt (upper.trans_lt hi),upper⟩

set_option maxHeartbeats 1000000 in
theorem any (base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) (m : Memory w)
    (cf : count.Fits w base) (src : source.Fits w base) (host : H<2^w) (room : roof base H D R E<2^w) :
    let p:=program w base H D R E count source shapes
    p.Runs m ∧ ∀a,a<base ∨ roof base H D R E≤a→p.image m a=m a := by
  intro p
  let f:=phase w base H D R E count source shapes
  have size : endAddress base H D R E<2^w:=(Nat.le_add_right ..).trans_lt room
  have sl:=DescentOrdinaryPeerRows.any base H D R E count source shapes m cf src host size
  have keep:=prior base H D R E
  have ofit:=origin_fit base H D R E room
  have moved : count.Fits w (endAddress base H D R E):=⟨cf.1,cf.2.1,cf.2.2.trans keep⟩
  have ok : (next base H D R E S count).Fits w (endAddress base H D R E):=
    ⟨⟨moved,trivial⟩,trivial,⟨ofit,moved,trivial⟩,trivial⟩
  let g := emit w base H D R E S count
  have writes : g.Runs (f.image m) :=
    scan_exec (endAddress base H D R E) 1 (next base H D R E S count) (f.image m) ok room
  change (f.seq g).Runs m ∧ ∀ a, a<base ∨ roof base H D R E≤a → (f.seq g).image m a=m a
  refine ⟨NativePhase.seq_runs f g m sl.1 writes,?_⟩
  intro a outside
  exact NativePhase.seq_keeps f g m a
    (sl.2 a (outside.imp_right ((Nat.le_add_right ..).trans ·)))
    (ProtocolRAMGeneratedWrite.frame_image (endAddress base H D R E) 1
      (next base H D R E S count) (f.image m) a (outside.imp_left (·.trans_le keep)))

private theorem next_eval (base N H D R E S : ℕ) (count : Bank) (m : Memory w) (i : Word w)
    (bounded : N ≤ H) (host : H < 2^w) (stored : count.read m ((0 : ℕ) : Word w) = (N : Word w)) :
    (next base H D R E S count).eval m i =
      if N < H then (DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin.read m (N : Word w)
      else ((H*S : ℕ) : Word w) := by
  let org := (DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin
  change (if Comparison.lt.test (count.read m ((0 : ℕ) : Word w)) (H : Word w) then
    org.read m (count.read m ((0 : ℕ) : Word w)) else ((H*S : ℕ) : Word w)) = _
  have cmp : Comparison.lt.test (N : Word w) (H : Word w) = decide (N<H) := by
    simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt host,Fin.val_cast_of_lt (bounded.trans_lt host)]
  rw [stored,cmp]
  by_cases h : N < H <;> simp [h,org]

set_option maxHeartbeats 1000000 in
theorem count_read (base N H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) (m : Memory w)
    (cf : count.Fits w base) (src : source.Fits w base) (host : H<2^w) (room : roof base H D R E<2^w)
    (bounded : N≤H) (stored : m count.base=(N:Word w)) :
    (program w base H D R E count source shapes).image m (newCount base H D R E).base=((N*S:ℕ):Word w) := by
  let f:=phase w base H D R E count source shapes
  have full:=DescentOrdinaryPeerRows.any base H D R E count source shapes m cf src host ((Nat.le_add_right ..).trans_lt room)
  have stable : f.image m count.base=(N:Word w):=(full.2 _ (.inl ((Nat.lt_add_of_pos_right cf.1).trans_le cf.2.2))).trans stored
  have readCount : count.read (f.image m) ((0:ℕ):Word w)=(N:Word w):=
    (bank_read count _ cf.1 cf).trans (by simpa using stable)
  change ProtocolRAM.image (endAddress base H D R E) 1 (next base H D R E S count) (f.image m) _=_
  rw [show (newCount base H D R E).base=endAddress base H D R E+((0:Fin 1).val) by rfl,
      ProtocolRAMGeneratedWrite.read_image _ 1 _ _ (0:Fin 1),
      next_eval base N H D R E S count (f.image m) _ bounded host readCount]
  by_cases low : N < H
  · rw [ite_eq_left low]
    let org := (DescentOrdinaryPeerChart.tables (fixed base H D) H (R*E)).origin
    have available : N < org.size := low.trans_le (span_ge H)
    change org.read (f.image m) (N : Word w) = _
    rw [bank_read org (f.image m) available (origin_fit base H D R E room)]
    let req := DescentOrdinaryPeerSlots.request (H:=H) (P:=DescentTenHopRAM.paths D) (R:=R) (D:=E) shapes
    exact DescentOrdinaryPeerChart.origin_word (fixed base H D) R count (reached base H D) req
      ((reach w base H D source).image m) ⟨N,low⟩
  · rw [ite_eq_right low]
    exact congrArg (fun n : ℕ => ((n*S : ℕ) : Word w)) (Nat.le_antisymm (Nat.le_of_not_gt low) bounded)

theorem keeps (base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) (m : Memory w)
    (a : ℕ) (before : a<endAddress base H D R E) :
    (program w base H D R E count source shapes).image m a=(phase w base H D R E count source shapes).image m a :=
  ProtocolRAMGeneratedWrite.frame_image _ 1 _ _ a (.inl before)

theorem extent (base H D R E : ℕ) :
    roof base H D R E ≤ base+2*(H*DescentTenHopRAM.paths D)+8*(R*E)+2*H+7 := by
  have lower:=DescentOrdinaryPeerRows.extent base H D R E
  dsimp only [roof]
  omega

theorem output_fit (base H D R E : ℕ) (space : roof base H D R E<2^w) :
    (peers base H D R E).Fits w (roof base H D R E) ∧ R*E≤(peers base H D R E).size ∧
    (newCount base H D R E).Fits w (roof base H D R E) := by
  have earlier : (peers base H D R E).base+(peers base H D R E).size=endAddress base H D R E:=rfl
  have extent_ : endAddress base H D R E≤roof base H D R E:=Nat.le_add_right ..
  exact ⟨⟨span_pos _,(Nat.le_add_left ..).trans_lt (earlier.le.trans_lt (extent_.trans_lt space)),
    earlier.le.trans extent_⟩,span_ge _,⟨Nat.zero_lt_one,(Nat.le_add_left 1 (endAddress base H D R E)).trans_lt space,le_rfl⟩⟩

theorem price (base H D R E : ℕ) (count source : Bank) (shapes : Fin S→Finset (Fin S)) :
    let p:=program w base H D R E count source shapes
    p.ticks+DescentStaticWordColumn.names p.program ≤
      15000*(H+1)*(D+12)^50+300*(R*E)+50*H+800 := by
  intro p
  have a:=DescentOrdinaryPeerRows.price (w:=w) base H D R E count source shapes
  change ((phase w base H D R E count source shapes).ticks+(emit w base H D R E S count).ticks)+DescentStaticWordColumn.names (((phase w base H D R E count source shapes).program).seq (emit w base H D R E S count).program)≤_
  rw [DescentStaticWordColumn.names_seq]
  have bill : DescentStaticWordColumn.names (emit w base H D R E S count).program=91:=by
    change DescentStaticWordColumn.names (scan w _ 1 _) = _
    rw [DescentStaticWordColumn.names_scan]; rfl
  change (phase w base H D R E count source shapes).ticks+48+(DescentStaticWordColumn.names (phase w base H D R E count source shapes).program+DescentStaticWordColumn.names (emit w base H D R E S count).program)≤_
  rw [bill]
  omega


end
end Hierarchy.DescentOrdinaryPeerCount

end OAI
