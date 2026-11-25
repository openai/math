import OAI.Hierarchy.DescentGatheredVectorReshape
import OAI.Hierarchy.DescentOperandStateWrite

namespace OAI
/-! # Contiguous physical allocation for state normalization, all donor gathers and the vector return -/
namespace Hierarchy.DescentOperandVectorArena
open DescentSIMDLookup DescentOperandStateBanks DescentVectorBookReshape ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM.ScalarOperand (Refs)
noncomputable section

structure Layout where
  operands : ℕ
  /-- The normalized tensor has this many physical rows per field and argument. -/
  normalizedRows : ℕ
  /-- The aperture of the eight state-normalizer ROM pages. -/
  stateBits : ℕ
  hosts : ℕ
  lows : ℕ
  groups : ℕ
  radix : ℕ
  lanes : ℕ
  /-- The receiving book has `scalar width * next node capacity` bits per lane. -/
  bookBits : ℕ

def Layout.pageCount (l : Layout) := 7*l.operands
def Layout.norm (l : Layout) (start : ℕ) := start+8*2^l.stateBits
def rounded (n : ℕ) := 2^Nat.clog 2 (n+1)
def Layout.srcWords (l : Layout) := l.pageCount*sourceWords l.hosts l.lows l.groups l.lanes
def Layout.dstWords (l : Layout) := l.pageCount*rows l.hosts l.lows l.groups l.radix l.lanes
def Layout.chunkRows (l : Layout) := (l.hosts*l.lows)*chunks l.groups l.lanes
def Layout.dictWords (l : Layout) := dictionaryWords l.radix l.bookBits l.lanes

/-- There is space for every rounded normalized page, even the last. -/
def Layout.scratch (l : Layout) (start : ℕ) : Bank :=
  ⟨l.norm start+l.pageCount*l.normalizedRows+rounded l.normalizedRows,Nat.clog 2 (l.srcWords+1)⟩
def Layout.tables (l : Layout) (start : ℕ) := (l.scratch start).base+rounded l.srcWords
def Layout.out (l : Layout) (start : ℕ) := output (l.tables start) l.pageCount l.hosts l.lows l.groups l.radix l.bookBits l.lanes
/-- This final reserve covers the rounded physical width of the last returned block bank. -/
def Layout.endAddress (l : Layout) (start : ℕ) := l.out start+l.dstWords+rounded l.chunkRows

theorem affine (l : Layout) (start : ℕ) : l.endAddress start=start+l.endAddress 0 := by
  simp only [Layout.endAddress,Layout.out,output,Layout.tables,Layout.scratch,Layout.norm,Nat.zero_add,Nat.add_assoc]

theorem rounded_bound (n : ℕ) : rounded n≤2*(n+2) := by
  unfold rounded
  cases e:Nat.clog 2 (n+1) with
  | zero=>simp only [pow_zero];omega
  | succ j=>have h:=Nat.pow_lt_of_lt_clog (show j<Nat.clog 2 (n+1) by omega);rw [pow_succ];omega

/-- Linear in the real normalized/gathered/returned extents and the native
packed dictionary cardinal derived from the lane width. -/
theorem bound (l : Layout) (start : ℕ) : l.endAddress start ≤ start+8*2^l.stateBits+
    l.pageCount*l.normalizedRows+2*l.normalizedRows+2*l.srcWords+3*l.dictWords+
    5*l.dstWords+2*l.chunkRows+20 := by
  have h₀:=rounded_bound l.normalizedRows;have h₁:=rounded_bound l.srcWords
  have h₂:=rounded_bound l.dictWords;have h₃:=rounded_bound l.dstWords;have h₄:=rounded_bound l.chunkRows
  change l.norm start+l.pageCount*l.normalizedRows+rounded l.normalizedRows+rounded l.srcWords+
    (l.dictWords+2*l.dstWords)+rounded l.dictWords+rounded l.dstWords+l.dstWords+rounded l.chunkRows≤_
  unfold Layout.norm
  omega

private theorem tables_le_out (l : Layout) (start : ℕ) : l.tables start ≤ l.out start := by
  simp only [Layout.out,output,Nat.add_assoc]
  exact Nat.le_add_right _ _

private theorem tables_le_end (l : Layout) (start : ℕ) : l.tables start ≤ l.endAddress start :=
  (tables_le_out l start).trans ((Nat.le_add_right (l.out start) l.dstWords).trans
    (Nat.le_add_right _ (rounded l.chunkRows)))

theorem arranged (l : Layout) (start : ℕ) {w : ℕ} (space : l.endAddress start<2^w) :
    Room l.pageCount l.hosts l.lows l.groups l.radix l.bookBits l.lanes w (l.tables start) (l.out start) (l.scratch start) := by
  have sec : l.out start+l.dstWords<2^w:=(Nat.le_add_right ..).trans_lt space
  have t:=tables_le_out l start
  have c : l.srcWords≤rounded l.srcWords:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have fit : (l.scratch start).Fits w (l.tables start):=by
    refine ⟨Nat.two_pow_pos _,?_,le_rfl⟩
    change rounded l.srcWords<2^w
    exact (Nat.le_add_left ..).trans_lt (t.trans_lt ((Nat.le_add_right ..).trans_lt sec))
  exact DescentVectorBookReshape.arranged _ _ fit c sec

/-- A subsequent reader can actually use each returned `Bank.read` before the
next allocation, including when rounding crosses the last occupied row. -/
theorem block_room (l : Layout) (start : ℕ) {w : ℕ} (space : l.endAddress start<2^w)
    (p : Fin l.pageCount) (b : Fin l.radix) :
    (blockBank (l.out start) l.hosts l.lows l.groups l.radix l.lanes p b).Fits w (l.endAddress start) := by
  let u:=l.chunkRows
  have under : b.val*u≤l.radix*u:=Nat.mul_le_mul_right _ b.isLt.le
  have less : p.val*(l.radix*u)+b.val*u≤l.pageCount*(l.radix*u) := calc
    _ ≤ p.val*(l.radix*u)+l.radix*u:=Nat.add_le_add_left under _
    _ = (p.val+1)*(l.radix*u):=(Nat.succ_mul _ _).symm
    _ ≤ _:=Nat.mul_le_mul_right _ p.isLt
  have final_ : (blockBank (l.out start) l.hosts l.lows l.groups l.radix l.lanes p b).base+
      (blockBank (l.out start) l.hosts l.lows l.groups l.radix l.lanes p b).size≤l.endAddress start := by
    change l.out start+p.val*(l.radix*u)+b.val*u+rounded u≤l.out start+l.pageCount*(l.radix*u)+rounded u
    omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (final_.trans_lt space),final_⟩

/-- The real gathered source interval and the physical transpose room used by
`DescentGatheredVectorReshape.exec` share one end-address hypothesis. -/
theorem gather_room (l : Layout) (start : ℕ) {w : ℕ} (space : l.endAddress start<2^w) :
    (l.scratch start).base+(l.pageCount*l.lows)*(l.hosts*chunks l.groups l.lanes)<2^w := by
  have ceiling : (l.scratch start).base+rounded l.srcWords≤l.endAddress start :=
    tables_le_end l start
  have capacity : l.srcWords≤rounded l.srcWords:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have same : l.srcWords=(l.pageCount*l.lows)*(l.hosts*chunks l.groups l.lanes) := by
    simp only [Layout.srcWords,sourceWords,Nat.mul_assoc]
  rw [←same]
  exact (Nat.add_le_add_left capacity _).trans_lt (ceiling.trans_lt space)

/-- The eight static pages and the normalized output satisfy exactly the two
numeric bounds consumed by the physical state writer. -/
theorem normalized (l : Layout) (start : ℕ) {w : ℕ} (space : l.endAddress start<2^w) :
    start+8*2^l.stateBits≤l.norm start ∧ l.norm start+l.pageCount*l.normalizedRows<2^w := by
  refine ⟨le_rfl,?_⟩
  have within : l.norm start+l.pageCount*l.normalizedRows ≤ l.tables start :=
    (Nat.le_add_right _ (rounded l.normalizedRows)).trans
      (Nat.le_add_right _ (rounded l.srcWords))
  exact (within.trans (tables_le_end l start)).trans_lt space

/-- These literal addresses admit the composed state writer and original return
program on every memory after the predecessor's donor tables. -/
theorem issue (l : Layout) (start : ℕ) {w D k K cap : ℕ} (space : l.endAddress start<2^w)
    (ak aliasBits field H G M : ℕ) (B : Write.Sources l.operands) (m : Memory w)
    (C : Fin l.pageCount→Fin l.lows→Refs D k K cap) (g₀ : ℕ)
    (rowsFit : l.normalizedRows=H*chunks G M) (bits : l.stateBits=Write.aperture ak aliasBits M)
    (same : g₀=l.groups*l.radix) (lanes : 0<l.lanes) (radix : 0<l.radix)
    (old : Write.Early B w start) (inputs : ∀p j,((C p j).expr l.hosts).inputEnd≤(l.scratch start).base) :
    let first:=Write.issue ak aliasBits field H G M start (l.norm start) w B
    let mid:=Write.imageAt ak aliasBits field H G M start (l.norm start) B m
    let last:=DescentGatheredVectorReshape.program C l.hosts g₀ l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) w (l.scratch start)
    let state:=DescentGatheredVectorReshape.result C l.hosts g₀ l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) (l.scratch start) mid
    (first.seq last).Exec m state (Write.work ak aliasBits field H G M start (l.norm start) B+
      DescentGatheredVectorReshape.ticks C l.hosts g₀ l.groups l.radix l.lanes l.bookBits (l.scratch start)) := by
  intro first mid last state
  have room:=normalized l start space
  have ran : first.Exec m mid (Write.work ak aliasBits field H G M start (l.norm start) B) := (Write.run (k:=ak) (b:=aliasBits) (coeff:=field) (H:=H) (G:=G) (M:=M) B m old (by simpa only [bits] using room.1)
    (by simpa only [rowsFit,Layout.pageCount,DescentOperandStateBanks.pageSize] using room.2)).1
  have cl : chunks g₀ (l.lanes*l.radix)=chunks l.groups l.lanes:=by rw [same];exact chunks_group _ _ _ lanes radix
  have finish : last.Exec mid state (DescentGatheredVectorReshape.ticks C l.hosts g₀ l.groups l.radix l.lanes l.bookBits (l.scratch start)) :=
    DescentGatheredVectorReshape.exec C l.hosts g₀ l.groups l.radix l.lanes l.bookBits (l.tables start) (l.out start) (l.scratch start) mid inputs
      (by rw [cl];exact gather_room l start space) (arranged l start space)
  intro P R K₀ machine;exact Procedure.Exec.then ran finish machine


end
end Hierarchy.DescentOperandVectorArena

end OAI
