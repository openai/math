import OAI.Hierarchy.DescentScalarVenueDirectoryROM
import OAI.Hierarchy.DescentPackedHostLookupROM
import OAI.Hierarchy.DescentScalarVenueMask

namespace OAI
/-! # All donor return tables and their shared packed query ROM in one memory -/
namespace Hierarchy.DescentScalarVenueMask.Headers
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentScalarVenueDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M P w : ℕ}

def start (base H P : ℕ):=base+DescentScalarVenueDirectory.ROM.size H P
def afterHeaders (base H P : ℕ):=start base H P+P*(H*P)
def rom (base H P : ℕ):=afterHeaders base H P+DescentScalarVenueDirectory.ROM.page H P
def post (base H G M P : ℕ):=DescentPackedChildNeighbor.SIMD.ROM.output (rom base H P) P (Packed.bits P) 1 M H G

def bank (base H P : ℕ) (s : Fin P):Bank:=⟨origin (start base H P) H P s.val,DescentScalarVenueDirectory.ROM.width H P⟩
def layout (base H G M P : ℕ) (s : Fin P):=DescentPackedChildNeighbor.SIMD.ROM.layout (rom base H P) P (Packed.bits P) 1 M (DescentPackedChildNeighbor.SIMD.ROM.rowBits H G M) (bank base H P s)

def code (sorted ends : Bank) (base H G M P w : ℕ): Procedure w:=
  let C:=DescentScalarVenueDirectory.ROM.chart sorted ends base H P;let scans:=passes C (start base H P) H P
  ((DescentStaticWordColumn.program w base (DescentScalarVenueDirectory.ROM.shape H P) (DescentScalarVenueDirectory.ROM.size H P)).seq (ProtocolRAM.program w scans)).seq (DescentPackedChildNeighbor.SIMD.ROM.program (rom base H P) P (Packed.bits P) 1 M H G w)

def image (sorted ends : Bank) (base H G M P : ℕ) (m : Memory w):=
  let C:=DescentScalarVenueDirectory.ROM.chart sorted ends base H P;let scans:=passes C (start base H P) H P
  let shape:=DescentStaticWordColumn.image base (DescentScalarVenueDirectory.ROM.shape H P) m (DescentScalarVenueDirectory.ROM.size H P)
  DescentPackedChildNeighbor.SIMD.ROM.after (rom base H P) P (Packed.bits P) 1 M H G (ProtocolRAM.result scans shape)

def ticks (sorted ends : Bank) (base H G M P : ℕ):=
  let scans:=passes (DescentScalarVenueDirectory.ROM.chart sorted ends base H P) (start base H P) H P
  ((4+10*DescentScalarVenueDirectory.ROM.size H P)+ProtocolRAM.clock scans)+(4+10*DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G)

theorem bankFits (base H G M P w : ℕ) (s : Fin P) (last : post base H G M P+H*chunks G M<2^w):
    (bank base H P s).Fits w (rom base H P) ∧ H*P≤(bank base H P s).size:=by
  have width: H*P≤DescentScalarVenueDirectory.ROM.page H P:=(le_max_right ..).trans ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _))
  have row:s.val*(H*P)≤P*(H*P):=Nat.mul_le_mul_right _ s.isLt.le
  have high:rom base H P≤post base H G M P:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have room : (bank base H P s).base+(bank base H P s).size≤rom base H P:=by dsimp [bank,origin,Bank.size,rom,afterHeaders,DescentScalarVenueDirectory.ROM.page] at *;omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (room.trans_lt (high.trans_lt ((Nat.le_add_right ..).trans_lt last))),room⟩,width⟩

/-- Only the actual endpoints and actual sorted rank directory precede this
pass. The common lookup dictionary is written once for every donor. -/
theorem mount (sorted ends : Bank) (base : ℕ) (m : Memory w) (walks : Fin H→Fin P→Option (Fin H))
    (sortedFit : sorted.Fits w base) (endFit : ends.Fits w base) (sortedSize : H*P≤ sorted.size) (endSize : H*P≤ends.size)
    (sortedRead : ∀h s,m (sorted.base+(h.val*P+s.val))=(number (DescentSortedRoster.indexed walks h s):Word w))
    (terminalRead : ∀h p,m (ends.base+(h.val*P+p.val))=(number (walks h p):Word w))
    (last : post base H G M P+H*chunks G M<2^w) :
    let state:=image sorted ends base H G M P m;let out:=post base H G M P
    (code sorted ends base H G M P w).Exec m state (ticks sorted ends base H G M P) ∧
      (∀s,DescentPackedChildNeighbor.SIMD.Stored (layout base H G M P s) H G (Packed.bits P) 1 M (checks walks s) state) ∧
      (∀s q,q.Fits w out→DescentPackedChildNeighbor.SIMD.Room (layout base H G M P s) q H G (Packed.bits P) 1 M w out) ∧
      (∀a,a<base ∨ out≤a→state a=m a) ∧ CheapCode (code sorted ends base H G M P w):=by
  intro state out
  have middle:afterHeaders base H P≤rom base H P:=Nat.le_add_right ..
  have top:rom base H P+DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G≤out:=Nat.le_add_right ..
  have exist:rom base H P≤out:=(Nat.le_add_right ..).trans top
  have high:out<2^w:=(Nat.le_add_right ..).trans_lt last
  obtain ⟨setup,room,initial,fr,cheap⟩:=DescentScalarVenueDirectory.ROM.mount sorted ends base m walks sortedFit endFit sortedSize endSize sortedRead terminalRead (middle.trans_lt (exist.trans_lt high))
  obtain ⟨pass,printed,untouched,cheapP⟩:=emit _ _ room _ walks initial
  let chart := DescentScalarVenueDirectory.ROM.chart sorted ends base H P
  let scans := passes chart (start base H P) H P
  let shape := DescentStaticWordColumn.image base (DescentScalarVenueDirectory.ROM.shape H P) m
    (DescentScalarVenueDirectory.ROM.size H P)
  let printedState := ProtocolRAM.result scans shape
  let tableSize := DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G
  let tableWords := DescentPackedChildNeighbor.SIMD.ROM.numbers P (Packed.bits P) 1 M H G
  let shapeCode := DescentStaticWordColumn.program w base (DescentScalarVenueDirectory.ROM.shape H P)
    (DescentScalarVenueDirectory.ROM.size H P)
  let shapeTicks := 4+10*DescentScalarVenueDirectory.ROM.size H P
  let lookupCode := DescentStaticWordColumn.program w (rom base H P) tableWords tableSize
  have stat : lookupCode.Exec printedState state (4+10*tableSize) :=
    @DescentStaticWordColumn.mount w (rom base H P) tableSize tableWords printedState (top.trans_lt high)
  have prefixRun : (shapeCode.seq (ProtocolRAM.program w scans)).Exec m printedState
      (shapeTicks+ProtocolRAM.clock scans) :=
    @Procedure.Exec.then w shapeCode (ProtocolRAM.program w scans) m shape printedState
      shapeTicks (ProtocolRAM.clock scans) (@setup) (@pass)
  refine ⟨@Procedure.Exec.then w (shapeCode.seq (ProtocolRAM.program w scans)) lookupCode
      m printedState state (shapeTicks+ProtocolRAM.clock scans) (4+10*tableSize) (@prefixRun) (@stat),
    ?_, ?_, ?_, @cheap_seq w (shapeCode.seq (ProtocolRAM.program w scans)) lookupCode
      (@cheap_seq w shapeCode (ProtocolRAM.program w scans) (@cheap) (@cheapP))
      (@DescentStaticWordColumn.cheap w (rom base H P) tableWords tableSize)⟩
  · intro s
    have fit := bankFits base H G M P w s last
    apply DescentPackedChildNeighbor.SIMD.ROM.stored (H:=H) (G:=G) (a:=Packed.bits P) (M:=M)
      (bank base H P s) (rom base H P) (DescentPackedChildNeighbor.SIMD.ROM.rowBits H G M)
      (checks walks s) printedState ((Nat.add_le_add_left fit.2 _).trans fit.1.2.2)
    intro h p
    have small : (hit walks s h p).toNat < 2^1 := by cases hit walks s h p <;> decide
    simpa only [checks, Fin.val_cast_of_lt small, printedState, scans, chart, shape, bank, start]
      using printed s h p
  · intro s q good
    exact (DescentPackedChildNeighbor.SIMD.ROM.arranged_expr (T:=P) (a:=Packed.bits P) (b:=1)
      (H:=H) (G:=G) (M:=M) (bank base H P s) q (rom base H P) (bankFits base H G M P w s last)
      good last).2
  · intro x away
    have retain := DescentStaticWordColumn.frame (rom base H P) tableSize tableWords printedState x
    rcases away with below|above
    · have early : x < start base H P := below.trans_le (Nat.le_add_right ..)
      exact (retain (.inl (early.trans_le ((Nat.le_add_right ..).trans middle)))).trans
        ((untouched x (.inl early)).trans (fr x (.inl below)))
    · have later : afterHeaders base H P ≤ x := middle.trans (exist.trans above)
      exact (retain (.inr (top.trans above))).trans
        ((untouched x (.inr later)).trans (fr x (.inr ((Nat.le_add_right ..).trans later))))

end
end Hierarchy.DescentScalarVenueMask.Headers

end OAI
