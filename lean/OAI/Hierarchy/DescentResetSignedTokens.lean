import OAI.Hierarchy.DescentResetSignedTokenShape
import OAI.Hierarchy.DescentVenueSlabPhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentMarkedNeighborToken

namespace OAI
/-! # Retiling signed records and publishing their reset tokens -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology ProtocolRAM ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace Layout
variable (s : Layout)
def word (j : ℕ) := (DescentSIMDLookup.table (M:=s.targetLanes)
  (DescentPackedMatchSenderPins.table s.degree s.cap s.short) (j:Cell (s.bits*s.targetLanes))).val
def readers (base : ℕ) : List Expr := List.ofFn fun j : Fin s.slots =>
  Expr.lookup (s.dictionary base) (.lookup (s.raw base (finProdFinEquiv.symm j)) .row)
def passes (base : ℕ) := columns s.rows (s.start base) (s.readers base)
def phase (base w : ℕ) (pages : s.Slot → Bank) : NativePhase w :=
  let shift : NativePhase w := ⟨DescentVenueSlabs.program s.venue (s.inputs pages) base w,
    DescentVenueSlabs.ticks s.venue (s.inputs pages) base,DescentVenueSlabs.image s.venue (s.inputs pages) base,
    DescentVenueSlabs.cheap s.venue (s.inputs pages) base w⟩
  let lut := s.dictionary base
  let table : NativePhase w := ⟨DescentStaticWordColumn.program w lut.base s.word lut.size,4+10*lut.size,
    fun m=>DescentStaticWordColumn.image lut.base s.word m lut.size,DescentStaticWordColumn.cheap w lut.base s.word lut.size⟩
  let scans : NativePhase w := ⟨ProtocolRAM.program w (s.passes base),ProtocolRAM.clock (s.passes base),
    ProtocolRAM.result (s.passes base),ProtocolRAM.program_cheap w (s.passes base)⟩
  (shift.seq table).seq scans

theorem room {w base : ℕ} (cap : s.endAddress base < 2^w) :
    (s.dictionary base).Fits w (s.start base) ∧
    (∀t : s.Slot,(s.raw base t).Fits w (s.dictionary base).base ∧ s.rows≤(s.raw base t).size) ∧
    (∀t : s.Slot,(s.bank base t).Fits w (s.endAddress base) ∧ s.rows≤(s.bank base t).size) := by
  have past : s.start base ≤ s.endAddress base := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have next : (s.dictionary base).base ≤ s.start base := Nat.le_add_right ..
  refine ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (past.trans_lt cap),le_rfl⟩,?_,?_⟩
  · intro t
    exact DescentVenueSlabs.page_room s.venue base w (finProdFinEquiv t) ((next.trans past).trans_lt cap)
  · intro t
    have j : (finProdFinEquiv t).val ≤ s.slots := (finProdFinEquiv t).isLt.le
    have end_ := Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right s.rows j) (s.start base))
      (2^Nat.clog 2 s.rows)
    exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt cap),end_⟩,Nat.le_pow_clog (by decide) _⟩

theorem reader_fits {base w : ℕ} (cap : s.endAddress base < 2^w) :
    ∀e∈s.readers base,e.Fits w (s.start base) := by
  intro e he
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
  have h := (s.room cap).2.1 (finProdFinEquiv.symm j)
  exact ⟨(s.room cap).1,⟨h.1.1,h.1.2.1,h.1.2.2.trans (Nat.le_add_right ..)⟩,trivial⟩

variable {w : ℕ}

theorem any (base : ℕ) (pages : s.Slot → Bank) (m : Memory w)
    (before : ∀t,(pages t).Fits w base) (cap : s.endAddress base < 2^w) :
    (s.phase base w pages).Runs m ∧ ∀i,i<base ∨ s.endAddress base≤ i→(s.phase base w pages).image m i=m i := by
  let lut := s.dictionary base
  let mid := DescentVenueSlabs.image s.venue (s.inputs pages) base m
  let tab := DescentStaticWordColumn.image lut.base s.word mid lut.size
  have len : (s.readers base).length=s.slots := List.length_ofFn
  have cut : s.start base+s.slots*s.rows ≤ s.endAddress base := Nat.le_add_right ..
  have top : s.start base < 2^w := ((Nat.le_add_right ..).trans cut).trans_lt cap
  have old : lut.base < 2^w := (Nat.le_add_right ..).trans_lt top
  have origin : base ≤ lut.base := by
    change base ≤ DescentVenueSlabs.endAddress s.venue base
    rw [DescentVenueSlabs.translates]; exact Nat.le_add_right ..
  obtain ⟨shift,frame⟩ := DescentVenueSlabs.any s.venue (s.inputs pages) base m (fun j=>before _) old
  have load : (DescentStaticWordColumn.program w lut.base s.word lut.size).Exec mid tab (4+10*lut.size) :=
    DescentStaticWordColumn.mount lut.base lut.size s.word mid top
  have scans : (ProtocolRAM.program w (s.passes base)).Exec tab (ProtocolRAM.result (s.passes base) tab)
      (ProtocolRAM.clock (s.passes base)) := columns_exec (s.readers base) tab (columns_safe (src:=s.start base) _ le_rfl
    (s.reader_fits cap) (by rw [len]; exact cut.trans_lt cap))
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then shift load) scans
      machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  intro i outside
  have held : i<s.start base ∨ s.start base+(s.readers base).length*s.rows ≤ i := by
    rw [len]
    rcases outside with low|hi
    · exact .inl ((low.trans_le origin).trans_le (Nat.le_add_right ..))
    · exact .inr (cut.trans hi)
  have saved : i<lut.base ∨ lut.base+lut.size≤ i := outside.imp (·.trans_le origin)
    (fun hi=>((show s.start base ≤ s.start base+s.slots*s.rows from Nat.le_add_right ..).trans cut).trans hi)
  exact (columns_frame (s.readers base) tab held).trans
    ((DescentStaticWordColumn.frame lut.base lut.size s.word mid i saved).trans
      (frame i (outside.imp_right (fun hi=>(show lut.base≤ s.start base from Nat.le_add_right ..).trans
        (((show s.start base≤ s.start base+s.slots*s.rows from Nat.le_add_right ..).trans cut).trans hi)))))


open private DescentSIMDLookup.bank_read from OAI.Hierarchy.DescentSIMDLookup

private theorem table_data {a b H G M : ℕ} (f : Cell a → Cell b) (empty : f 0=0)
    (v : Fin H → Fin G → Cell a) (p : Row H G M) :
    DescentSIMDLookup.table f (data v p) = data (fun h g=>f (v h g)) p := by
  unfold DescentSIMDLookup.table data
  rw [Equiv.symm_apply_apply]
  apply congrArg (encode b M)
  funext i
  by_cases live : p.2.val*M+i.val<G <;> simp [live,empty]

/-- Each full signed row remains readable at the new pitch, and the second bank contains
its marked outgoing neighbor. A partial final SIMD word has zero in each unused lane. -/
theorem issued (base : ℕ) (pages : s.Slot → Bank) (m : Memory w)
    (values : s.Slot → Fin s.hosts → Fin s.groups → Option (DescentSharedCableNames.Stage.Live s.degree s.cap))
    (before : ∀t,(pages t).Fits w base) (extent : ∀t,s.hosts*chunks s.groups s.sourceLanes≤(pages t).size)
    (read : ∀t,Reads (pages t) (fun h g=>DescentSignedCableCodec.encode (values t h g)) s.sourceLanes m)
    (live : 0<s.sourceLanes) (cap : s.endAddress base<2^w) :
    (s.phase base w pages).Runs m ∧
      ∀t, Reads (s.raw base t) (fun h g=>DescentSignedCableCodec.encode (values t h g)) s.targetLanes
          ((s.phase base w pages).image m) ∧
        Reads (s.bank base t) (fun h g=>DescentPacking.PackedMatch.Local.Stage.marked s.short (values t h g))
          s.targetLanes ((s.phase base w pages).image m) := by
  let lut := s.dictionary base
  let mid := DescentVenueSlabs.image s.venue (s.inputs pages) base m
  let tab := DescentStaticWordColumn.image lut.base s.word mid lut.size
  have len : (s.readers base).length=s.slots := List.length_ofFn
  have stop : lut.base ≤ s.start base := Nat.le_add_right ..
  have past : s.start base ≤ s.endAddress base := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have original := DescentVenueSlabs.run s.venue (s.inputs pages) base m
    (fun j h g=>DescentSignedCableCodec.encode (values (finProdFinEquiv.symm j) h g))
    (fun j=>before _) (fun j=>extent _) (fun j=>read _) live ((stop.trans past).trans_lt cap)
  have tableFit := (s.room cap).1
  refine ⟨(s.any base pages m before cap).1,?_⟩
  intro t
  let j : Fin s.slots := finProdFinEquiv t
  have rfit := (s.room cap).2.1 t
  have bits (p : Row s.hosts s.groups s.targetLanes) :
      tab ((s.raw base t).base+(row _ _ _ p).val) =
        ((data (fun h g=>DescentSignedCableCodec.encode (values t h g)) p).val:Word w) := by
    have bounded := (Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le rfit.2) _).trans_le rfit.1.2.2
    have originalRow := original.2.1 j p
    rw [show finProdFinEquiv.symm j=t from Equiv.symm_apply_apply _ t] at originalRow
    exact (DescentStaticWordColumn.frame lut.base lut.size s.word mid _ (.inl bounded)).trans originalRow
  constructor
  · intro p
    have low := (Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le rfit.2) _).trans_le rfit.1.2.2
    exact (columns_frame (s.readers base) tab (.inl (low.trans_le stop))).trans (bits p)
  · intro p
    let value := data (fun h g=>DescentSignedCableCodec.encode (values t h g)) p
    have jlt : j.val < (s.readers base).length := len.symm ▸ j.isLt
    have seen := columns_read (s.readers base) tab (src:=s.start base) le_rfl
      (s.reader_fits cap) j.val jlt (row _ _ _ p)
    have selected : (s.readers base)[j.val]'jlt = Expr.lookup lut (.lookup (s.raw base t) .row) := by
      simp only [readers,List.getElem_ofFn,Fin.eta]
      change Expr.lookup lut (.lookup (s.raw base (finProdFinEquiv.symm (finProdFinEquiv t))) .row) = _
      rw [Equiv.symm_apply_apply]
    rw [selected] at seen
    have below : value.val<lut.size := value.isLt
    have rawWord := (DescentSIMDLookup.bank_read (s.raw base t) tab (row _ _ _ p).val (s.dictionary base).base ((row _ _ _ p).isLt.trans_le rfit.2) rfit.1).trans (bits p)
    have encoded : (Expr.lookup lut (.lookup (s.raw base t) .row)).eval tab ((row _ _ _ p).val:Word w) =
        (s.word value.val:Word w) := by
      exact (congrArg (lut.read tab) rawWord).trans
        ((DescentSIMDLookup.bank_read lut tab value.val (s.start base) below tableFit).trans
          (DescentStaticWordColumn.read lut.base lut.size s.word mid below))
    have view := table_data (DescentPackedMatchSenderPins.table s.degree s.cap s.short)
      DescentPackedMatchSenderPins.empty (fun h g=>DescentSignedCableCodec.encode (values t h g)) p
    have castValue : (value.val:Cell (s.bits*s.targetLanes))=value := Fin.ext (Nat.mod_eq_of_lt value.isLt)
    have result : s.word value.val =
        (data (fun h g=>DescentPacking.PackedMatch.Local.Stage.marked s.short (values t h g)) p).val := by
      unfold word
      rw [castValue]
      simpa only [value,DescentPackedMatchSenderPins.table_at] using congrArg Fin.val view
    exact (seen.trans encoded).trans (congrArg (fun z:ℕ=>(z:Word w)) result)

end Layout
end
end Hierarchy.DescentResetSignedTokens

end OAI
