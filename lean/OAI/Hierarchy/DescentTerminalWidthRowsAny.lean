import OAI.Hierarchy.DescentTerminalWidthRowsHardware
import OAI.Hierarchy.DescentTerminalHeaderAny

namespace OAI
/-! # Deterministic execution and retained memory for arbitrary terminal width counts -/
namespace Hierarchy.DescentTerminalWidthRowsRAM.Layout
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPrimitiveArena
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

variable (L : Layout) (q p w : ℕ)

def boot (m : Memory w) := DescentStaticWordColumn.image L.origin (L.literal q p) m L.entries
def sums (m : Memory w) := DescentTerminalHeaderPrefixRAM.result L.prefix.base L.groups .add L.rank (L.boot q p w m)
def filled (m : Memory w) := ProtocolRAM.image L.output.base L.rows (L.fill q p) (L.sums q p w m)
def actualAddr (m : Memory w) (i : Fin L.groups) := (L.dest.eval (L.filled q p w m) (i.val : Word w)).val
def actualData (m : Memory w) (i : Fin L.groups) := L.datum.eval (L.filled q p w m) (i.val : Word w)
def finalMem (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image L.addresses L.words L.dest L.datum (L.actualAddr q p w m)
    (L.actualData q p w m) (L.filled q p w m)

private theorem target_bounds (m : Memory w) (i : Word w) (fit : L.output.Fits w L.addresses)
    (top : L.stop<2^w) :
    L.output.base ≤ (L.dest.eval m i).val ∧ (L.dest.eval m i).val≤L.sink := by
  have endAt : L.addresses < 2^w := by change L.addresses+L.groups+L.groups<2^w at top;omega
  have lim : L.sink<2^w := (Nat.lt_succ_self L.sink).trans endAt
  have splitDest : L.dest.eval m i=(L.sink:Word w) ∨
      L.dest.eval m i=(DescentTerminalHeaderScatter.bounded L.output L.rawDest).eval m i := by
    unfold dest
    simp only [Expr.eval]
    by_cases h : DescriptorExpr.Comparison.eq.test (L.rank.eval m i) (0 : Word w) = true
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  rcases splitDest with zero|bounded_
  · rw [zero,Fin.val_cast_of_lt lim]
    exact ⟨Nat.le_add_right ..,le_rfl⟩
  · rw [bounded_,DescentTerminalHeaderScatter.bounded_val _ _ _ _ fit endAt]
    have lt_ := Nat.mod_lt (((L.rawDest.eval m i)-(L.output.base:Word w)).val) fit.1
    unfold sink
    omega

theorem exec_any (m : Memory w) (source : L.source.Fits w L.origin) (room : L.stop<2^w) :
    (L.program q p w).Exec m (L.finalMem q p w m) (L.clocks q p) ∧ CheapCode (L.program q p w) := by
  have fit:=L.fits q p w source room
  let rom := DescentStaticWordColumn.program w L.origin (L.literal q p) L.entries
  let counts := DescentTerminalHeaderPrefixRAM.program w L.prefix.base L.groups .add L.rank
  let fillScan := scan w L.output.base L.rows (L.fill q p)
  let writes := ProtocolRAMGeneratedWrite.program w L.addresses L.words L.groups L.dest L.datum
  have rent:=@DescentStaticWordColumn.mount w L.origin L.entries (L.literal q p) m fit.installEnd
  have count_:=@DescentTerminalHeaderPrefixRAM.exec_any w L.prefix.base L.groups .add L.rank (L.boot q p w m)
    trivial fit.rank fit.prefixEnd
  have init:=@scan_exec w L.output.base L.rows (L.fill q p) (L.sums q p w m) fit.fill fit.outputEnd
  have bound (i : Fin L.groups) : L.actualAddr q p w m i < L.addresses :=
    (target_bounds L w (L.filled q p w m) (i.val:Word w) fit.output room).2.trans_lt (Nat.lt_succ_self L.sink)
  have write_:=@ProtocolRAMGeneratedWrite.run w L.groups L.addresses L.words L.dest L.datum
    (L.actualAddr q p w m) (L.actualData q p w m) (L.filled q p w m) fit.dest fit.datum fit.columns fit.limit
    (fun i=>by simp [actualAddr,Fin.cast_val_eq_self]) (fun _=>rfl)
    (fun i=>(L.dest.eval (L.filled q p w m) (i.val:Word w)).isLt)
    (fun i j=>by have:=bound j;omega)
    (fun i j=>by have:=bound j; have lo : L.addresses≤L.words:=Nat.le_add_right ..;omega)
  have romCounts := @Procedure.Exec.then w rom counts m (L.boot q p w m) (L.sums q p w m)
    _ _ (@rent) (@count_)
  have throughFill := @Procedure.Exec.then w (rom.seq counts) fillScan m (L.sums q p w m)
    (L.filled q p w m) _ _ (@romCounts) (@init)
  refine ⟨?_, L.cheap q p w⟩
  exact @Procedure.Exec.then w ((rom.seq counts).seq fillScan) writes m (L.filled q p w m)
    (L.finalMem q p w m) _ _ (@throughFill) (@write_)

/-- All later passes leave both immutable lookup tables and the preceding geometry intact.
The same statement also covers addresses just past the sparse scratch columns. -/
theorem after_boot (m : Memory w) (source : L.source.Fits w L.origin) (room : L.stop<2^w) (j : ℕ)
    (away : j<L.prefix.base ∨ L.stop≤j) : L.finalMem q p w m j=L.boot q p w m j := by
  have fit:=L.fits q p w source room
  have groupsRoom : L.groups≤L.prefix.size := covered _
  have rowsRoom : L.rows≤L.output.size := covered _
  have b0 : L.prefix.base+L.prefix.size=L.output.base:=rfl
  have b1 : L.output.base+L.output.size=L.sink:=rfl
  have b2 : L.sink+1=L.addresses:=rfl
  have b3 : L.addresses+L.groups=L.words:=rfl
  have b4 : L.words+L.groups=L.stop:=rfl
  have clear (i : Fin L.groups) : j≠L.actualAddr q p w m i := by
    have h:=target_bounds L w (L.filled q p w m) (i.val:Word w) fit.output room
    change L.output.base≤L.actualAddr q p w m i ∧ L.actualAddr q p w m i≤L.sink at h
    omega
  have keep:=ProtocolRAMGeneratedWrite.frame L.addresses L.words L.dest L.datum
    (L.actualAddr q p w m) (L.actualData q p w m) (L.filled q p w m) j clear (by omega) (by omega)
  have init:=ProtocolRAMGeneratedWrite.frame_image L.output.base L.rows (L.fill q p) (L.sums q p w m) j (by omega)
  apply (keep.trans init).trans
  have outside : ¬(L.prefix.base ≤ j ∧ j < L.prefix.base+L.groups) := by omega
  simp [sums,DescentTerminalHeaderPrefixRAM.result,fillSegment,outside]

theorem frame_any (m : Memory w) (source : L.source.Fits w L.origin) (room : L.stop<2^w) (j : ℕ)
    (away : j<L.origin ∨ L.stop≤j) : L.finalMem q p w m j=m j := by
  have org : L.origin≤L.prefix.base := Nat.le_add_right ..
  have endTable : L.origin+L.entries = L.prefix.base := rfl
  have rest : L.prefix.base≤L.stop := by
    change L.prefix.base ≤ L.prefix.base+L.prefix.size+L.output.size+1+L.groups+L.groups
    omega
  exact (L.after_boot q p w m source room j (by omega)).trans
    (DescentStaticWordColumn.frame L.origin L.entries (L.literal q p) m j (by omega))


end
end Hierarchy.DescentTerminalWidthRowsRAM.Layout

end OAI
