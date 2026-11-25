import OAI.Hierarchy.DescentTerminalLeafFold
import OAI.Hierarchy.DescentTerminalHeaderScatter
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # Defined cheap scalar print memory on every selector, including rejected ones -/
namespace Hierarchy.DescentTerminalLeafFold
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM DescentTerminalHeaderScatter
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}
def selected (L : Layout) (m : Memory w) (pool n : ℕ) :=
  actual (n:=n) (low L) (high L) (cleared L pool m)
def reduced (L : Layout) (m : Memory w) (pool n src : ℕ) :=
  ProtocolRAMWeightedScatter.image (fun i=>(selected L m pool n i).1.val)
    (fun i=>(selected L m pool n i).2.val) (staged L pool n src m) n
def final (L : Layout) (m : Memory w) (pool n src out : ℕ) :=
  image out pool (lookup L) (reduced L m pool n src)

theorem any (L : Layout) (m : Memory w) (src out pool n : ℕ) (pos : 0<w)
    (fit : L.cells.Fits w src) (range : pool+1 ≤ L.cells.size) (early : L.lanes.Fits w L.cells.base)
    (ready : (row L).Fits w src) (resultFits : (lookup L).Fits w out) (room : src+2*n<2^w)
    (endAt : out+pool<2^w) (static : ∀(i : Fin n) (j:Fin 2),L.lanes.read m ((field i j).val:Word w)=(j.val:Word w)) :
    (program w src pool n out L).Exec m (final L m pool n src out) (work L pool n) ∧ CheapCode (program w src pool n out L) := by
  let clear:=cleared L pool m
  let dest (i : Fin n):=(selected L m pool n i).1.val
  let amount (i : Fin n):=(selected L m pool n i).2.val
  have endCells:=fit.2.2
  have srcFit : src<2^w:=by omega
  have init:=@scan_exec w L.cells.base (pool+1) (.lit 0) m trivial (by omega)
  have write:=@scan_exec w src (2*n) (row L) clear ready room
  have bank (i : Fin n) (j : Fin 2) : L.lanes.read clear ((field i j).val:Word w)=(j.val:Word w) := by
    let x : Word w:=(field i j).val
    have lowAddr : L.lanes.base+x.val%L.lanes.size<L.cells.base :=
      (Nat.add_lt_add_left (Nat.mod_lt x.val early.1) L.lanes.base).trans_le early.2.2
    exact (DescentTerminalChipRuntime.image_low m L.cells.base (pool+1) (.lit 0) lowAddr).trans (static i j)
  have safe (i : Fin n) : dest i<src := by
    change ((bounded L.cells (address L)).eval clear ((field i 0).val:Word w)).val<src
    rw [bounded_val L.cells (address L) _ _ fit srcFit]
    have:=Nat.mod_lt ((address L).eval clear ((field i 0).val:Word w)-(L.cells.base:Word w)).val fit.1
    omega
  have stagedAt (i : Fin n) (j : Fin 2) : staged L pool n src m (src+(field i j).val)=
      if j=0 then (dest i:Word w) else (amount i:Word w) := by
    rw [staged,DescentTerminalDenseHeaderRAM.at_image src (row L) clear (field i j)]
    change (stage (low L) (high L) L.lanes).eval clear ((field i j).val:Word w)=_
    rw [lane_read _ _ _ _ _ _ pos (bank i j)]
    fin_cases j <;> simp [selected,dest,amount,actual,clear,Fin.cast_val_eq_self]
  have replay:=@ProtocolRAMWeightedScatter.run w n src dest amount (staged L pool n src m) room.le
    (fun i=>(safe i).trans srcFit) (fun i=>Or.inl (safe i))
    (fun i=>⟨by simpa [field] using stagedAt i 0,by simpa [field,Nat.add_assoc] using stagedAt i 1⟩)
  have print:=@scan_exec w out pool (lookup L) (reduced L m pool n src) resultFits endAt
  exact ⟨@scans w L src pool n out m clear (staged L pool n src m) (reduced L m pool n src)
    (final L m pool n src out) init write replay print,@cheap w src pool n out L⟩

theorem before (L : Layout) (m : Memory w) (src out pool n : ℕ)
    (fit : L.cells.Fits w src) (endAt : src<2^w) (later : src≤out)
    {j : ℕ} (early : j<L.cells.base) : final L m pool n src out j=m j := by
  have endCells:=fit.2.2
  have hsrc : j<src:=by omega
  have hout : j<out:=by omega
  have safe (i : Fin n) : (selected L m pool n i).1.val≠j := by
    change ((bounded L.cells (address L)).eval (cleared L pool m) ((field i 0).val:Word w)).val≠j
    rw [bounded_val L.cells (address L) _ _ fit endAt]
    omega
  calc
    final L m pool n src out j = reduced L m pool n src j :=
      DescentTerminalChipRuntime.image_low _ out pool (lookup L) hout
    _ = staged L pool n src m j := ProtocolRAMWeightedScatter.frame
      (fun i=>(selected L m pool n i).1.val) (fun i=>(selected L m pool n i).2.val)
      (staged L pool n src m) n j safe
    _ = cleared L pool m j := DescentTerminalChipRuntime.image_low _ src (2*n) (row L) hsrc
    _ = m j := DescentTerminalChipRuntime.image_low m L.cells.base (pool+1) (.lit 0) early

theorem physical (L : Layout) (m : Memory w) (src out pool n : ℕ) {budget : ℕ} {product : Memory w→Prop}
    (reached : (program w src pool n out L).Exec m (final L m pool n src out) (work L pool n))
    (truth : ∃a,(program w src pool n out L).Exec m a budget ∧ product a) :
    product (final L m pool n src out) :=
  @actual_after w (program w src pool n out L) m (final L m pool n src out) (work L pool n)
    budget product reached truth

end
end Hierarchy.DescentTerminalLeafFold

end OAI
