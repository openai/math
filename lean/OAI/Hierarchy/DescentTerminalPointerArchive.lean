import OAI.Hierarchy.DescentTerminalWholeRows
import OAI.Hierarchy.DescentTerminalPointerSource
import OAI.Hierarchy.DescentTerminalPointerPages
import OAI.Hierarchy.DescentPriorOperandTerminal
import OAI.Hierarchy.DescentTerminalSignedGrainWord
import OAI.Hierarchy.DescentTerminalMaskChannels

namespace OAI
/-! # The last native source is the preceding state, its signed wires and the two pin tables -/
namespace Hierarchy.DescentTerminalPointerDigits.Gather
open DescentSIMDLookup ProtocolRAM DescentOperandStateBanks DescentSharedCableNames DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {blocks groups H D cap N A d w : ℕ}

private theorem digit_low (width g m : ℕ) (small : width*(g+1)≤d) :
    digit width g (m%2^d)=digit width g m := by
  unfold digit
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow _ small)]

private theorem node_low (s : Widths) {K : ℕ} (packed : s.nodeCapacity=some K)
    (width n g m : ℕ) (small : (width*K)*(g+1)≤d) :
    s.nodeDigit width n g (m%2^d)=s.nodeDigit width n g m := by
  simp only [Widths.nodeDigit,packed,digit_low (width*K) g m small]

/-- The public-arity lookup reads its signed grains directly from the signed
panel at the original group and host. -/
theorem Pages.signed_panel (s : Pages blocks cap A) (mem : Memory w) (x : Fin blocks) (h : Fin H) (g : Fin groups)
    (fmt : Widths) (pin : ℕ→ℕ→ℕ→ℕ) (chips : Fin (2*cap)→Option (Stage.Live D cap))
    (sideSmall : DescentSignedCableCodec.width D cap*groups≤d)
    (signed : ∀j,DescentTerminalSignedGrainWord.wing D cap (s.signed j x) mem h g
      (Nat.zero_lt_of_lt g.isLt)=chips j) :
    (decode D fmt pin (s.source (N:=N) (d:=d) mem x h) g.val).chips=chips := by
  let pos:=Nat.zero_lt_of_lt g.isLt
  have addr:=at_whole groups pos h g
  funext j
  change DescentSignedCableCodec.decode D cap
    ((digit (DescentSignedCableCodec.width D cap) g.val ((mem ((s.address (N:=N) (scol j) x).atHost h)).val%2^d):ℕ):Cell _)=_
  rw [s.port]
  change DescentSignedCableCodec.decode D cap ((digit _ g.val ((mem ((s.signed j x).base+h.val)).val%2^d):ℕ):Cell _)=_
  rw [digit_low _ _ _ ((Nat.mul_le_mul_left _ g.isLt).trans sideSmall)]
  have k:=signed j
  have small:=DescentTerminalSignedGrainWord.digit_bound (DescentSignedCableCodec.width D cap) g.val
    (mem ((s.signed j x).base+h.val)).val
  have readChip :
      ((digit (DescentSignedCableCodec.width D cap) g.val (mem ((s.signed j x).base+h.val)).val : ℕ) :
        Cell (DescentSignedCableCodec.width D cap)) =
      DescentTerminalSignedGrainWord.chip (s.signed j x) mem h g pos := by
    apply Fin.ext
    simp only [DescentTerminalSignedGrainWord.chip, Fin.val_cast_of_lt small, addr.1, addr.2]
  exact (congrArg (DescentSignedCableCodec.decode D cap) readChip).trans k

/-- A real paid scalar and all its true operands use the old node-in-group
packing. The selected signed words use just the outer group digit. -/
theorem Pages.live (s : Pages blocks cap A) (mem : Memory w) (x : Fin blocks) (h : Fin H) (g : Fin groups)
    (fmt : Widths) {K : ℕ} (packed : fmt.nodeCapacity=some K) (t : CellInputs D cap N A)
    (nodeSmall : fmt.nodes*groups≤d) (aritySmall : (fmt.arity*K)*groups≤d)
    (fieldsSmall : ∀f,(fmt.pointer f*K)*groups≤d) (sideSmall : DescentSignedCableCodec.width D cap*groups≤d)
    (nodes : digit fmt.nodes g.val (mem ((s.population x).base+h.val)).val=t.n)
    (arity : ∀u : Fin N,u.val<t.n→ fmt.nodeDigit fmt.arity u.val g.val (mem ((s.arity x).base+h.val)).val=t.arity u)
    («fields» : ∀i : Fin (N*A),t.active i→∀f,let j:=((finProdFinEquiv (m:=N) (n:=A)).symm i).2
      fmt.nodeDigit (fmt.pointer f) (nodeOf i).val g.val (mem ((s.pointers f j x).base+h.val)).val=(t.pointer i).header f)
    (signed : ∀j,DescentTerminalSignedGrainWord.wing D cap (s.signed j x) mem h g
      (Nat.zero_lt_of_lt g.isLt)=t.chips j) :
    SourceRead fmt (s.source (d:=d) mem x h) g.val t := by
  let pos:=Nat.zero_lt_of_lt g.isLt
  have addr:=at_whole groups pos h g
  refine ⟨?_,?_,?_,?_⟩
  · change digit fmt.nodes g.val ((mem ((s.address (N:=N) ncol x).atHost h)).val%2^d)=_
    rw [(s.fixed (N:=N) x).1]
    exact (digit_low _ _ _ ((Nat.mul_le_mul_left _ g.isLt).trans nodeSmall)).trans nodes
  · intro u hu
    change fmt.nodeDigit fmt.arity u.val g.val ((mem ((s.address (acol u) x).atHost h)).val%2^d)=_
    rw [s.node]
    exact (node_low fmt packed _ _ _ _ ((Nat.mul_le_mul_left _ g.isLt).trans aritySmall)).trans (arity u hu)
  · intro i hi f
    change fmt.nodeDigit (fmt.pointer f) (nodeOf i).val g.val ((mem ((s.address (pcol f i) x).atHost h)).val%2^d)=_
    rw [s.pointer]
    exact (node_low fmt packed _ _ _ _ ((Nat.mul_le_mul_left _ g.isLt).trans (fieldsSmall f))).trans («fields» i hi f)
  · exact congrFun (s.signed_panel (N:=N) mem x h g fmt (fun _ _ j=>j) t.chips sideSmall signed)
/-- Specialization of the prior history's all-pages receipt. The actual nested
node digit, including the original immutable copy stamp, is used verbatim. -/
theorem Pages.archived_field (s : Pages blocks cap A) (mem : Memory w) (x : Fin blocks) (h : Fin H) (g : Fin groups)
    (fmt : Widths) {K : ℕ} (packed : fmt.nodeCapacity=some K) (f : Fin 4) (arg : Fin A)
    (values : Fin H→ Fin groups→ Cell (fmt.pointer f*K)) (stored : Reads (s.pointers f arg x) values groups mem)
    (fits : (fmt.pointer f*K)*groups≤w) (i : Fin K) (value : Cell (fmt.pointer f))
    (actual : (encode _ K).symm (values h g) i=value) :
    fmt.nodeDigit (fmt.pointer f) i.val g.val (mem ((s.pointers f arg x).base+h.val)).val=value.val := by
  let pos:=Nat.zero_lt_of_lt g.isLt
  have addr:=at_whole groups pos h g
  simpa only [addr.1,addr.2] using Widths.nodeDigit_of_stored fmt packed _ values mem stored fits pos h g i value actual


end
end Hierarchy.DescentTerminalPointerDigits.Gather

end OAI
