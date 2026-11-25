import OAI.Hierarchy.ProtocolRAMGateDirectory
import OAI.Hierarchy.ProtocolRAMPurchaseGateShape

namespace OAI
/-! # Runtime materialization of the mark tape from dynamically generated DFS tile columns -/

namespace Hierarchy.ProtocolRAMPurchaseGateColumns

open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.GateColumns
open ProtocolRAMPurchaseGateShape
open scoped Fin.CommRing

abbrev gates (R H : ℕ) := R*(4*H+3)

/-- Shape depends on the controller parameters, the public gate ordinal and the
column number. Runtime labels have no role in the six advice columns. -/
def spec {R H : ℕ} (tiles work first : ℕ) (g : Fin (gates R H)) (c : Fin 3) : Operand :=
  match (shapeAt tiles work first g).field c with
  | .literal n => .literal n
  | .stock pos => .tile (pos.val*R+(candidate g).val)

/-- The physical DFS layout, with one live candidate column per position. -/
def TileRows {w R H tiles : ℕ} (source : Bank) (rows : Fin R → Fin H → Fin tiles) (m : Memory w) : Prop :=
  ∀ i j, m (source.base+(j.val*R+i.val)) = ((rows i j).val : Word w)

/-- The complete gate recipe for fixed controller parameters fits in a linearly
sized ordinary public list. -/
def staticAdvice (R H tiles work first dirBase : ℕ) :=
  adviceWords (directory dirBase (gates R H)) (spec (R := R) (H := H) tiles work first)

theorem staticAdvice_size (R H tiles work first dirBase : ℕ) :
    (staticAdvice R H tiles work first dirBase).length ≤ 12*(gates R H+1) := by
  simpa [staticAdvice] using directory_space dirBase (gates R H)

def code (w R H : ℕ) (source : Bank) (D : Directory) (work base : ℕ) :=
  program w (passes source D work (gates R H) base)

def output {w : ℕ} (R H : ℕ) (source : Bank) (D : Directory) (work base : ℕ) (m : Memory w) :=
  result (passes source D work (gates R H) base) m

private theorem bounded {R H : ℕ} (tiles work first : ℕ) (source : Bank) (size : H*R ≤ source.size)
    (i : Fin (gates R H)) (c : Fin 3) (a : ℕ) (hit : spec tiles work first i c = .tile a) :
    a < source.size := by
  cases hf : (shapeAt tiles work first i).field c with
  | literal n => simp [spec,hf] at hit
  | stock j =>
    have eq : j.val*R+(candidate i).val=a := by simpa [spec,hf] using hit
    have next := Nat.mul_le_mul_right R j.isLt
    rw [Nat.succ_mul] at next
    have hi := (candidate i).isLt
    omega

private theorem value {w R H tiles : ℕ} (source : Bank) (rows : Fin R → Fin H → Fin tiles)
    (m : Memory w) (raw : TileRows source rows m) (work first : ℕ) (i : Fin (gates R H)) (c : Fin 3) :
    (spec tiles work first i c).value source work m =
      (((shapeAt tiles work first i).field c).eval work (rows (candidate i)) : Word w) := by
  unfold spec
  cases hf : (shapeAt tiles work first i).field c with
  | literal n => rfl
  | stock pos =>
    simp [Operand.value,Field.eval,Nat.cast_add]
    exact raw (candidate i) pos

/-- Each native output word is precisely the corresponding operand of the gate
obtained from the selected runtime candidate and position. -/
theorem packed {w R H tiles : ℕ} (source : Bank) (D : Directory) (work first base : ℕ)
    (rows : Fin R → Fin H → Fin tiles) (m : Memory w) (raw : TileRows source rows m)
    (advice : Mounted D (spec (R := R) (H := H) tiles work first) m) (width : 0<w)
    (size : H*R ≤ source.size) (hs : source.Fits w base) (hd : ∀ j, j<6 → (D.bank j).Fits w base) :
    MarkTape.Packed base (MarkTape.compilePaths tiles work first (List.ofFn (fun i => List.ofFn (rows i))))
      (output R H source D work base m) := by
  have words (i : Fin (gates R H)) (c : Fin 3) :=
    (GateColumns.read source D work base (spec tiles work first) m advice width hs hd
      (bounded tiles work first source size) i c).trans (value source rows m raw work first i c)
  rw [compilePaths_eq_ofFn]
  intro i
  let j : Fin (gates R H) := Fin.cast (by simp [gates]) i
  have jval : j.val=i.val := Fin.val_cast _ _
  have atRow := And.intro (words j 0) (And.intro (words j 1) (words j 2))
  simp only [jval] at atRow
  simp only [List.get_ofFn,List.length_ofFn]
  simpa [output,Shape.eval,Shape.field,j,gates,Fin.val_cast] using atRow

private theorem code_cheap (w R H : ℕ) (source : Bank) (D : Directory) (work base : ℕ) :
    CheapCode (code w R H source D work base) := by
  unfold code
  generalize passes source D work (gates R H) base = ps
  exact @program_cheap w ps

set_option maxHeartbeats 1500000 in
/-- Link the compiler directly after a DFS controller whose live memory already contains
the fixed shape directory. This form requires no remounting at the phase boundary. -/
theorem execute {w R H tiles : ℕ} (source : Bank) (D : Directory) (work first base : ℕ)
    (rows : Fin R → Fin H → Fin tiles) (m : Memory w) (raw : TileRows source rows m)
    (dir : Mounted D (spec (R := R) (H := H) tiles work first) m)
    (width : 0<w) (size : H*R ≤ source.size) (hs : source.Fits w base)
    (hd : ∀ j, j<6 → (D.bank j).Fits w base) (room : base+3*gates R H<2^w) :
    let m' := output R H source D work base m
    let ticks := clock (passes source D work (gates R H) base)
    (code w R H source D work base).Exec m m' ticks ∧
      MarkTape.Packed base (MarkTape.compilePaths tiles work first (List.ofFn (fun i => List.ofFn (rows i)))) m' ∧
      CheapCode (code w R H source D work base) ∧ ticks ≤ 16+3*gates R H*64 ∧
      ∀ a, (a<base ∨ base+3*gates R H≤a) → m' a=m a := by
  dsimp only
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  · exact @GateColumns.run w (gates R H) source D work base m hs hd room
  · exact packed source D work first base rows m raw dir width size hs hd
  · exact @code_cheap w R H source D work base
  · exact GateColumns.ticks (gates R H) source D work base
  · exact fun a ha=>GateColumns.frame (gates R H) source D work base m a ha

/-- Starting from only runtime DFS values and the explicit fixed shape tape, this
single cheap native program writes all three gate columns in fixed linear time. -/
theorem from_advice {w R H tiles : ℕ} (source : Bank) (D : Directory) (work first base : ℕ)
    (rows : Fin R → Fin H → Fin tiles) (m : Memory w) (raw : TileRows source rows m)
    (width : 0<w) (size : H*R ≤ source.size) (cap : gates R H ≤ D.stride)
    (sourceBeforeShape : source.base+source.size≤D.base)
    (shapeBeforeOut : D.base+6*D.stride≤base) (room : base+3*gates R H<2^w) :
    let s := mount D (spec (R := R) (H := H) tiles work first) m
    let m' := output R H source D work base s
    let ticks := clock (passes source D work (gates R H) base)
    (code w R H source D work base).Exec s m' ticks ∧
      MarkTape.Packed base (MarkTape.compilePaths tiles work first (List.ofFn (fun i => List.ofFn (rows i)))) m' ∧
      CheapCode (code w R H source D work base) ∧ ticks ≤ 16+3*gates R H*64 ∧
      ∀ a, (a<base ∨ base+3*gates R H≤a) → m' a=s a := by
  let s : Memory w := mount D (spec (R := R) (H := H) tiles work first) m
  have hs : source.Fits w base := ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have hd (j : ℕ) (hj : j<6) : (D.bank j).Fits w base := by
    have endBound := Nat.mul_le_mul_right D.stride hj
    rw [Nat.succ_mul] at endBound
    exact ⟨Nat.two_pow_pos _,by change D.stride<2^w; omega,by
      change D.base+j*D.stride+D.stride≤base; omega⟩
  have live : TileRows source rows s := by
    intro i j
    have endBound := Nat.mul_le_mul_right R j.isLt
    rw [Nat.succ_mul] at endBound
    have hi := i.isLt
    exact (mount_frame _ _ _ (Or.inl (by omega))).trans (raw i j)
  exact execute source D work first base rows s live (mount_mounted D _ _ cap (by omega))
    width size hs hd room

/-- Consecutive regions place the fixed advice after the live tile bank, then the
three gate columns, then the mark interpreter's workspace. -/
def shapeDirectory (source : Bank) (R H : ℕ) := directory (source.base+source.size) (gates R H)

def packedBase (source : Bank) (R H : ℕ) :=
  (shapeDirectory source R H).base+6*(shapeDirectory source R H).stride

def markBase (source : Bank) (R H : ℕ) := packedBase source R H+3*gates R H

theorem markBase_le (source : Bank) (R H : ℕ) :
    markBase source R H ≤ source.base+source.size+15*(gates R H+1) := by
  have bound := directory_space (source.base+source.size) (gates R H)
  change source.base+source.size+6*(directory (source.base+source.size) (gates R H)).stride+
    3*gates R H ≤ _
  omega

/-- A single final address bound suffices to compile the actual tape at the
canonical consecutive addresses and to put its final word below the mark workspace. -/
theorem canonical {w R H tiles : ℕ} (source : Bank) (first : ℕ)
    (rows : Fin R → Fin H → Fin tiles) (m : Memory w) (raw : TileRows source rows m)
    (width : 0<w) (size : H*R ≤ source.size) (room : markBase source R H+4+tiles+first+R<2^w) :
    let D := shapeDirectory source R H
    let base := packedBase source R H
    let work := markBase source R H
    let s := mount D (spec (R := R) (H := H) tiles work first) m
    let m' := output R H source D work base s
    let ticks := clock (passes source D work (gates R H) base)
    (code w R H source D work base).Exec s m' ticks ∧
      MarkTape.Packed base (MarkTape.compilePaths tiles work first (List.ofFn (fun i => List.ofFn (rows i)))) m' ∧
      CheapCode (code w R H source D work base) ∧ ticks ≤ 16+3*gates R H*64 ∧
      ∀ a, (a<base ∨ base+3*gates R H≤a) → m' a=s a := by
  apply from_advice source _ _ first _ rows m raw width size
    (directory_capacity _ _) le_rfl le_rfl
  change markBase source R H < 2^w
  omega


end Hierarchy.ProtocolRAMPurchaseGateColumns

end OAI
