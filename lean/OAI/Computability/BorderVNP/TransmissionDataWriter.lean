import OAI.Computability.BorderVNP.TransmissionSources
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Lowering a packed literal or pin demand to a physical transmission record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission.DataWriter

open VPVNP.BurstRAM Packing.Directory
open DiagonalResidueRAM (word)
open Packing.Directory.ISA (pushWords)

/-- Values loaded from the common public frame. -/
structure Layout where
  /-- Width and locations of the physical processor inputs. -/
  pins : Pins.Layout
  /-- Base of the seven-column delivery demands. -/
  input : ℕ
  /-- Number of populated demand rows. -/
  count : ℕ
  /-- First transmission descriptor address. -/
  output : ℕ
  /-- Two words per cell giving its owner and absolute input bank base. -/
  owners : ℕ

/-- Read the actual public dimensions and both table bases. -/
def layout (pub : Arg → ℕ) (mem : ℕ → ℕ) : Layout :=
  let f := frameField pub mem
  ⟨⟨f 0,f 1,f 2,f 3,f 4,f 23,f 21,f 22,f 24⟩,f 8,f 9,f 12,f 72⟩

/-- Read one populated raw delivery row from the demand writer. -/
def demandAt (mem : ℕ → ℕ) (a : ℕ) : Row :=
  ⟨mem a,mem (a+1),mem (a+2),mem (a+3),mem (a+4),mem (a+5),mem (a+6)⟩

/-- Resolve both cell directory words, preserving the natural source and within-cell
slot. In particular an extra-field source points to the prepared substitution array. -/
def record (d : Layout) (mem : ℕ → ℕ) (r : Row) : List ℕ :=
  let a := d.owners+r.cell*2
  [1,r.team,mem a,r.width,r.sourceBase d.pins,0,mem (a+1)+r.slot]

/-- Decode the frame and establish the immutable constants, source stride and cursors.
Register 10 counts rows; register 20 points to the next seven output words. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 7,
  readFrame 4 62 63 8, readFrame 5 62 63 9, readFrame 6 62 63 72, readFrame 7 62 63 3,
  readFrame 8 62 63 21, readFrame 9 62 63 1, readFrame 11 62 63 4,
  .binary .sub 9 9 1, .binary .mul 9 9 11, .binary .add 9 7 9, .binary .add 9 9 7,
  .copy 10 0, readFrame 20 62 63 12]

/-- Select the actual source address, then look up the receiver's team and bank. -/
def compute : Code := .block [
  .binary .mul 30 10 3, .binary .add 30 4 30,
  popWord 22 30, popWord 23 30, popWord 24 30, popWord 25 30, popWord 26 30,
  popWord 27 30, .load 28 30,
  .binary .mul 30 26 2, .binary .add 30 6 30, .load 29 30, .binary .add 30 30 1,
  .load 31 30, .binary .add 31 31 27,
  .ifEq 24 0 (.binary .mul 32 23 9)
    (.seq (.binary .mul 32 23 7) (.binary .add 32 8 32)),
  .binary .add 32 32 25]

/-- Emitted columns, in the physical scheduler's order. -/
def columns : List Reg := [1,22,29,28,32,0,31]

/-- Lower one descriptor and advance to the next raw row. -/
def step : Code := .block [compute,pushWords columns,.binary .add 10 10 1]

/-- Fill the initial data rows and publish their count before shared rows append. -/
def program : Code := .block [setup, .whileLt 10 5 step, writeFrame 5 62 63 13]

/-- The low registers of the data writer at the beginning of row `i`. -/
structure Prepared (d : Layout) (i : ℕ) (s : Reg → ℕ) : Prop where
  /-- The four physical literal constants. -/
  constants : s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 2 ∧ s 3 = 7
  /-- Input records, count and cell-owner directory. -/
  input : s 4 = d.input ∧ s 5 = d.count ∧ s 6 = d.owners
  /-- Literal, substitution base and complete processor stride. -/
  source : s 7 = d.pins.literal ∧ s 8 = d.pins.ibase ∧ s 9 = d.pins.stride
  /-- The current demand index. -/
  index : s 10 = i
  /-- The next emitted record begins at this word address. -/
  cursor : s 20 = d.output+i*7

/-- Unbounded arithmetic evaluation of initialization. -/
theorem setup_eval (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    Prepared (layout pub mem) 0 (setup.evalNat pub mem s) := by
  constructor <;> simp (config := {decide := true}) [setup,layout,Code.block,Code.evalNat,readFrameFixed,
    Pins.Layout.stride,Pins.Layout.offset,addressOp]

/-- Numeric word room for the setup's reached address and stride instructions. -/
theorem setup_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (fitted : pub 0+72 < 2^w) (teams : 0 < (layout pub mem).pins.teams)
    (stride : (layout pub mem).pins.stride < 2^w) :
    setup.safeReadOnly w pub mem s := by
  simp (config := {decide := true}) [setup,Code.block,Code.safeReadOnly,Code.evalNat,readFrame,
    addressOp,addressOpFits]
  simp only [layout, Pins.Layout.stride, Pins.Layout.offset, frameField] at stride teams
  have hw : w ≠ 0 := by rintro rfl; simp at fitted
  repeat' apply And.intro
  all_goals first | exact hw | omega

/-- The concrete registers contain exactly the seven mathematical transmission columns. -/
theorem compute_eval {d : Layout} {i : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (h : Prepared d i s) : columns.map (compute.evalNat pub mem s) =
      record d mem (demandAt mem (d.input+i*7)) := by
  obtain ⟨⟨z,u,two,seven⟩,⟨input,_,owners⟩,⟨lit,sub,stride⟩,idx,_⟩ := h
  by_cases literal : mem (d.input+i*7+2) = 0 <;>
    simp only [Nat.add_assoc] at literal <;>
    simp (config := {decide := true}) [columns,compute,popWord,Code.block,Code.evalNat,addressOp,
      z,u,two,seven,input,owners,lit,sub,stride,idx,demandAt,record,Row.sourceBase,
      Nat.add_assoc, literal]

/-- The four genuine scalar bounds for decoding one row. The input table and the
two owner words, the source sum and the destination sum all fit their words. -/
structure RowFits (w : ℕ) (d : Layout) (mem : ℕ → ℕ) (i : ℕ) : Prop where
  /-- The last of the seven input words is addressable. -/
  input : d.input+i*7+6 < 2^w
  /-- Both words of the owner directory entry fit. -/
  owner : d.owners+(demandAt mem (d.input+i*7)).cell*2+1 < 2^w
  /-- Adding the within-cell slot to the absolute bank base fits. -/
  destination : let r := demandAt mem (d.input+i*7)
                mem (d.owners+r.cell*2+1)+r.slot < 2^w
  /-- The literal or substituted-pin address fits. -/
  source : (demandAt mem (d.input+i*7)).sourceBase d.pins < 2^w

/-- The native read-only computation has no wrapped arithmetic on a fitted row. -/
theorem compute_safe {w : ℕ} {d : Layout} {i : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (h : Prepared d i s) (fit : RowFits w d mem i) : compute.safeReadOnly w pub mem s := by
  obtain ⟨⟨z,u,two,seven⟩,⟨input,_,owners⟩,⟨lit,sub,stride⟩,idx,_⟩ := h
  obtain ⟨raw,own,dst,src⟩ := fit
  by_cases literal : mem (d.input+i*7+2) = 0 <;>
    simp only [Nat.add_assoc] at literal <;>
    simp [demandAt, Row.sourceBase, Nat.add_assoc, literal] at own dst src <;>
    simp (config := {decide := true}) [compute,popWord,Code.block,Code.evalNat,Code.safeReadOnly,
      addressOp,addressOpFits,z,u,two,seven,input,owners,lit,sub,stride,idx,Nat.add_assoc,literal] <;> omega

end RoutingISA.Transmission.DataWriter

end BorderVNP
end Computability
end OAI
