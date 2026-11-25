import OAI.Computability.BorderVNP.CubeISAHeaderDecodeStep

/-! # Installing the compact decoder from the actual primary and secondary frames -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderDecode

open VPVNP.BurstRAM Cube.DeclarationBits

/-- Meaning of the static words read by the compact header program. The source
starts one word past the branch bit and the specified number of epoch bits. -/
structure AtFrame (l : Layout) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Frame 63 supplies the secondary header pointer. -/
  header : frameField pub mem 63 = l.header
  /-- Frame 59 supplies the grouping alphabet. -/
  d : frameField pub mem 59 = l.d
  /-- Actual common-header bit location after the epoch words. -/
  source : frameField pub mem 25 + 1 + mem (l.header+9) = l.source
  /-- Static claimed table base. -/
  dense : mem (l.header+1) = l.dense
  /-- Static dense table length. -/
  entries : mem (l.header+2) = l.entries
  /-- Static totals table base. -/
  totals : mem (l.header+3) = l.totals
  /-- Direction count. -/
  dimension : mem (l.header+4) = l.a
  /-- Width of the coordinate field. -/
  cw : mem (l.header+10) = l.cw
  /-- Width of each subtotal field. -/
  rw : mem (l.header+11) = l.rw
  /-- Public cap of every subtotal. -/
  cap : mem (l.header+12) = l.cap

/-- State at the first coordinate bit, before any external header field is decoded. -/
structure Initial (l : Layout) (old : ℕ → ℕ) (z : NatState) : Prop where
  /-- All persistent dimensions and pointers are loaded from the physical frames. -/
  fixed : Static l z.reg
  /-- Initially no dense field is processed. -/
  cursor : z.reg 23 = 0
  /-- Source points at the first coordinate bit. -/
  source : z.reg 24 = l.source
  /-- The reader is set to the exact coordinate field width. -/
  width : z.reg 41 = l.cw
  /-- Coordinate limit is the physical direction count. -/
  bound : z.reg 42 = l.a
  /-- Setup reads only the physical memory. -/
  memory : z.mem = old

private theorem primarySafe {w : ℕ} (d : Reg) (f : Word 8) (p : Arg → ℕ) (m : ℕ → ℕ) (reg : Reg → ℕ)
    (h : p 0+f.val < 2^w) : (readFrame d 62 63 f).safeReadOnly w p m reg := by
  simp (config := {decide := true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,h]
  omega

/-- Actual frame traversal leaves a fully initialized coordinate decoder and public
column-aggregation registers. The shared memory is retained byte for byte. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (frame : AtFrame l (readings pub) (readings m)) (room : Fits l w)
    (primary : readings pub 0 + 63 < 2^w) (header : l.header+12 < 2^w) :
    BoundedRun pub mac setup s m setup.slots (Initial l (readings m)) := by
  let p := readings pub
  let mem := readings m
  let reg := readings s
  have pr (d : Reg) (f : Word 8) (hf : f.val ≤ 63) (t : Reg → ℕ) :=
    primarySafe (w := w) d f p mem t (by change readings pub 0+_ < _; omega)
  have sec (d : Reg) (f : Word 8) (hf : f.val ≤ 12) (t : Reg → ℕ) :=
    CubeLengths.fieldSafe d f p mem t primary (by change frameField (readings pub) (readings m) 63+f.val < _
                                                  rw [frame.header]; omega)
  have p59 := pr 28 59 (by decide)
  have p63 := pr 22 63 (by decide)
  have p25 := pr 24 25 (by decide)
  have f2 := sec 29 2 (by decide)
  have f1 := sec 30 1 (by decide)
  have f3 := sec 31 3 (by decide)
  have f4 := sec 32 4 (by decide)
  have f12 := sec 34 12 (by decide)
  have f10 := sec 20 10 (by decide)
  have f11 := sec 21 11 (by decide)
  have f9 := sec 62 9 (by decide)
  obtain ⟨ptr,alphabet,source,dense,entries,totals,a,cw,rw,cap⟩ := frame
  change frameField p mem 63 = l.header at ptr
  change frameField p mem 59 = l.d at alphabet
  change frameField p mem 25 + 1 + mem (l.header+9) = l.source at source
  change mem (l.header+1) = l.dense at dense
  change mem (l.header+2) = l.entries at entries
  change mem (l.header+3) = l.totals at totals
  change mem (l.header+4) = l.a at a
  change mem (l.header+10) = l.cw at cw
  change mem (l.header+11) = l.rw at rw
  change mem (l.header+12) = l.cap at cap
  have lo : l.source ≤ l.start l.entries := by dsimp [Layout.start,fieldStart]; omega
  have sourceFit : l.source < 2^w := lo.trans_lt room.stream
  have start1 : frameField p mem 25 + 1 < 2^w := by omega
  have square : l.d*l.d < 2^w :=
    (Nat.le_mul_of_pos_right (l.d*l.d) room.dimension).trans_lt room.count
  have five : 5 < 2^w := by omega
  have one : 1 < 2^w := by omega
  have head5 : l.header+5 < 2^w := room.coordinate
  have safe : setup.safeReadOnly w p mem reg := by
    simp (config := {decide := true}) [setup,Code.block,Code.safeReadOnly,p59,p63,p25,f2,f1,f3,f4,f12,f10,f11,f9,
      CubeLengths.fieldValue,readFrameFixed,Code.evalNat,addressOpFits,addressOp,alphabet,ptr,source,sourceFit,start1,square,five,one,head5]
  obtain ⟨es,t,r,cost,eq⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨es,t,m,r,cost,?_⟩
  change Initial l mem ⟨readings t,mem⟩
  rw [eq]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,rfl⟩ <;>
    simp (config := {decide := true}) [setup,Code.block,Code.evalNat,readFrameFixed,CubeLengths.fieldValue,addressOp,
      ptr,alphabet,source,dense,entries,totals,a,cw,rw,cap,p,mem]

end RoutingISA.HeaderDecode

end BorderVNP
end Computability
end OAI
