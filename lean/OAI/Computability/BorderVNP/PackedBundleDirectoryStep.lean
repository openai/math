import OAI.Computability.BorderVNP.PackedBundleDirectoryImage

/-! # Native execution of one complete cell in the stable bundle directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA RoutingISA.CellPacket
open BottomReports
open BottomReports.Writer (write)
open private controlField from OAI.Computability.BorderVNP.PackedBundleDirectoryISA

/-- All loop controls, current compact ordinals, and the exact accumulated writes. -/
structure Scan (l : Layout) (g : ℕ → List BundleHeader) (m₀ : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop where
  cells : z.reg 31 = l.cells
  payload : z.reg 32 = l.payload
  left : z.reg 33 = l.rank
  right : z.reg 34 = l.stopRank
  ranges : z.reg 35 = l.ranges+2*i
  dest : z.reg 36 = l.output
  six : z.reg 37 = 6
  cell : z.reg 38 = i
  first : z.reg 39 = «prefix» g i
  cursor : z.reg 52 = l.output+6*«prefix» g i
  one : z.reg 63 = 1
  mem : z.mem = l.image g m₀ i

set_option maxRecDepth 4000 in
/-- Setup reads the real published frame and the four pointed-to controls. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (g : ℕ → List BundleHeader) {width : ℕ}
    (loaded : l.loaded (pub 0).val (readings m)) (fit : l.Fits w width) :
    BoundedRun pub mac setup s m setup.slots (Scan l g (readings m) 0) := by
  obtain ⟨hf,hc,hn,hb,hr,ho,hp,hi⟩ := loaded
  have hframe := fit.frameEnd
  have hcontrol := fit.controlEnd
  have hmarkers := fit.markers
  have hbound := fit.rankEnd
  have hw : w ≠ 0 := by rintro rfl; simp at hframe
  let z := NatState.ofWords s m
  have zmem : z.mem = readings m := rfl
  have zero : readings pub 0 = l.frame := hf
  have safe : setup.fixedSafe w (readings pub) z := by
    simp [setup,controlField,readFrame,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOp,addressOpFits,Function.update,zero,zmem,hc,hn,hb,hi,hw]
    omega
  apply (setup.runFixed pub mac s m safe).mono le_rfl
  rintro _ rfl
  change Scan l g (readings m) 0 (setup.fixedEval (readings pub) z)
  constructor <;>
    simp [setup,controlField,readFrame,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      Function.update,zero,zmem,hc,hn,hb,hr,ho,hp,hi,Layout.image,Layout.stopRank,Nat.add_assoc]

/-- Execute the live marker reads, the exact scalar copy, and both ordinal stores. -/
theorem cell_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (g : ℕ → List BundleHeader) (m₀ : ℕ → ℕ)
    {width i : ℕ} (fit : l.Fits w width) (secs : l.Sections g width m₀)
    (total : «prefix» g l.cells = l.bundles) (hi : i < l.cells) (h : Scan l g m₀ i (.ofWords s m)) :
    BoundedRun pub mac cellStep s m (15+5*(cellWords g i).length) (Scan l g m₀ (i+1)) := by
  let lo := l.start m₀ i
  let last := l.stop m₀ i
  let d := l.output+6*«prefix» g i
  let xs := cellWords g i
  let z := NatState.ofWords s m
  have hwidth : xs.length = 6*(g i).length := fields_length _
  have hend : lo+xs.length = last := secs.extent i hi
  have bounds := secs.rankBound i hi
  have hmax := prefix_mono g (show i+1 ≤ l.cells from hi)
  rw [total,prefix_succ] at hmax
  have hmark := fit.markers
  have hrend := fit.rankEnd
  have hpend := fit.payloadEnd
  have hout := fit.outputEnd
  have hrange := fit.rangesEnd
  have rankRead (a : ℕ) (ha : l.rank ≤ a) (hb : a < l.rank+width) : z.mem a = m₀ a := by
    have hr := apart_word fit.rangesRank ha hb
    have hd := apart_word fit.outputRank ha hb
    rw [show z.mem = _ from h.mem]
    exact l.image_outside g m₀ i a (by omega) (by omega)
  have ra : z.mem (l.rank+i) = m₀ (l.rank+i) := rankRead _ (by omega) (by omega)
  have rb : z.mem (l.stopRank+i) = m₀ (l.stopRank+i) := rankRead _ (by unfold Layout.stopRank; omega)
    (by unfold Layout.stopRank; omega)
  have hlast : last < 2^w := by dsimp [last,Layout.stop]; omega
  have hd : d+xs.length < 2^w := by dsimp [d]; omega
  have hleft : z.reg 33 = l.rank := h.left
  have hright : z.reg 34 = l.stopRank := h.right
  have hpay : z.reg 32 = l.payload := h.payload
  have hcell : z.reg 38 = i := h.cell
  have hone : z.reg 63 = 1 := h.one
  have hsafe : openSection.fixedSafe w (readings pub) z := by
    simp [openSection,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOp,
      addressOpFits,Function.update,hleft,hright,hpay,hcell,hone,ra,rb]
    unfold Layout.stopRank at *; omega
  obtain ⟨a,t,mt,step,ca,he⟩ := openSection.runFixed pub mac s m hsafe
  change NatState.ofWords t mt = openSection.fixedEval (readings pub) z at he
  have tm : readings mt = z.mem := congrArg NatState.mem he
  have regs (j : Reg) (j40 : j ≠ 40) (j41 : j ≠ 41) (j50 : j ≠ 50) (j51 : j ≠ 51) :
      readings t j = z.reg j := by
    exact congrArg Fin.val (step.keepsReg (by simp [openSection,Code.block,Code.keeps,j40,j41,j50,j51]))
  have ts : readings t 50 = lo := by
    change (NatState.ofWords t mt).reg 50 = lo
    simpa [openSection,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,
      lo,Layout.start,hleft,hcell,hpay,hone,ra] using congrFun (congrArg NatState.reg he) 50
  have te : readings t 51 = last := by
    change (NatState.ofWords t mt).reg 51 = last
    simpa [openSection,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update,
      last,Layout.stop,hright,hcell,hpay,rb] using congrFun (congrArg NatState.reg he) 51
  have td : readings t 52 = d := (regs 52 (by decide) (by decide) (by decide) (by decide)).trans h.cursor
  have tu : readings t 63 = 1 := (regs 63 (by decide) (by decide) (by decide) (by decide)).trans h.one
  have stored : WordsAt (readings mt) lo xs := by
    intro j
    have ha : l.payload ≤ lo+j.val := by dsimp [lo,Layout.start]; omega
    have hb : lo+j.val < l.payload+width := by have := j.isLt; dsimp [last,Layout.stop] at hend; omega
    have hr := apart_word fit.rangesPayload ha hb
    have hd' := apart_word fit.outputPayload ha hb
    rw [tm,show z.mem = _ from h.mem,l.image_outside _ _ _ _ (by omega) (by omega)]
    exact secs.words i hi j
  have sep : lo+xs.length ≤ d ∨ d+xs.length ≤ lo := by
    have hsep := fit.outputPayload
    dsimp [apart] at hsep
    dsimp [lo,Layout.start,d]
    dsimp [last,lo,Layout.start,Layout.stop] at hend
    omega
  obtain ⟨b,u,mu,copy,cb,_,ud,um⟩ := copy_runs pub mac t mt lo d xs ts (te.trans hend.symm) td tu stored sep hd
  let y := NatState.ofWords u mu
  have ur (r : Reg) (h40 : r ≠ 40) (h41 : r ≠ 41) (h50 : r ≠ 50) (h51 : r ≠ 51)
      (h52 : r ≠ 52) (h53 : r ≠ 53) : y.reg r = z.reg r :=
    (congrArg Fin.val (copy_keeps copy r h50 h52 h53)).trans (regs r h40 h41 h50 h51)
  have u35 : y.reg 35 = l.ranges+2*i := (ur 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.ranges
  have u36 : y.reg 36 = l.output := (ur 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.dest
  have u37 : y.reg 37 = 6 := (ur 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.six
  have u38 : y.reg 38 = i := (ur 38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.cell
  have u39 : y.reg 39 = «prefix» g i := (ur 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.first
  have u63 : y.reg 63 = 1 := (ur 63 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.one
  have u52 : y.reg 52 = l.output+6*«prefix» g (i+1) := by
    change (NatState.ofWords u mu).reg 52 = _
    rw [ud,hwidth,prefix_succ,Nat.mul_add]; dsimp [d]; omega
  have mem : y.mem = write (l.image g m₀ i) d xs := um.trans (by rw [tm,show z.mem = _ from h.mem])
  have closeSafe : closeSection.fixedSafe w (readings pub) y := by
    simp [closeSection,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      addressOp,addressOpFits,Function.update,u35,u36,u37,u38,u52,u63]
    omega
  obtain ⟨c,v,mv,close,cc,ve⟩ := closeSection.runFixed pub mac u mu closeSafe
  refine ⟨_,v,mv,step.seq (copy.seq close),?_,?_⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost c) ≤ _
    change traceCost a ≤ 7 at ca
    change traceCost c ≤ 7 at cc
    change traceCost b ≤ 5*(cellWords g i).length+1 at cb
    omega
  · rw [ve]
    change Scan l g m₀ (i+1) (closeSection.fixedEval (readings pub) y)
    have regKeep (r : Reg) (hr : r.val ≤ 34) : y.reg r = z.reg r :=
      ur r (by rintro rfl; contradiction) (by rintro rfl; contradiction) (by rintro rfl; contradiction)
        (by rintro rfl; contradiction) (by rintro rfl; contradiction) (by rintro rfl; contradiction)
    have regs31 := (regKeep 31 (by decide)).trans h.cells
    have regs32 := (regKeep 32 (by decide)).trans h.payload
    have regs33 := (regKeep 33 (by decide)).trans h.left
    have regs34 := (regKeep 34 (by decide)).trans h.right
    constructor <;>
      simp [closeSection,Code.block,Code.fixedEval,Code.evalNat,addressOp,Function.update_idem,
        regs31,regs32,regs33,regs34,u35,u36,u37,u38,u39,u63,u52,Nat.mul_succ,Nat.add_assoc,
        Layout.image,write,mem,d,xs]

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
