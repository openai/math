import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation
import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun

/-! # Aligning the sparse records before the fixed-address residue query -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyMaterialize

/-- Frame word 34 initially names the length-only local subtotal bank. Move the record
start back by two words per actual operand. Subsequent allocation restores the fixed
subtotal pointer by adding exactly this runtime record length. -/
def alignTallies : Code := .block [readFrame 48 60 61 34,readFrame 49 60 61 35,
  .binary .add 49 49 49,.binary .sub 48 48 49,writeFrame 48 60 61 34]

/-- Native address alignment before materialization. All earlier input words apart from
the destination pointer remain available to the subsequent indirect reads. -/
theorem alignTallies_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base count : ℕ) (hb : (m ((pub 0).val+34)).val=base)
    (hc : (m ((pub 0).val+35)).val=count) (room : (pub 0).val+35<2^w) (fit : 2*count ≤ base) :
    ∃ es t mt, Runs pub mac alignTallies s m es t mt ∧ traceCost es ≤ alignTallies.slots ∧
      readings mt=Function.update (readings m) ((pub 0).val+34) (base-2*count) ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) := by
  let z := NatState.ofWords s m
  have bl : base<2^w := hb ▸ (m ((pub 0).val+34)).isLt
  have safe : alignTallies.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [alignTallies,readFrame,writeFrame,Code.block,Code.fixedSafe,
      Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,Function.update,
      NatState.ofWords,z,readings,hb,hc]; omega
  obtain ⟨es,t,mt,r,cost,eq⟩ := alignTallies.runFixed pub mac s m safe
  have e := congrArg NatState.mem eq
  refine ⟨es,t,mt,r,cost,?_,ordinary_run (by decide) r⟩
  simpa (config := {decide := true}) [alignTallies,readFrame,writeFrame,Code.block,Code.fixedEval,
    Code.evalNat,addressOp,Function.update,NatState.ofWords,z,readings,hb,hc,two_mul] using e

/-- The length-only local-bank endpoint replaces just the initial records pointer
of the same ordinary source frame. -/
def Arena.alignedSeed {w : ℕ} (a : Arena) (pub : Arg → Word w) (m : Memory w) (p : ℕ) : Prop :=
  ({a with fresh := a.fresh+2*a.count} : Arena).seed pub m p

/-- The single native pointer update supplies exactly the ordinary allocator's expected input. -/
theorem Arena.seed_after_align {w : ℕ} (a : Arena) (pub : Arg → Word w) (m mt : Memory w)
    (p : ℕ) (before : a.alignedSeed pub m p)
    (image : readings mt=Function.update (readings m) ((pub 0).val+34) a.fresh) : a.seed pub mt p := by
  obtain ⟨dim,_,count,raw,teams,team,width,ptr,hw⟩ := before
  have read (j : ℕ) : (mt ((pub 0).val+j)).val=(Function.update (readings m) ((pub 0).val+34) a.fresh)
      ((pub 0).val+j) := congrFun image _
  simp [Arena.seed,read,Function.update,readings,dim,count,raw,teams,team,width,ptr,hw]

end DiagonalTallyRAM

namespace DiagonalTallyAllocation

open DiagonalTallyRAM

/-- The true scatter-record interval ends at the fixed subtotal address on every history. -/
def AfterTasks.arenaFor (a : AfterTasks) (count raw dim teams team width : ℕ) : Arena :=
  ⟨a.localBase-2*count,raw,dim,count,teams,team,width⟩

/-- Every prior physically emitted descriptor precedes the dynamically aligned record array. -/
theorem AfterTasks.arena_lower (a : AfterTasks) {count : ℕ} (bound : count ≤ a.bound.operands)
    (raw dim teams team width : ℕ) :
    a.fresh ≤ (a.arenaFor count raw dim teams team width).fresh := by
  change a.fresh ≤ a.fresh+2*a.bound.operands-2*count
  omega

/-- The local subtotal and entry-reader addresses depend only on the public length parameters.
In particular every legal history with the same dimensions uses the identical Fourier query bank. -/
theorem AfterTasks.fixed_outputs (a : AfterTasks) {count : ℕ} (bound : count ≤ a.bound.operands)
    (raw dim teams team width w : ℕ) :
    let ar := a.arenaFor count raw dim teams team width
    ar.frame.localBase=a.localBase ∧ ar.frame.claims=a.localBase+dim ∧
      ar.frame.totals=a.localBase+dim+teams*dim+dim ∧
      (ar.bitFrame w).dst=a.localBase+dim+teams*dim+dim+dim+1 := by
  have hb : 2*count ≤ a.localBase := by unfold localBase; omega
  simp [arenaFor,Arena.frame,Arena.bitFrame,Nat.sub_add_cancel hb]

/-- The length-only upper endpoint supplies the complete arithmetic arena bound. -/
theorem AfterTasks.arena_fits (a : AfterTasks) {count raw dim teams team width w frame : ℕ}
    (countBound : count ≤ a.bound.operands) (dir : frame+45 ≤ a.fresh)
    (rawBefore : raw+teams*dim*width ≤ a.fresh)
    (endFit : a.localBase+dim+teams*dim+dim+dim+1+dim*w<2^w)
    (teamFit : team<teams) (teamsFit : teams<2^w) (widthFit : width ≤ w) (wpos : 0<w) :
    (a.arenaFor count raw dim teams team width).Fits w frame := by
  have lo := a.arena_lower countBound raw dim teams team width
  have out := (a.fixed_outputs countBound raw dim teams team width w).2.2.2
  exact ⟨dir.trans lo,rawBefore.trans lo,by rw [out]; exact endFit,teamFit,teamsFit,widthFit,wpos⟩

end DiagonalTallyAllocation

end BorderVNP
end Computability
end OAI
