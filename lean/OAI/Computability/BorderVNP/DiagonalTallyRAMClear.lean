import OAI.Computability.BorderVNP.DiagonalTallyRAMLayout
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Initializing the local counter array through the actual instruction table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- Locate the team's fresh counter bank and initialize the clear-loop cursor. -/
def clearSetup : Code := .block [readFrame 48 60 61 32,readFrame 49 60 61 33,
  .constant 50 0,.constant 51 0,.constant 63 1]

/-- Explicitly write one zero word and advance the coordinate number. -/
def clearStep : Code := .block [.binary .add 52 48 50,.store 52 51,.binary .add 50 50 63]

/-- The scratch contents before the routine may be arbitrary. -/
def clear : Code := .seq clearSetup (.whileLt 50 49 clearStep)

/-- Memory after resetting a prefix of the team's local counters. -/
def cleared {α : Type*} [Zero α] (m : ℕ → α) (base n a : ℕ) : α :=
  if base≤a ∧ a<base+n then 0 else m a

private theorem cleared_succ {α : Type*} [Zero α] (m : ℕ → α) (base n : ℕ) :
    Function.update (cleared m base n) (base+n) 0 = cleared m base (n+1) := by
  funext a
  by_cases h : a=base+n
  · subst a; simp [cleared]
  · rw [Function.update_of_ne h]
    unfold cleared; split_ifs <;> first | rfl | omega

private structure ClearState (base dim i : ℕ) (orig : ℕ → ℕ) (z : NatState) : Prop where
  baseEq : z.reg 48=base
  limit : z.reg 49=dim
  cursor : z.reg 50=i
  zeroEq : z.reg 51=0
  oneEq : z.reg 63=1
  mem : z.mem=cleared orig base i

variable {w : ℕ}

private theorem clear_step_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (base dim i : ℕ) (orig : ℕ → ℕ)
    (hi : i<dim) (room : base+dim<2^w) (hs : ClearState base dim i orig (.ofWords s m)) :
    BoundedRun pub mac clearStep s m clearStep.slots (ClearState base dim (i+1) orig) := by
  let z := NatState.ofWords s m
  change ClearState base dim i orig z at hs
  obtain ⟨b,d,c,zeroEq,oneEq,mem⟩ := hs
  have safe : clearStep.fixedSafe w (readings pub) z := by
    simp [clearStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,b,c,oneEq]; omega
  apply (clearStep.runFixed pub mac s m safe).mono le_rfl
  intro z' eq
  rw [eq]
  change ClearState base dim (i+1) orig (clearStep.fixedEval (readings pub) z)
  constructor
  case mem =>
    simp [clearStep,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,b,c,zeroEq,mem,
      cleared_succ]
  all_goals simp [clearStep,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,b,d,c,zeroEq,oneEq]

/-- Every local coordinate starts at zero after the native routine, independently of
old memory. All other addresses retain their preceding values. -/
theorem clear_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (hr : f.resident pub m) (fit : f.addressesFit w (pub 0).val) :
    ∃ es t, Runs pub mac clear s m es t (cleared m f.localBase f.dim) ∧
      traceCost es ≤ clearSetup.slots+4*f.dim+1 := by
  obtain ⟨base,dim,_,_,_,_,_,_,_,_⟩ := hr
  obtain ⟨dir,room,_,_,_,_,_,_,_⟩ := fit
  have hw : w≠0 := by rintro rfl; simp at dir
  have safe : clearSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [clearSetup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,
      addressOpFits,readings,hw]; omega
  obtain ⟨a,t,ra,ha,ht⟩ := clearSetup.runReadOnly pub mac m s safe
  have init : ClearState f.localBase f.dim 0 (readings m) (.ofWords t m) := by
    constructor
    case mem => funext i; simp [cleared,NatState.ofWords]
    all_goals
      change readings t _ = _
      rw [ht]
      simp [clearSetup,readFrame,Code.block,Code.evalNat,readings,Function.update,addressOp,base,dim]
  obtain ⟨b,z,mz,rb,hb,hz⟩ := run_counted_loop pub mac 50 49 clearStep f.dim clearStep.slots
    (fun i => ClearState f.localBase f.dim i (readings m)) (fun _ _ h => ⟨h.cursor,h.limit⟩)
    (fun i hi su mu h => clear_step_runs pub mac su mu f.localBase f.dim i _ hi room h)
    0 (by omega) t m init
  have hm : mz=cleared m f.localBase f.dim := by
    funext j
    apply Fin.ext
    simpa only [cleared,NatState.ofWords,readings,apply_ite Fin.val,Fin.val_zero] using congrFun hz.mem j
  refine ⟨_,_,ra.seq (hm ▸ rb),?_⟩
  rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
  simp only [Nat.sub_zero,show clearStep.slots = 3 by decide] at hb; omega

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
