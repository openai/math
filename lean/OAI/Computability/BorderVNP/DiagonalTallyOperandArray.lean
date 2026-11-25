import OAI.Computability.BorderVNP.DiagonalTallyPacketEmit
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Native array stores for the count and use operand directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyOperandArray

open VPVNP.BurstRAM RoutingISA DiagonalTallyPacketEmit

/-- Store the computed value at the next physical array index and advance. -/
def save : Code := .block [.binary .add 54 42 40,.store 54 50,.binary .add 40 40 43]

/-- Each expression reads the physical row index in register 40 and returns register 50. -/
def array (expr : Code) : Code := .whileLt 40 41 (.seq expr save)

private structure State (orig : Reg → ℕ) (mem : ℕ → ℕ) (output : ℕ → ℕ)
    (dst len i : ℕ) (z : NatState) : Prop where
  low : ∀ j : Reg, j.val<40 → z.reg j=orig j
  cursor : z.reg 40=i
  bound : z.reg 41=len
  dest : z.reg 42=dst
  unit : z.reg 43=1
  image : z.mem=written dst output mem i

/-- Every initialized array entry is written by an actual native store. The original
state is otherwise unrestricted, including old contents of the destination interval. -/
theorem array_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (expr : Code) (output : ℕ → ℕ) (dst len : ℕ)
    (hp : expr.protects 44=true) (h0 : (s 40).val=0) (hn : (s 41).val=len)
    (hd : (s 42).val=dst) (hu : (s 43).val=1) (hroom : dst+len<2^w)
    (value : ∀ (i : ℕ), i<len → ∀ z : NatState,
      (∀ j : Reg, j.val<40 → z.reg j=(s j).val) → z.reg 40=i → z.reg 43=1 →
      expr.safeReadOnly w (readings pub) z.mem z.reg ∧
        expr.evalNat (readings pub) z.mem z.reg 50=output i) :
    ∃ es t mt, Runs pub mac (array expr) s m es t mt ∧
      traceCost es ≤ len*(expr.slots+save.slots+1)+1 ∧
      readings mt=written dst output (readings m) len ∧
      (∀ j : Reg, j.val<40 → t j=s j) := by
  let P := State (readings s) (readings m) output dst len
  have step (i : ℕ) (hi : i<len) (u : Bank w) (mu : Memory w) (hs : P i (.ofWords u mu)) :
      BoundedRun pub mac (.seq expr save) u mu (expr.slots+save.slots) (P (i+1)) := by
    let z := NatState.ofWords u mu
    change P i z at hs
    obtain ⟨lo,ci,bn,de,un,mi⟩ := hs
    obtain ⟨safe,val⟩ := value i hi z lo ci un
    obtain ⟨a,u₁,r₁,c₁,e₁⟩ := expr.runReadOnly pub mac mu u safe
    let z₁ := NatState.ofWords u₁ mu
    have stable (j : Reg) (hj : j.val<44) : z₁.reg j=z.reg j :=
      (congrFun e₁ j).trans (expr.evalNat_protected _ _ _ hp _ hj)
    have ci₁ := (stable 40 (by decide)).trans ci
    have bn₁ := (stable 41 (by decide)).trans bn
    have de₁ := (stable 42 (by decide)).trans de
    have un₁ := (stable 43 (by decide)).trans un
    have val₁ : z₁.reg 50=output i := (congrFun e₁ 50).trans val
    have safe₁ : save.fixedSafe w (readings pub) z₁ := by
      simp [save,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
        Function.update,addressOpFits,ci₁,de₁,un₁]; omega
    obtain ⟨b,y,my,r₂,c₂,e₂⟩ := save.runFixed pub mac u₁ mu safe₁
    refine ⟨_,y,my,r₁.seq r₂,?_,?_⟩
    · rw [show traceCost (a++b)=traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]; omega
    · rw [e₂]
      change P (i+1) (save.fixedEval (readings pub) z₁)
      constructor
      case low =>
        intro j hj
        have h40 : j≠40 := by rintro rfl; exact (by decide : ¬ (40 : Reg).val<40) hj
        have h54 : j≠54 := by rintro rfl; exact (by decide : ¬ (54 : Reg).val<40) hj
        simpa [save,Code.block,Code.fixedEval,Code.evalNat,Function.update,h40,h54] using
          (stable j (by omega)).trans (lo j hj)
      case image =>
        have mem₁ : z₁.mem=written dst output (readings m) i := mi
        simp [save,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,ci₁,de₁,val₁,
          mem₁,written_step]
      all_goals simp [save,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,ci₁,bn₁,de₁,un₁]
  have init : P 0 (.ofWords s m) := ⟨fun _ _ => rfl,h0,hn,hd,hu,by funext j; simp [written,NatState.ofWords]⟩
  obtain ⟨es,t,mt,r,hcost,endState⟩ := run_counted_loop pub mac 40 41 (.seq expr save)
    len (expr.slots+save.slots) P (fun _ _ h => ⟨h.cursor,h.bound⟩) step 0 (by omega) s m init
  exact ⟨es,t,mt,r,by simpa using hcost,endState.image,fun j hj => Fin.ext (endState.low j hj)⟩

end DiagonalTallyOperandArray

end BorderVNP
end Computability
end OAI
