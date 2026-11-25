import OAI.Hierarchy.DescentResetNumberStem

namespace OAI
/-! # Program size and runtime of the six measured stem operands and both installed laws -/
namespace Hierarchy.DescentResetNumberStem.Layout
open ProtocolRAM DescentStaticWordColumn
variable {X J K : ℕ} (L : Layout X J K)

private theorem pass_names (w U : ℕ) (ps : List Pass) (cheap : ∀p∈ps,p.term.work≤U) :
    names (ProtocolRAM.program w ps) ≤ 15 + ps.length*(11+4*U) := by
  induction ps with
  | nil => simp [ProtocolRAM.program,names_scan,Expr.work]
  | cons p rest ih =>
    have head := cheap p (.head _)
    have tail := ih (fun q hq => cheap q (.tail _ hq))
    rw [ProtocolRAM.program,names_seq,Pass.procedure,names_scan,List.length_cons,Nat.succ_mul rest.length (11+4*U)]
    omega

theorem tariff (w U : ℕ) (inputs : ∀x j i,(L.src x j i).work≤U) :
    L.ticks + 7*names (L.code w) ≤
      4096*(X*J+1)*(U+1)*(1+L.rows+2^(7*L.field*L.M)) := by
  let cost := 14+6*(U+11)
  have perSlot (p : Fin (X*J)) : (L.term p).work≤cost :=
    DescentOperandPairBook.expr_work L.laws L.M L.header _ _ U (inputs _ _)
  have perPass (p : Pass) (hp : p∈L.jobs) : p.rows≤L.rows ∧ p.term.work≤cost := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨le_rfl,perSlot i⟩
  have length : L.jobs.length=X*J := by simp [jobs,DescentResetOriginalSlots.passes]
  have run := clock_le L.jobs L.rows cost perPass
  have body := pass_names w cost L.jobs (fun p hp=>(perPass p hp).2)
  rw [length] at run body
  let n := DescentOperandPairBook.words 6 L.field L.M
  have setup : names (DescentOperandPairBook.program L.laws L.M w L.header)=15*(n+1) :=
    names_mount ..
  have units : DescentOperandPairBook.unit 6 L.field=7*L.field := by
    unfold DescentOperandPairBook.unit
    omega
  have header : n=16*2^(7*L.field*L.M) := by
    dsimp only [n,DescentOperandPairBook.words]
    rw [units]
    omega
  unfold ticks code
  rw [names_seq,setup]
  calc
    _ ≤ (4+10*n+(4+(X*J)*(4+L.rows*(2*cost+4)))) +
        7*(15*(n+1)+(15+(X*J)*(11+4*cost))) :=
      Nat.add_le_add (Nat.add_le_add_left run _) (Nat.mul_le_mul_left 7 (Nat.add_le_add_left body _))
    _ ≤ _ := by
      rw [header]
      dsimp only [cost]
      ring_nf
      omega

theorem tariff64 (w : ℕ) (inputs : ∀x j i,(L.src x j i).work≤64) :
    L.ticks + 7*names (L.code w) ≤ 266240*(X*J+1)*(1+L.rows+2^(7*L.field*L.M)) := by
  have paid := L.tariff w 64 inputs
  have coefficient (slots total : ℕ) : 4096*slots*(64+1)*total = 266240*slots*total := by ring
  simpa only [coefficient] using paid

end Hierarchy.DescentResetNumberStem.Layout

end OAI
