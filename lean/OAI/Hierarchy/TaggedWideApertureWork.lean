import OAI.Hierarchy.TaggedWidePrefixNative
import OAI.Hierarchy.TaggedWideOverlapNative

namespace OAI
/-! # Native instruction bounds for each role prefix and both ends of a signed overlap -/
noncomputable section
namespace Hierarchy.ProtocolRAM.NativeSiteWork
open scoped Classical

theorem prefix_total (d B : ℕ) (row : Fin d→Expr) (cheap : ∀i,(row i).work≤B) :
    (LocalPrefix.total d row).work≤1+d*(B+1) := by
  induction d with
  | zero=>simp [LocalPrefix.total,Expr.work]
  | succ d ih=>
    have less := ih (fun i=>row i.succ) (fun i=>cheap i.succ)
    have first := cheap 0
    simp only [LocalPrefix.total,Expr.work,Nat.succ_mul]
    omega

def PrefixFields (B : ℕ) (a : LocalPrefix.Columns) := a.ordinal.work≤B ∧ a.opposite.work≤B ∧ a.width.work≤B
theorem «prefix» (d B : ℕ) (row : Fin d→LocalPrefix.Columns) (head : LocalPrefix.Columns)
    (cheap : ∀i,PrefixFields B (row i)) (pivot : PrefixFields B head) :
    (LocalPrefix.expr row head).work≤1+d*(5*B+4+1) := by
  apply prefix_total d (5*B+4)
  intro i
  rcases cheap i with ⟨h₁,h₂,h₃⟩
  rcases pivot with ⟨h₄,h₅,h₆⟩
  simp only [LocalPrefix.term,Expr.work]
  omega

def Fields (B : ℕ) (a : Overlap.Fields) :=
  a.start.work≤B ∧ a.width.work≤B ∧ a.low.work≤B ∧ a.opposite.work≤B

theorem overlap_length (B : ℕ) (a b : Overlap.Fields) (ca : Fields B a) (cb : Fields B b) :
    (Overlap.length a b).work ≤ 256*(B+1) := by
  rcases ca with ⟨h₁,h₂,h₃,h₄⟩
  rcases cb with ⟨h₅,h₆,h₇,h₈⟩
  simp only [Overlap.length,Overlap.diff,Overlap.small,Overlap.upper,Overlap.start,Overlap.large,Overlap.lower,Expr.work]
  omega

theorem overlap_head (B W : ℕ) (a b c : Overlap.Fields) (ca : Fields B a) (cb : Fields B b)
    (cc : Fields B c) : (Overlap.head W a b c).work≤256*(B+1) := by
  rcases ca with ⟨h₁,h₂,h₃,h₄⟩
  rcases cb with ⟨h₅,h₆,h₇,h₈⟩
  rcases cc with ⟨h₉,h₁₀,h₁₁,h₁₂⟩
  simp only [Overlap.head,Overlap.small,Overlap.diff,Overlap.start,Overlap.large,Overlap.lower,Expr.work]
  omega

end Hierarchy.ProtocolRAM.NativeSiteWork

end
end OAI
