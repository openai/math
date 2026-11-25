import OAI.Hierarchy.DescentBundleHistory

namespace OAI
/-! # Full operand words of a scalar table split into aligned payload arguments -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory
noncomputable section
variable {A Tag : Type} {p : ℕ} (r : Recipe Tag A) (w : A→ℕ) (hp : 0<p)
variable (pub : ∀a,p∣w a) (priv : ∀h,p∣r.width h)

private theorem units (n : ℕ) (h : p∣n) : n=(n/p)*p := (Nat.div_mul_cancel h).symm

private def aligned {A : Type} {v : A→ℕ} (a : A) (i : Fin (v a/p)) : BlockRef p v :=
  ⟨a,i.val,(Nat.le_div_iff_mul_le hp).mp i.isLt⟩

private def operand (e : A⊕r.Hidden) (g : Fin (BitRecipe.referenceWidth r w e/p)) :
    BlockRef p w⊕BlockRef p r.width := match e with
  | .inl a=>.inl (aligned hp a g)
  | .inr h=>.inr (aligned hp h g)

include pub priv in
private theorem whole_eq (e : A⊕r.Hidden) :
    BitRecipe.referenceWidth r w e=BitRecipe.referenceWidth r w e/p*p := by
  cases e with | inl a=> exact units _ (pub a) | inr h=> exact units _ (priv h)

private theorem operand_read (e : A⊕r.Hidden) (g : Fin (BitRecipe.referenceWidth r w e/p)) (d : Fin p) :
    decode (Slice.whole hp (operand r w hp e g)) d=
      BitRecipe.exposeRef r w e (Fin.cast (whole_eq r w pub priv e).symm (finProdFinEquiv (g,d))) := by
  rw [decode_whole]
  rcases e with a|h
  · apply congrArg Sum.inl
    apply congrArg (Sigma.mk a)
    apply Fin.ext
    change g.val*p+d.val=d.val+p*g.val
    ring
  · apply congrArg Sum.inr
    apply congrArg (Sigma.mk h)
    apply Fin.ext
    change g.val*p+d.val=d.val+p*g.val
    ring

def exposed : Shape p (BitRecipe.expose r w) where
  hiddenMultiple := priv
  groups u j := BitRecipe.referenceWidth r w (r.operand u j)/p
  size_eq u j := whole_eq r w pub priv (r.operand u j)
  chunk u j g := Slice.whole hp (operand r w hp (r.operand u j) g)
  read u j g d := operand_read r w hp pub priv (r.operand u j) g d

@[simp] theorem exposed_stride (u j g) : ((exposed r w hp pub priv).chunk u j g).stride=1 := rfl
end
end Hierarchy.DescentBundleHistory

end OAI
