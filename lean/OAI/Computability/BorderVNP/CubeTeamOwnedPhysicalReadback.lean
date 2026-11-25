import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalSetup

/-! # Owned input banks after publishing the vertex directory

The team traversal establishes each incident input in the memory returned
by its row program. The final store to frame field 46 is below both scatter
banks, so the published memory retains the established inputs and all other
public source words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical Padding.Banks TeamRowSources RoutingISA VPVNP.BurstRAM

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}
variable {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ}
variable {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {m pre mt : Memory w}

/-- A physical row return extends the bank invariant at its actual ordinal.
The allocation separates the two banks and the frame bound supplies a nonzero
machine word width. -/
theorem PhysicalSetup.past_step (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (q : Fin (l.d*l.d)) (old : A.Past (l := l) owner q.val pre)
    (words : ∀ a, A.BankWord a →
      mt a = A.rowMem (pairAt l.d q).1 (pairAt l.d q).2 (l.view q.val) (l.crossing q.val) pre a) :
    A.Past (l := l) owner (q.val+1) mt := by
  have positive : 0 < w := by
    by_contra! zero
    have hz := Nat.eq_zero_of_le_zero zero
    have bound := P.fits.frameFit
    rw [hz] at bound
    simp at bound
  exact old.step q (l.view q.val) (l.crossing q.val)
    (A.separate_of_allocated P.allocation.orderPackets) positive words

private theorem afterFrame (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (a : ℕ) (word : A.BankWord a) : l.frame+112 ≤ a := by
  rcases word with ⟨z,rfl⟩ | ⟨p,j,rfl⟩
  · have lo : A.packetBase ≤ A.singleBase := (Nat.le_add_right ..).trans P.allocation.orderPackets
    exact (P.allocation.frame.trans lo).trans
      (show A.singleBase ≤ A.singleAddr z from (Nat.le_add_right ..).trans (Nat.le_add_right ..))
  · have lo : A.packetBase ≤ A.packetAddr p := Nat.le_add_right ..
    exact (P.allocation.frame.trans lo).trans (Nat.le_add_right ..)

/-- Publishing the count preserves every reserved packet or singleton word. -/
theorem PhysicalSetup.publish_bankWord (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (count a : ℕ) (word : A.BankWord a) :
    publishVertexCount pre l.frame count a = pre a := by
  apply publishVertexCount_other
  have lower := afterFrame P a word
  omega

/-- The actual count store preserves the established bank words at every prefix. -/
theorem PhysicalSetup.publish_past (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    {q : ℕ} (count : ℕ) (past : A.Past (l := l) owner q pre) :
    A.Past (l := l) owner q (publishVertexCount pre l.frame count) :=
  fun x owned passed => A.holds_of_words (P.publish_bankWord count) x (past x owned passed)

/-- After the last row and the count store, every physically owned endpoint
word or packet vertex can be read in the published memory. -/
theorem PhysicalSetup.publish_holds (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (count : ℕ) (past : A.Past (l := l) owner (l.d*l.d) pre)
    (x : View n l.d blocks (h*b)) (owned : owner (x.row A.axis).1 = l.teamID) :
    A.Holds (publishVertexCount pre l.frame count) x :=
  P.publish_past count past x owned (finProdFinEquiv (x.row A.axis)).isLt

/-- Read back all owned physical inputs and the complete vertex count from
the actual returned memory. The other immutable words agree with entry memory. -/
theorem PhysicalSetup.publish_readback (P : PhysicalSetup A owner power base stop actual claimed rows pub m)
    (past : A.Past (l := l) owner (l.d*l.d) pre) (same : ∀ a ∈ source l power n, pre a = m a)
    (published : mt = publishVertexCount pre l.frame (vertexPrefix l (wordOwner owner) n blocks (l.d*l.d))) :
    (∀ x : View n l.d blocks (h*b), owner (x.row A.axis).1 = l.teamID → A.Holds mt x) ∧
    readings mt (l.frame+46) = vertexPrefix l (wordOwner owner) n blocks (l.d*l.d) ∧
    (∀ a ∈ source l power n, a ≠ l.frame+46 → mt a = m a) := by
  subst mt
  have countFit : vertexPrefix l (wordOwner owner) n blocks (l.d*l.d) < 2^w := by
    have cap := P.capacity
    have room := P.allocation.endFit
    omega
  exact ⟨P.publish_holds _ past,publishVertexCount_here pre l.frame _ countFit,
    fun a inside other => (publishVertexCount_other pre l.frame _ a other).trans (same a inside)⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
