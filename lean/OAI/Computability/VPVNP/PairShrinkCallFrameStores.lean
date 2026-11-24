import OAI.Computability.VPVNP.PairShrinkCallFrameLive
import OAI.Computability.VPVNP.PairVertexFrameData
import OAI.Computability.VPVNP.PairShrinkHiddenStep
import OAI.Computability.VPVNP.PairNodeChildPackets

/-!
# Private geometry through the two shrinking stores

The vertex invariant gives the geometry pointer and the cache, length and
histogram words. Child packets occupy argument slots below the geometry.
Absorbed-wire stores occupy private slots beyond the leaf stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallFrameLive

open BurstRAM DFS NodeArguments LeafSourceLoad TreeDecode
open scoped Fin.CommRing
open private resident_read from OAI.Computability.VPVNP.PairVertexControl

variable {w n : ℕ} {R : LeafArena.Regions} {priv : Word w → Word w}
local notation "G" => NativeFrame.frameBase R

/-- Read the four live private cells directly from the scratch invariant
carried at each pending vertex. -/
theorem of_vertex {data : Fin 10 → Word w} {offset : Word w} {vals : Static 34 → Word w}
    (frame : VertexFrameData R data offset vals (scratch n priv))
    (cache : data 8 = (R.cacheBase : Word w)) (length : data 9 = (n : Word w))
    (above : n ≤ G) (room : G + 12 ≤ 2 ^ w) : Stored R n priv := by
  have resident := resident_read priv (G : Word w) offset (R.histBase : Word w) frame.resident
  have value (j : Fin 10) : priv ((G : Word w) + (j.val : Word w)) = data j := by
    have hj := j.isLt
    have live : n ≤ ((G + j.val : ℕ) : Word w).val := by
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : G + j.val < 2 ^ w)]
      omega
    have v := frame.record.values_at j
    rw [rawScratch, dite_eq_left live] at v
    rw [← Nat.cast_add]
    exact v
  exact ⟨resident.1, (value 8).trans cache, (value 9).trans length, resident.2.2⟩

private theorem child_outside (A : Arena) (qs : List Packet) (x : Word w)
    (fit : ∀ q ∈ qs, A.base q.node + q.bits.length ≤ 2 ^ w)
    (outside : ∀ q ∈ qs, x.val < A.base q.node ∨ A.base q.node + q.bits.length ≤ x.val) :
    ChildScan.storePackets A qs priv x = priv x := by
  induction qs generalizing priv with
  | nil => rfl
  | cons q qs ih =>
    exact (ih (fit := fun z hz ↦ fit z (List.mem_cons_of_mem _ hz))
      (outside := fun z hz ↦ outside z (List.mem_cons_of_mem _ hz))).trans
      (PrivateFields.storeBits_outside _ _ _ x (fit q List.mem_cons_self)
        (outside q List.mem_cons_self))

/-- The old children use real nodes below the region's exclusive node
bound, and all of their packet intervals begin above the geometry pointer cell. -/
theorem Stored.children (h : Stored R n priv) (qs : List Packet)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n)
    (nodes : ∀ q ∈ qs, q.node < R.nodes)
    (abovePointer : ∀ q ∈ qs, n < R.arguments.base q.node)
    (room : G + 12 ≤ 2 ^ w) :
    Stored R n (ChildScan.storePackets R.arguments qs priv) := by
  have kept (x : Word w) := child_outside (priv := priv) R.arguments qs x
    (fun q hq ↦ (fits q hq).2.2)
  apply h.transfer
  · exact kept _ (fun q hq ↦ .inl ((Nat.mod_le ..).trans_lt (abovePointer q hq)))
  · intro j hj
    have small : j < 12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    apply kept _
    intro q hq
    right
    have before := R.node_before (nodes q hq)
    have length := (fits q hq).2.1
    have next : R.histBase ≤ G := Nat.le_add_right ..
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : G + j < 2 ^ w)]
    omega

theorem hidden_below (base stride : ℕ) (rows : List ShrinkHiddenGuess.Row) (x : Word w)
    (room : ∀ row ∈ rows, base + row.1 * stride + row.2.length ≤ 2 ^ w)
    (below : x.val < base) : ShrinkHiddenGuess.storeRows base stride rows priv x = priv x := by
  induction rows generalizing priv with
  | nil => rfl
  | cons row rows ih =>
    exact (ih (room := fun z hz ↦ room z (List.mem_cons_of_mem _ hz))).trans
      (PrivateFields.storeBits_outside _ _ _ x (room row List.mem_cons_self)
        (.inl (below.trans_le (Nat.le_add_right _ _))))

/-- The hidden store starts beyond the entire geometry directory. Its
computed interval fits also cover zero-width absorbed rows. -/
theorem Stored.hidden (h : Stored R n priv) (stride : ℕ) (rows : List ShrinkHiddenGuess.Row)
    (above : n ≤ G) (fits : ∀ row ∈ rows,
      ShrinkCallABI.hiddenBase R n + row.1 * stride + row.2.length ≤ 2 ^ w) :
    Stored R n (ShrinkHiddenGuess.storeRows (ShrinkCallABI.hiddenBase R n) stride rows priv) := by
  have room : G + 12 ≤ ShrinkCallABI.hiddenBase R n := by
    unfold NativeFrame.frameBase ShrinkCallABI.hiddenBase LeafArena.Regions.stackBase
      LeafArena.Regions.cacheBase
    omega
  have kept (x : Word w) := hidden_below (priv := priv) (ShrinkCallABI.hiddenBase R n) stride
    rows x fits
  apply h.transfer
  · exact kept _ ((Nat.mod_le ..).trans_lt (by omega))
  · intro j hj
    have small : j < 12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    exact kept _ ((Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left small _).trans_le room))

end PairSimulation.ShrinkCallFrameLive

end VPVNP
end Computability
end OAI
