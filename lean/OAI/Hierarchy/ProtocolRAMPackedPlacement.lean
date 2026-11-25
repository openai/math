import OAI.Hierarchy.TaggedShorterPackedRows

namespace OAI
/-! # Physical subslot coordinates from live old-group socket receipts -/

noncomputable section
namespace Hierarchy.ProtocolRAMPackedPlacement

open ProtocolRAMReportedPorts Tagged.WideStack TaggedShorterSupergroups

variable {G : Type*} {size : G → ℕ} {N H w menu γ lanes D : ℕ}

abbrev Live (rows : Fin N → Row) (w : ℕ) := {i : Fin N // 0 < pieces rows w i}

abbrev Receipt (rows : Fin N → Row) (w : ℕ) (size : G → ℕ) :=
  Bool → Live rows w ↪ (Σ g,Fin (size g))

/-- The word actually emitted for the group is meaningful on every row.
Original link IDs, payload widths, and geometric endpoints come from the unchanged descriptor. -/
def translated (rows : Fin N → Row) (groups : Fin N → ℕ) (i : Fin N) : Row :=
  {rows i with group := groups i}

def placement (dir : Directory size H) (hH : 0 < H) (rows : Fin N → Row)
    (links : Function.Injective fun i => (rows i).link) (receipt : Receipt rows w size)
    (groups : ∀ (b : Bool) (i : Live rows w),(dir.group (receipt b i).1).val = (rows i.val).group)
    (room : ∀ i,pieces rows w i ≤ lanes) (fit : H*lanes ≤ D)
    (g : Fin dir.groups) (b : Bool) : Fin (count rows w menu γ g.val) ↪ Fin D :=
  (common rows w menu γ g.val links).symm.toEmbedding.trans
    (staticUnit rows g (fun side => dir.livePort hH rows w (receipt side))
      (fun side => dir.live_distinct hH rows (receipt side) (groups side) g) room fit b)

theorem bound (dir : Directory size H) (hH : 0 < H) (rows : Fin N → Row)
    (links : Function.Injective fun i => (rows i).link) (receipt : Receipt rows w size)
    (groups : ∀ (b : Bool) (i : Live rows w),(dir.group (receipt b i).1).val = (rows i.val).group)
    (room : ∀ i,pieces rows w i ≤ lanes) (fit : H*lanes ≤ D)
    (g : Fin dir.groups) : count rows w menu γ g.val ≤ D :=
  static_capacity rows links g (fun side => dir.livePort hH rows w (receipt side))
    (fun side => dir.live_distinct hH rows (receipt side) (groups side) g) room fit

theorem group_fit (dir : Directory size H) (rows : Fin N → Row) (receipt : Receipt rows w size)
    (groups : ∀ (b : Bool) (i : Live rows w),(dir.group (receipt b i).1).val = (rows i.val).group)
    (i : Fin N) (live : 0 < pieces rows w i) : (rows i).group < dir.groups :=
  (groups false ⟨i,live⟩) ▸ (dir.group (receipt false ⟨i,live⟩).1).isLt

/-- The native base may contain any word on an unused row. A unit witnesses that
its row is live, so the publisher observes the exact frozen port for every write. -/
theorem publish_located (dir : Directory size H) (hH : 0 < H) (rows : Fin N → Row)
    (links : Function.Injective fun i => (rows i).link) (receipt : Receipt rows w size)
    (groups : ∀ (b : Bool) (i : Live rows w),(dir.group (receipt b i).1).val = (rows i.val).group)
    (room : ∀ i,pieces rows w i ≤ lanes) (fit : H*lanes ≤ D)
    (lr : Bool → Fin N → ℕ)
    (read : ∀ (b : Bool) (i : Live rows w),lr b i.val = (dir.slot (receipt b i).1 (receipt b i).2).val*lanes)
    (b : Bool) (g : Fin dir.groups) (u : ProtocolRAMReportedPorts.Unit rows w menu γ g.val) :
    (placement dir hH rows links receipt groups room fit g b (common rows w menu γ g.val links u)).val =
      lr b u.1.val + u.2.val := by
  simp only [placement,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
  rcases u with ⟨i,j⟩
  let actual : Live rows w := ⟨i.val,Nat.zero_lt_of_lt j.isLt⟩
  change j.val+lanes*(dir.livePort hH rows w (receipt b) actual.val).val = lr b actual.val+j.val
  rw [dir.livePort_at hH rows (receipt b) actual,read b actual,Nat.mul_comm lanes,Nat.add_comm]

end Hierarchy.ProtocolRAMPackedPlacement

end
end OAI
