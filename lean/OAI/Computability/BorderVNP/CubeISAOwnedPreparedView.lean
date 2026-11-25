import OAI.Computability.BorderVNP.CubeISAOwnedRowAllocation

/-! # Deriving a native side's inputs from the actual outer row preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowSources

open Physical Physical.Owned Scatter RoutingISA RoutingISA.OwnedStages VPVNP.BurstRAM Tally DiagonalResidueRAM
open Padding.Banks

variable {w n d blocks b h K s : ℕ}

/-- Linear index of the directed view, with the owner's local group first. -/
def key (v : Fin d × Fin d) : ℕ := (finProdFinEquiv v).val

/-- The side of a strict row selected by the outer native cursor. -/
def oriented (p : Symbols d) (high : Bool) : Fin d × Fin d :=
  if high then p.val.swap else p.val

/-- Division and remainder recover both actual endpoint symbols of the native key. -/
theorem key_digits (v : Fin d × Fin d) : key v/d = v.1.val ∧ key v%d = v.2.val :=
  ⟨congrArg (fun p : Fin d × Fin d => p.1.val) (finProdFinEquiv.symm_apply_apply v),
    congrArg (fun p : Fin d × Fin d => p.2.val) (finProdFinEquiv.symm_apply_apply v)⟩

/-- Initial scalar frame image after the header, power table and declared coordinate
have been installed. The delivered row streams enter separately from the returned receiver. -/
structure Seed (A : Data n d blocks b h K s) (l : TeamRowPrepare.Layout) (power : ℕ)
    (pub : Arg → Word w) (m : Memory w) : Prop where
  /-- Actual primary frame base. -/
  frame : readings pub 0 = l.frame
  /-- Number of public symbols. -/
  alphabet : l.d = d
  /-- Decoded grouping coordinate. -/
  axis : l.axis = A.axis.val
  /-- Exact installed selector prefix for a strict pair. -/
  selectorCount : l.selectors = 2*blocks*(d.choose 2)^n*VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h
  /-- True primary, secondary and power-table inputs. -/
  loaded : (rowLayout A l power).Loaded n (readings pub) (readings m)
  /-- The number of product-label codes in the real frame. -/
  labels : readings m (l.frame+56) = d^(n+1)
  /-- Absolute singleton bank pointer in the real frame. -/
  singles : readings m (l.frame+88) = A.singleBase

variable {A : Data n d blocks b h K s} {l : TeamRowPrepare.Layout} {power vertexBase stop : ℕ}
variable {pub : Arg → Word w} {original m : Memory w}

private theorem pointer {v : Word w} {k : ℕ} (eqn : v.val = k) : v = word w k :=
  Fin.ext (eqn.trans (word_val _ _ (eqn ▸ v.isLt)).symm)

/-- Transfer every loaded scalar and power across previous physical row updates. -/
theorem Seed.transfer (seed : Seed A l power pub original) (same : ∀ j ∈ source l power n, m j = original j) :
    Seed A l power pub m := by
  have fr : (pub 0).val = l.frame := seed.frame
  have hprotected : Protected (rowLayout A l power) n (pub 0).val (source l power n) := fr ▸ frame_protected
  exact ⟨seed.frame,seed.alphabet,seed.axis,seed.selectorCount,hprotected.loaded seed.loaded same,
    (congrArg Fin.val (same _ (primary (by decide)))).trans seed.labels,
    (congrArg Fin.val (same _ (primary (by decide)))).trans seed.singles⟩

/-- The native quotient, remainder, sorted symbols and owner bit are exactly the
strict row's expected calling convention, on both incident views. -/
theorem strict_entry (seed : Seed A l power pub original) (p : Symbols d) (high : Bool) (r : Bank w)
    (prepared : TeamRowPrepare.ReadyRow l (readings m) (key (oriented p high)) (.ofWords r m)) :
    Entry A.axis p.val.1 p.val.2 r ∧ readings r 3 = (if high then p.val.2 else p.val.1).val := by
  have left : key (oriented p high)/l.d = (oriented p high).1.val := by rw [seed.alphabet]; exact (key_digits _).1
  have right : key (oriented p high)%l.d = (oriented p high).2.val := by rw [seed.alphabet]; exact (key_digits _).2
  have lt : p.val.1.val < p.val.2.val := p.property
  refine ⟨⟨prepared.zero,prepared.one,prepared.axis.trans seed.axis,?_,?_⟩,?_⟩
  · apply prepared.smaller.trans
    rw [left,right]
    cases high <;> simp [oriented,Nat.min_eq_left lt.le,Nat.min_eq_right lt.le]
  · apply prepared.larger.trans
    rw [left,right]
    cases high <;> simp [oriented,Nat.max_eq_right lt.le,Nat.max_eq_left lt.le]
  · apply prepared.localGroup.trans
    rw [left]
    cases high <;> rfl

/-- For this actual directed view the crossing cursor follows its true selector prefix. -/
theorem strict_crossing (seed : Seed A l power pub original) (p : Symbols d) (high : Bool) :
    let q := key (oriented p high)
    l.crossing q = l.view q+(commonSelectors A.select A.axis p).length := by
  intro q
  have left : key (oriented p high)/l.d = (oriented p high).1.val := by rw [seed.alphabet]; exact (key_digits _).1
  have right : key (oriented p high)%l.d = (oriented p high).2.val := by rw [seed.alphabet]; exact (key_digits _).2
  have lt : p.val.1.val < p.val.2.val := p.property
  have ne : q/l.d ≠ q%l.d := by
    change key (oriented p high)/l.d ≠ key (oriented p high)%l.d
    rw [left,right]
    cases high <;> simpa [oriented] using (by first | exact lt.ne | exact lt.ne')
  rw [TeamRowPrepare.Layout.crossing,ite_eq_right ne,commonSelectors_length,strict_rowSelectorBits,seed.selectorCount]

/-- The true routed words from either directed endpoint and the actual outer
prepare return suffice for the full native strict-side execution. -/
theorem strict_ready (seed : Seed A l power pub original) (space : Allocation A l power vertexBase stop w)
    (p : Symbols d) (high : Bool) (r : Bank w) (out : ℕ) (output : readings r 7 = out)
    (before : vertexBase ≤ out) (room : out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ stop)
    (same : ∀ j ∈ source l power n, m j = original j)
    (prepared : TeamRowPrepare.ReadyRow l (readings m) (key (oriented p high)) (.ofWords r m))
    (sels : Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) original
      (l.view (key (oriented p high))) (commonSelectors A.select A.axis p))
    (crosses : Resident (Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d))) original
      (l.view (key (oriented p high))+(commonSelectors A.select A.axis p).length)
      (commonCrossings b A.axis p A.select A.supply (fun z => A.value z.1.val z.2))) :
    let q := key (oriented p high)
    SideReady (A.packet p high (l.view q) (l.crossing q)) (A.side power l.header out)
      pub (source l power n) r m := by
  intro q
  have current := seed.transfer same
  have lim := before.trans ((Nat.le_add_right _ _).trans room)
  obtain ⟨entry,group⟩ := strict_entry seed p high r prepared
  have hframe : (pub 0).val = l.frame := seed.frame
  refine ⟨entry,group,pointer prepared.selectorCursor,pointer prepared.crossingCursor,output,rfl,current.loaded,
    hframe ▸ space.packets,hframe ▸ space.singles,hframe ▸ frame_protected,hframe ▸ primary (by decide),hframe ▸ primary (by decide),
    hframe ▸ current.labels,hframe ▸ current.singles,(resident_views sels).congr same,?_,
    fun u _ j hj => space.packetDest lim u hj,fun u v j hj => space.singleDest lim u v hj,
    space.orderPackets,space.orderSingles.trans before,room.trans_lt space.endFit⟩
  change Resident (source l power n) m (l.crossing q) _
  rw [strict_crossing seed p high]
  exact (resident_views crosses).congr same

/-- All protected words remain usable after this strict side, whether they
precede the physical packet bank or follow the global directory. -/
theorem strict_source (space : Allocation A l power vertexBase stop w) (p : Symbols d) (high : Bool)
    {r t : Bank w} {mt : Memory w} (sel cross out : ℕ) (before : vertexBase ≤ out)
    (room : out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ stop)
    (post : SideResult (A.packet p high sel cross) (A.side power l.header out) (source l power n) r m t mt) :
    ∀ j ∈ source l power n, mt j = m j := by
  intro j hj
  rcases space.outside hj with low | high
  · have hpack := (Nat.le_add_right ..).trans space.orderPackets
    have hsing := (Nat.le_add_right ..).trans space.orderSingles
    exact post.source j hj (low.trans_le (hpack.trans (hsing.trans before)))
  · exact post.above j hj (room.trans high)

end Cube.TeamRowSources

end BorderVNP
end Computability
end OAI
