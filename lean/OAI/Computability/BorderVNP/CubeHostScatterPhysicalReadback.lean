import OAI.Computability.BorderVNP.CubeHostScatterPhysicalEnds
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix

/-! # Genuine crossing words after the four native control producers

The endpoint owner's scatter starts from its recovered physical banks.
The subsequent compact directory and control-row writes preserve this
absolute destination inside the cell's supplied block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Physical NativeIntervals HostAddress Crossing Tally VPVNP.MotifBase
open RoutingISA VPVNP.BurstRAM FiniteEvaluator.OpenSuffix

variable {D m n d blocks b h K s : ℕ} {P : Type*} {bits : P → ℕ} {Cell Team : Type}
variable {N : Network D P bits} {cell : N.Site → Cell} {il : NativeIntervals.Layout}
variable {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin il.count}
variable {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1)=il.alphabet}
variable {i : Fin (n+1)} {team : Fin d → Team} {number : Team ↪ ℕ}
variable {w : ℕ} {pub : Team → Arg → Word w} {mac : Team → TeamOpcode.Macros w 8}
variable {before dir : Team → ℕ → ℕ} {initial : Team → Memory w}
variable {single : SingleSlot n d blocks (h*b) → Bool} {ends : Packet n d blocks → Ends n → Fin (h*b) → Bool}
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
  (crossWidth N cell ∘ ord.symm) u ≤ blocks*(h*b))

/-- Host layout decoded from each original team's public frame and returned ownership memory. -/
abbrev hostLayout (pub : Team → Arg → Word w) (mem : Team → Memory w) (t : Team) :=
  Layout.fromFrame (pub t 0).val (readings (mem t))

/-- The sparse row is visited at the exact owner of the chosen endpoint. Its
word after the host copy is the routed assignment's physical endpoint bit. -/
theorem crossing_after_host (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) (side : Bool)
    (data : ∀ t, ResidentRows (hostLayout pub initial t) il (before t) (dir t) (readings (initial t)) n d blocks b h K s)
    (rows : ∀ t, PhysicalRows N cell il (before t) ord row cells label (productCode n d il.alphabet hz))
    (img : ∀ t, il.Image (before t) il.count (dir t))
    (teamID : ∀ t, (hostLayout pub initial t).team = number t)
    (cellOwner : ∀ t c, readings (initial t) ((hostLayout pub initial t).cells+2*cells c) = number (team (label c i)))
    (separate : ∀ t, (hostLayout pub initial t).SeparateDestinations (readings (initial t)))
    (banks : EndBanks i team (fun t => (hostLayout pub initial t).packets) (fun t => (hostLayout pub initial t).singles)
      (fun t => readings (initial t)) single ends K s) :
    let q := packedSlotEmbedding N cell ord label blocks (h*b) cap ⟨e,j⟩
    let t := endOwner i team side q.1
    let l := hostLayout pub initial t
    let mem := readings (initial t)
    l.prefix mem l.count (l.dest mem (row (ord e)).val side+j.val)=(readEnd single ends side q).toNat := by
  intro q t l mem
  let k := row (ord e)
  have col := (data t).crossing (rows t) e j
  change l.cell mem k.val false = cells (crossSrc N cell e) ∧ l.cell mem k.val true = cells (crossDst N cell e) ∧
    l.width mem k.val = N.width e.val at col
  have labelEq := (packedSlot_address N cell ord label blocks (h*b) cap e j).1
  have own : l.Owned mem k.val side := by
    refine ⟨fun eq => (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)) (col.2.2.symm.trans eq),?_,?_⟩
    · intro eq
      exact e.property (cells.injective (col.1.symm.trans (eq.trans col.2.1)))
    · change mem (l.cells+2*l.cell mem k.val side) = l.team
      rw [teamID t]
      cases side with
      | false =>
        rw [col.1]
        exact (cellOwner t _).trans (congrArg number (congrArg (fun p => endOwner i team false p) labelEq).symm)
      | true =>
        rw [col.2.1]
        exact (cellOwner t _).trans (congrArg number (congrArg (fun p => endOwner i team true p) labelEq).symm)
  have inRange : k.val < l.count := (data t).count.symm ▸ k.isLt
  have within : j.val < l.width mem k.val := by rw [col.2.2]; exact j.isLt
  rw [l.prefix_owned_bit (separate t) inRange le_rfl own within]
  rw [(data t).source_eq (rows t) (img t) cap e j side]
  exact banks.read q.1.1 q.1.2 q.2 side

/-- The actual successful control run preserves each word copied into the supplied
block wherever the two directory outputs and both per-owned-cell tables are disjoint. -/
theorem read_host_after_controls {p : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r z : Bank w}
    {mem mz : Memory w} {es : List (TeamRAM.Event w)} (H : Inputs)
    (ready : Ready H (p 0).val (readings mem) w) (run : Runs p mac code r mem es z mz)
    (addr : ℕ) (ranges : addr < H.bundles.ranges ∨ H.bundles.ranges+2*H.bundles.cells ≤ addr)
    (bundle : addr < H.bundles.output ∨ H.bundles.output+6*Packing.BundleDirectory.«prefix» H.groups H.bundles.cells ≤ addr)
    (ctrl : ¬ H.control.outputs addr) : readings mz addr = hostImage (p 0).val (readings mem) addr := by
  have im := ((FiniteEvaluator.OpenSuffix.run H ready).sound run).2
  change readings mz = H.image (p 0).val (readings mem) at im
  rw [im,Inputs.image,CellControlRows.Layout.published,Function.update_of_ne (fun eq => ctrl (.inr (.inr eq))),
    CellControlRows.image_outside H.control _ le_rfl ctrl,Inputs.bundleImage,H.bundles.image_outside _ _ _ _ ranges bundle]

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
