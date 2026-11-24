import OAI.Computability.VPVNP.PairTraversalNodeBounds
import OAI.Computability.VPVNP.PairVertexRootFields
import OAI.Computability.VPVNP.PairTerminalPackedPrefix

/-!
# Root row of a selected placement tree

The selected tree ends at the row numbered by its final state's site order.
The terminal bootstrap publishes the base of that layer and its row stride
in header cells 6 and 15. Their native multiply-add recovers the same address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open LocalHistory NetworkKernel Compression DFS BurstRAM
open scoped Fin.CommRing

variable {A : Type*}

private def finalOrder {N Y : Network} (c : TermChain A N Y) (ords : ChainOrders c)
    (initial : Order N.Site) : Order Y.Site :=
  match c with
  | .done _ => initial
  | .more _ _ tail => finalOrder tail ords.2 ords.1

open private castOrders from OAI.Computability.VPVNP.PairTraversalSelectedOrder

private theorem cast_finalOrder {N M Y : Network} (e : N = M) (c : TermChain A M Y)
    (ords : ChainOrders c) (initial : Order M.Site) :
    finalOrder (e.symm ▸ c : TermChain A N Y) (castOrders e c ords) (e.symm ▸ initial) =
      finalOrder c ords initial := by cases e; rfl

variable [CommRing A]

private theorem branch_finalOrder {a g b n : ℕ} {X : State a g} (E : StateExecution A b n X)
    (data : E.Records) (z : E.Choices) :
    finalOrder (E.termChain data z) (branchOrders E data z) (siteOrder X) =
      siteOrder (E.finalState z) := by
  induction E with
  | done => rfl
  | more p tail ih =>
    let c := (tail z.1).termChain (data.2 z.1) z.2
    let ords := branchOrders (tail z.1) (data.2 z.1) z.2
    exact (cast_finalOrder (p.output_eq z.1) c ords (siteOrder (p.next z.1))).trans
      (ih z.1 (data.2 z.1) z.2)

open private addTree from OAI.Computability.VPVNP.PairTraversalHistory

private theorem chain_root_address {N Y : Network} {L : Type} [Fintype L] {κ : L → A}
    (c : TermChain A N Y) (r : ChainParsers κ c) (ords : ChainOrders c)
    (initial : Order N.Site) (cap base : ℕ) (prior : Layer) (count : prior.count = initial.length)
    (input : N.Site → VertexTree)
    (atRow : ∀ u, (input u).address = address cap base (initial.entries.symm u).val) (v : Y.Site) :
    (chainTrees c r (chainPointers cap c ords (address cap base initial.length)) input v).address =
      address cap (base + words cap (prior :: stepLayers c r ords initial).dropLast)
        ((finalOrder c ords initial).entries.symm v).val := by
  induction c generalizing base prior with
  | done =>
    change (input v).address = address cap (base + words cap []) (initial.entries.symm v).val
    rw [show words cap [] = 0 by simp [words], Nat.add_zero]
    exact atRow v
  | more t data tail ih =>
    let next := address cap base initial.length
    let layer := stepLayer initial ords.1 r.1
    have h := ih r.2 ords.2 ords.1 next layer rfl
      (addTree r.1 (sitePointers cap next ords.1) input) (fun _ => rfl)
    refine (h v).trans ?_
    simp only [stepLayers, finalOrder, List.dropLast_cons_cons, words, List.map_cons, List.sum_cons,
      Nat.mul_add, next, layer, address, count, Nat.add_assoc]
    rfl

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)

local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z
local notation "ls" => selectedLayers B f hf T hT X z

/-- Every final site has its root in the last row layer at its actual numerical ordinal. -/
theorem selectedTrees_address (base : ℕ) (v : (Y).network.Site) :
    (selectedTrees B f hf T hT X z base v).address =
      address B.recordLimit (base + words B.recordLimit (ls).dropLast)
        ((siteOrder (Y)).entries.symm v).val := by
  let E := B.execute f hf T hT X
  let data := B.records f hf T hT X
  let c := E.termChain data z
  let ords := branchOrders E data z
  let r := selectedParsers B f hf T hT X z
  let old := siteOrder X
  have h := chain_root_address c r ords old B.recordLimit base (leafLayer old) rfl
    (fun u => leafTree (sitePointers B.recordLimit base old u)) (fun _ => rfl) v
  rw [show finalOrder c ords old = siteOrder (Y) from branch_finalOrder E data z] at h
  exact h

variable {w : ℕ}

/-- The terminal gather computes the selected root using the live last-layer base
and row stride. Fit of the selected arena suffices for the native multiply-add. -/
theorem selectedTrees_address_ofHeader (base : ℕ) (v : (Y).network.Site) (degree : ℕ)
    (pub : Fin 11 → Word w) (H ordinal : Word w) (m : Memory w)
    (ord : ordinal.val = ((siteOrder (Y)).entries.symm v).val)
    (lastBase : m (H + 6).val = ((base + words B.recordLimit (ls).dropLast : ℕ) : Word w))
    (stride : m (H + 15).val = ((B.recordLimit + 2 : ℕ) : Word w))
    (fit : base + words B.recordLimit (ls) ≤ 2 ^ w) :
    (selectedTrees B f hf T hT X z base v).address =
      (TerminalRootGather.Layout.ofHeader degree pub H ordinal m).root := by
  let tree := selectedTrees B f hf T hT X z base v
  have mem : tree.address ∈ tree.preorder := by
    cases tree
    exact List.mem_cons_self
  have bound := (selectedTrees_below B f hf T hT X z base v mem).trans_le fit
  have eqn := selectedTrees_address B f hf T hT X z base v
  rw [eqn, address, ← ord] at bound ⊢
  change _ = (m (H + 6).val + m (H + 15).val * ordinal).val
  have hword : (ordinal.val : Word w) = ordinal := Fin.ext (Nat.mod_eq_of_lt ordinal.isLt)
  rw [lastBase, stride]
  calc
    _ = (((base + words B.recordLimit (ls).dropLast + (B.recordLimit + 2) * ordinal.val : ℕ) :
      Word w)).val := (Nat.mod_eq_of_lt bound).symm
    _ = _ := by simp only [Nat.cast_add, Nat.cast_mul, hword]

/-- The physical header fields published by the selected terminal bootstrap supply
both address operands of the root gather. -/
theorem selectedTrees_address_ofBootstrap (D : CompressorRecords.DescriptorSpace.Layout)
    (baseBits laneBits : ℕ) (tab : Fin D.shape.tables) (v : (Y).network.Site) (degree : ℕ)
    (pub : Fin 11 → Word w) (H ordinal : Word w) (m calendar : Memory w)
    (ord : ordinal.val = ((siteOrder (Y)).entries.symm v).val)
    (fields : ∀ j : Fin 21, j.val = 6 ∨ j.val = 15 →
      m (H + (j.val : Word w)).val =
        TerminalBootstrap.values D (ls).dropLast.length
          (TerminalBootstrap.fromState D (ls).dropLast B.recordLimit baseBits laneBits (Y) tab)
          B.recordLimit pub calendar j)
    (fit : CompressorRecords.DescriptorSpace.endAddress D + words B.recordLimit (ls) ≤ 2 ^ w) :
    (selectedTrees B f hf T hT X z (CompressorRecords.DescriptorSpace.endAddress D) v).address =
      (TerminalRootGather.Layout.ofHeader degree pub H ordinal m).root :=
  selectedTrees_address_ofHeader B f hf T hT X z _ v degree pub H ordinal m ord
    (fields 6 (Or.inl rfl)) (fields 15 (Or.inr rfl)) fit

end PairSimulation.TraversalRows

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords DescriptorSpace LocalHistory TraversalRows TerminalLink
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {n T : ℕ}
variable {hT : T * S.laneBits ≤ n} {X : State (S.degreeExponent 0) n}
variable {z : (B.execute f hf T hT X).Choices}
local notation "Y" => StateExecution.finalState (B.execute f hf T hT X) z

/-- At the physical vertex entry, the root gather reads the row for the
selected final site from the bootstrap fields preserved by the linked stages. -/
theorem VertexEntry.gather_root {D : Layout} {tab : Fin D.shape.tables} {baseBits laneBits : ℕ}
    {pub : Fin 11 → Word w} {calendar vertex : Memory w} {bits : Fin (Y).totalWidth → Bool}
    (entry : VertexEntry B f hf T hT X z D tab baseBits laneBits pub calendar vertex bits)
    (v : (Y).network.Site) (degree : ℕ) (ordinal : Word w)
    (ord : ordinal.val = ((siteOrder (Y)).entries.symm v).val)
    (headerFit : (header pub).val + 32 ≤ 2 ^ w)
    (rowFit : endAddress D + words B.recordLimit (selectedLayers B f hf T hT X z) ≤ 2 ^ w) :
    (selectedTrees B f hf T hT X z (endAddress D) v).address =
      (TerminalRootGather.Layout.ofHeader degree pub (header pub) ordinal vertex).root := by
  apply selectedTrees_address_ofBootstrap B f hf T hT X z D baseBits laneBits tab v degree pub
    (header pub) ordinal vertex calendar ord _ rowFit
  intro j hj
  have bound := j.isLt
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (by omega : j.val < 2 ^ w),
    Nat.mod_eq_of_lt (by omega)]
  exact entry.headers j (by omega) (by omega) (by omega)

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
