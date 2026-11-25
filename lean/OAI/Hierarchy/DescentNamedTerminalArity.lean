import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentTerminalArity

namespace OAI
/-! # Scalar arity in genuine terminal nodes of the named history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentKernelHistory DescentResetInvoice Catalyst Chronology
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

attribute [local irreducible] Origin.archivePackage site edge

private theorem carry_arity {P : Type} {d : ℕ} {bits : P → ℕ}
    {W W' : MarkedWorld F d P bits} {a : Archive W} (pkg : ArchiveTransport a W') {M : ℕ}
    (prior : a.bit.ArityBound M) : pkg.data.bit.ArityBound M :=
  (pkg.carry (fun _ next => PLift (next.bit.ArityBound M)) ⟨prior⟩).down

private theorem rename_arity {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (a : Archive W) (sites : Equiv.Perm W.graph.Site) (edges : Equiv.Perm W.graph.Edge) {M : ℕ}
    (prior : a.bit.ArityBound M) : (renamedArchive a sites edges).bit.ArityBound M :=
  fun v node => prior (sites.symm v) node

private theorem arity_mono {P : Type} {d : ℕ} {bits : P → ℕ}
    {W : MarkedWorld F d P bits} {b : BitDescription W} {x y : ℕ}
    (h : b.ArityBound x) (le : x ≤ y) : b.ArityBound y :=
  fun v n => (h v n).trans le

private theorem changeArchive {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (source destination : Archive W) {M : ℕ} (eqn : source = destination)
    (bound : source.bit.ArityBound M) : destination.bit.ArityBound M := eqn ▸ bound

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k}
    (o : Origin (S:=S) (s:=s) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)

-- Unfold the archive function before giving it an origin, so conversion never
-- evaluates the seed's site and edge permutations.
private theorem archive_fun_eq :
    @Origin.archive F _ cp pins X G S q ε k z wire s c digits =
      fun (root : Origin (S:=S) (s:=s) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits) =>
        (Origin.archivePackage root).data := rfl

private theorem archive_eq : o.archive = (Origin.archivePackage o).data :=
  congrFun (archive_fun_eq (X:=X) (G:=G) (S:=S) (q:=q) (ε:=ε) (k:=k) (z:=z)
    (wire:=wire) (s:=s) (c:=c) (digits:=digits)) o

/-- The physical naming of the seed preserves each original node's scalar arity. -/
theorem initial_arity : o.archive.bit.ArityBound 3 :=
  changeArchive o.archivePackage.data o.archive (archive_eq o).symm
    (carry_arity o.archivePackage (rename_arity (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
      (BitDescription.initial_arity_bound X S.copies s c)))

end Origin

section
variable {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
local notation "epochWire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q" => (1/((s:ℝ)*(epochWire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q*(epochWire:ℝ)
local notation "resetDepth" => GroupStage.depthBound (atRound S.rounds) n f g

theorem Branch.node_arity {he : 0 ≤ ε} {hu : 0 ≤ u} {radix : S.radix = 2^k} {R : ℕ}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice}
    (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p) :
    (Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit.ArityBound
      (max 8 (2 ^ S.capGain)) :=
  Chronology.Path.arities p hp b.origin.archive b.path (b.path.recorded_whole p b.recorded)
    (arity_mono (Origin.initial_arity b.origin) ((show 3 ≤ 8 by decide).trans (Nat.le_max_left ..)))

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
