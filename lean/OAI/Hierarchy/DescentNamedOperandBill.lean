import OAI.Hierarchy.DescentNamedSiteBill
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentCalendarNodeWidths
import OAI.Hierarchy.DescentPrivateShapeNumbers

namespace OAI
/-! # Payload bit counts in genuine terminal nodes of the named history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentKernelHistory DescentResetInvoice Catalyst Chronology
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

private theorem carry_width {P : Type} {d : ℕ} {bits : P → ℕ}
    {W W' : MarkedWorld F d P bits} {a : Archive W} (pkg : ArchiveTransport a W') {M : ℕ}
    (prior : a.bit.WidthBound M) : pkg.data.bit.WidthBound M :=
  (pkg.carry (fun _ next => PLift (next.bit.WidthBound M)) ⟨prior⟩).down

private theorem rename_width {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (a : Archive W) (sites : Equiv.Perm W.graph.Site) (edges : Equiv.Perm W.graph.Edge) {M : ℕ}
    (prior : a.bit.WidthBound M) : (renamedArchive a sites edges).bit.WidthBound M :=
  fun v node => prior (sites.symm v) node

private theorem changeArchive {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (source destination : Archive W) {M : ℕ} (eqn : source = destination)
    (bound : source.bit.WidthBound M) : destination.bit.WidthBound M := eqn ▸ bound

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

/-- The physical naming of the seed preserves each original node's payload width. -/
theorem node_width : o.archive.bit.WidthBound (3*s) :=
  changeArchive o.archivePackage.data o.archive (archive_eq o).symm
    (carry_width o.archivePackage (rename_width (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
      (BitDescription.initial_width X S.copies s c)))

end Origin

section
variable {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "s₀" => S.firstWidth G.b p
local notation "archive" => Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp
local notation "K" => (8*(G.C+G.k+G.b+2)+3)

variable {U : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width)))
    (fun _ => S.firstWidth G.b p * 1)} {i z' D : ℕ}
    {cur : Reached U G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z' D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (before : Path b.origin.source cur) (whole : before.whole p)

theorem Branch.prefix_node_bits (hh : 0<S.height) (base : G.b≤2^S.capGain) :
    (before.archive p hp b.origin.archive whole).bit.WidthBound (p*S.epochPower^(operandExponent G S)) :=by
  have Tpos : 0<S.epochPower := Nat.two_pow_pos _
  have two : 2≤S.epochPower := by
    unfold AtomSchedule.epochPower
    exact Nat.one_lt_pow hh.ne' (by decide : 1<2)
  have fixed : K≤S.epochPower^K := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left two _)
  have sBound := S.first_width_payload hh base p
  have fee : K*s₀≤p*S.epochPower^(operandExponent G S) := by
    calc
      _ ≤ S.epochPower^K*(p*S.epochPower^S.localGrainExponent) := Nat.mul_le_mul fixed sBound
      _ = p*S.epochPower^(K+S.localGrainExponent) := by rw [pow_add];ring
      _ ≤ _ := Nat.mul_le_mul_left p (Nat.pow_le_pow_right Tpos (Nat.le_add_right ..))
  have hb : 0<G.b := G.base_pos
  have zroom : S.grainAt G.b p 0≤ s₀ := Nat.le_mul_of_pos_right _ hb
  apply Chronology.Path.widths p hp _ before whole
  · intro v n
    exact (b.origin.node_width v n).trans
      ((Nat.mul_le_mul_right s₀ (show 3≤K by omega)).trans fee)
  · calc
      _ = (8*(G.C+G.k+G.b+2))*S.grainAt G.b p 0 := by ring
      _ ≤ K*s₀ := Nat.mul_le_mul (by omega) zroom
      _ ≤ _ := fee
  · exact (Nat.mul_le_mul_right s₀ (show 2≤K by omega)).trans fee
  · calc
      2^S.capGain*p ≤ S.epochPower^S.capGain*p := Nat.mul_le_mul_right p (Nat.pow_le_pow_left two _)
      _ = p*S.epochPower^S.capGain := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left p (Nat.pow_le_pow_right Tpos (Nat.le_add_left ..))

theorem Branch.node_bits (hh : 0<S.height) (base : G.b≤2^S.capGain) :
    (archive).bit.WidthBound (p*S.epochPower^(operandExponent G S)) :=
  Branch.prefix_node_bits X G S b hp b.path (b.path.recorded_whole p b.recorded) hh base

theorem Branch.site_operand_volume (hh : 0<S.height) (base : G.b≤2^S.capGain)
    (v : ((Epochs.finish G hu he r).state c).graph.Site) :
    (∑x,((archive).bit.recipe v).nodeBits x) ≤ p*S.epochPower^(operandExponent G S+S.localTokenExponent) := by
  apply (archive).bit.local_payload S (Branch.site_nodes X G S b hp hh v)
    (Branch.node_bits X G S b hp hh base v)
  exact (pow_add _ _ _).ge

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
