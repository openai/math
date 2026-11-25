import OAI.Hierarchy.DescentNamedSeedLocalNodes
import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentPrivateCounterRoom
import OAI.Hierarchy.DescentPrivatePathRegister
import OAI.Hierarchy.DescentReachedLocalNodes

namespace OAI
/-! # The native private counter and vertex order on the physically named seed trajectory -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentColonies DescentKernelHistory DescentHistoryOrder Catalyst
open Chronology DescentTerminalObservedExponent Computability.VPVNP.BurstRAM PrivateRAM GadgetNetwork
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

private theorem transferred_zero {P : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    {a : Archive W} (pkg : ArchiveTransport a V) (h : privateMass a.bit = 0) :
    privateMass pkg.data.bit = 0 :=
  (pkg.carry (fun _ b => PLift (privateMass b.bit = 0)) ⟨h⟩).down

private theorem renamed_zero {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (a : Archive W) (v : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge)
    (h : privateMass a.bit = 0) : privateMass (renamedArchive a v e).bit = 0 :=
  (named_mass a.bit v e).trans h

attribute [local irreducible] Origin.archivePackage Origin.source

private theorem mass_of_archive_eq {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (source destination : Archive W) (same : source = destination) (before : privateMass source.bit = 0) :
    privateMass destination.bit = 0 := same ▸ before

open private OrderTransfer OrderTransfer.destination orderTransfer Origin.orderFor from
  OAI.Hierarchy.DescentNamedSeedLocalNodes

private def orderOfTransfer {P : Type} {d : ℕ} {bits : P → ℕ}
    {W V : MarkedWorld F d P bits} {a : Archive W}
    (pkg : ArchiveTransport a V) (record : OrderTransfer)
    (same : record = orderTransfer pkg) (input : OrderTransfer.destination record) : DescentLocalArchiveOrder.Local pkg.data.bit := by
  subst record
  exact input

private def changeOrderArchive {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (src dst : Archive W) (same : src = dst) (order : DescentLocalArchiveOrder.Local src.bit) :
    DescentLocalArchiveOrder.Local dst.bit := same ▸ order

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
variable {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)

-- Identify the archive before projecting its dependent bit description.
private theorem archive_fun_eq :
    @Origin.archive F _ cp pins X G S q ε k z wire s c digits =
      fun (root : Origin (S:=S) (s:=s) (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits) =>
        (Origin.archivePackage root).data := rfl

private theorem archive_eq : o.archive = (Origin.archivePackage o).data :=
  congrFun (archive_fun_eq (X:=X) (G:=G) (S:=S) (q:=q) (ε:=ε) (k:=k) (z:=z)
    (wire:=wire) (s:=s) (c:=c) (digits:=digits)) o

theorem private_zero : privateMass o.archive.bit=0 :=
  mass_of_archive_eq o.archivePackage.data o.archive (archive_eq o).symm
    (transferred_zero o.archivePackage (renamed_zero (Chronology.seedArchive X S.copies s c)
    (site o.raw) (edge o.raw) (initial_mass X S.copies s c)))

private def archiveOrder : DescentLocalArchiveOrder.Local o.archive.bit :=
  changeOrderArchive o.archivePackage.data o.archive (archive_eq o).symm
    (orderOfTransfer o.archivePackage (Origin.orderFor o) rfl o.localNodes)

end Origin

section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "A" => Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp
local notation "N" => ((Epochs.finish G hu he r).state c).graph

def Branch.localNodes : DescentLocalArchiveOrder.Local (A).bit :=
  DescentLocalArchiveOrder.trajectory p hp b.origin.archive (Origin.archiveOrder b.origin) b.path (b.path.recorded_whole p b.recorded)

theorem Branch.archive_private : privateMass (A).bit=b.path.privateCharge := by
  unfold Branch.archive
  rw [Chronology.Path.archive_mass,b.origin.private_zero,Nat.zero_add]

theorem Branch.held_volume {wb header : ℕ} {m : Memory wb} (held : b.path.Held header m) :
    m header=(volume N (A).bit.recipe:Computability.VPVNP.BurstRAM.Word wb) := by
  have eq:=Branch.archive_private X G S b hp
  change (∑v,∑h,((A).bit.recipe v).hiddenWidth h)=b.path.privateCharge at eq
  rw [DescentTerminalObservedExponent.volume,eq]
  exact held

theorem Branch.private_max : privateMass (A).bit≤NativeBranch.privateMax G S p := by
  rw [Branch.archive_private X G S b hp]
  have bound := b.path.private_budget he
  have hs : 0<s₀ :=b.origin.source.atoms ▸ b.origin.source.valid.atom
  have ht : 0<S.epochPower :=Nat.two_pow_pos _
  have sw : (0:ℝ)<s₀:=by exact_mod_cast hs
  have wp : (0:ℝ)<(wire₀:ℕ):=by positivity
  have tp : (1:ℝ)≤S.epochPower:=by exact_mod_cast ht
  have cancel : q₀*(wire₀:ℝ)=1/(s₀:ℝ) :=by field_simp
  have scaled : 1 / (s₀ : ℝ) * (b.path.privateCharge : ℝ) ≤
      (S.length : ℝ) * ((privateRate G : ℝ) * (2^k : ℕ) * ε₀) := calc
    _ = q₀ * ((wire₀ : ℕ) : ℝ) * (b.path.privateCharge : ℝ) :=
      congrArg (fun a : ℝ => a * (b.path.privateCharge : ℝ)) (by simpa only [Nat.cast_pow] using cancel.symm)
    _ ≤ _ := bound
  have factor : ε₀≤((S.initialSites*S.copies:ℕ):ℝ) :=
    div_le_self (by positivity) tp
  have bound' := scaled.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left factor (by positivity : 0≤(privateRate G:ℝ)*(2^k:ℕ))) (by positivity : 0≤(S.length:ℝ)))
  have result := mul_le_mul_of_nonneg_left bound' sw.le
  rw [←mul_assoc,←mul_assoc,mul_one_div_cancel sw.ne',one_mul] at result
  unfold NativeBranch.privateMax
  rw [radix]
  push_cast at result ⊢
  exact_mod_cast (by simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using result :
    (b.path.privateCharge:ℝ)≤(S.length:ℝ)*(privateRate G:ℝ)*((2^k:ℕ):ℝ)*
      S.initialSites*((S.copies:ℝ)*s₀))

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
