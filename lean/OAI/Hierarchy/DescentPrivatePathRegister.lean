import OAI.Hierarchy.DescentChronologicalHeld
import OAI.Hierarchy.DescentRawArchiveCounter
import OAI.Hierarchy.DescentTerminalObservedExponent
import OAI.Hierarchy.DescentChronologicalPrivate

namespace OAI
/-! # The actual private-bit register of each retained history branch -/

namespace Hierarchy.DescentSixParty.NativeBranch
open Computability.VPVNP.BurstRAM PrivateRAM DescentHistoryOrder DescentKernelHistory DescentBundleHistory
open DescentCompiler DescentHostDegree DescentInitialHost Catalyst DescentTerminalObservedExponent
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
variable {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0 < p)
set_option quotPrecheck false
local notation "A" => NativeBranch.archive X G S b hp
local notation "N" => ((Epochs.finish G hu he r).state c).graph

theorem held_volume {bw word : ℕ} {m : Memory bw} (held : b.path.Held word m) :
    m word=(volume N (A).bit.recipe:Computability.VPVNP.BurstRAM.Word bw) := by
  have eq:=archive_private X G S b hp
  change (∑v,∑h,((A).bit.recipe v).hiddenWidth h)=b.path.privateCharge at eq
  rw [DescentTerminalObservedExponent.volume,eq]
  exact held

theorem exponent (sh : WorldShape p R (A).bit) {rows bw K : ℕ}
    (slot : DescentTerminalPrivateCount.Slots (fun v=>(sh.sites v).recipe hp)↪Fin rows)
    (D : DescentDistinctRAM.Banks) (O : DescentPrivateExponentRAM.Banks) (m : Memory bw)
    (room : D.Room bw K rows) (later : O.Room bw) (lower : O.totalBits<D.flags)
    (held : b.path.Held O.totalBits m)
    (input : D.Read (DescentTerminalPrivateCount.tags _ slot) m)
    (locality : DescentDistinctWindow.Local (DescentTerminalPrivateCount.tags _ slot) K)
    (startAddr : O.usedWords=D.starts+rows) :
    let out:=image hp N (A).bit.recipe sh.sites slot D O m (K:=K)
    ((D.program bw K rows).seq (O.program bw p)).Exec m out
      (((4+rows*(2*(D.fresh K).work+4))+(10+(3+12*rows)))+O.steps p) ∧
    out O.deadBits=(∑v,((sh.sites v).recipe hp).deadBits:ℕ) :=
  ⟨DescentTerminalObservedExponent.run hp N (A).bit.recipe sh.sites slot D O m room input locality startAddr later,
    DescentTerminalObservedExponent.read hp N (A).bit.recipe sh.sites slot D O m room later lower (held_volume X G S b hp held)⟩

end
end Hierarchy.DescentSixParty.NativeBranch

end OAI
