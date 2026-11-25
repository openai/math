import OAI.ThreeFlat.RAM.TickPrefix
import OAI.ThreeFlat.RAM.TickMarkerSwitch
import OAI.ThreeFlat.RAM.TickIdentity

namespace OAI
/-! # Physical tick dispatch and the identity summand in one native text -/

noncomputable section

namespace ThreeFlat.RAM.TickFrontROM

open scoped Fin.CommRing
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology

def phase : Fin 7 → Phase
  | 0 => .idle | 1 => .opening | 2 => .closing | 3 => .propose
  | 4 => .scan | 5 => .evaluate | _ => .clear

def phaseNo (ph : Phase) : Fin 7 := ⟨ph.tag, by cases ph <;> decide⟩

@[simp] theorem phase_phaseNo (ph : Phase) : phase (phaseNo ph) = ph := by cases ph <;> rfl

abbrev Labels (w k n : ℕ) (c : Clock) :=
  TickPrefix.Labels w k c ⊕ ((Fin 7 × Fin 4) ⊕ (Fin 42 ⊕ (Fin 1 ⊕ Fin n)))

abbrev Reg (w k : ℕ) (c : Clock) := TickPrefix.Slots w k c ⊕ Fin 7

variable {w k n s : ℕ} {c : Clock}

def prefixPC (loc : Labels w k n c → Fin s) (i : TickPrefix.Labels w k c) := loc (.inl i)
def switchPC (loc : Labels w k n c → Fin s) (i : Fin 7) (j : Fin 4) := loc (.inr (.inl (i,j)))
def idPC (loc : Labels w k n c ↪ Fin s) : Fin 42 ↪ Fin s :=
  ⟨fun i => loc (.inr (.inr (.inl i))), fun _ _ h => by simpa using loc.injective h⟩
def success (loc : Labels w k n c → Fin s) := loc (.inr (.inr (.inr (.inl 0))))
def historyPC (loc : Labels w k n c → Fin s) (i : Fin n) := loc (.inr (.inr (.inr (.inr i))))

variable {r : ℕ}

def prefixReg (reg : Reg w k c ↪ Fin r) : TickPrefix.Slots w k c ↪ Fin r :=
  ⟨fun i => reg (.inl i),fun _ _ h => Sum.inl.inj (reg.injective h)⟩
def idReg (reg : Reg w k c ↪ Fin r) : Fin 7 ↪ Fin r :=
  ⟨fun i => reg (.inr i),fun _ _ h => Sum.inr.inj (reg.injective h)⟩
def switchReg (reg : Reg w k c ↪ Fin r) : Fin 2 ↪ Fin r := (Fin.castAddEmb 5).trans (idReg reg)

def marker (regions : TickIdentity.Regions) (i : Fin 7) : Word w :=
  TickControlHeader.markerAddr (phase i) regions.oldAux regions.newAux

/-- All entries used for decoding physical identifiers, selecting the shared
marker, checking both zero auxiliary endpoints and comparing the external
chunks are emitted here. The last bank contains the history computation. -/
def emit (loc : Labels w k n c ↪ Fin s) (reg : Reg w k c ↪ Fin r) (keys : TickPrefix.Keys k)
    (a : ℕ) (regions : TickIdentity.Regions) (hEntry : Phase → Fin n)
    (history : Fin n → Instr w s r k) : Labels w k n c → Instr w s r k
  | .inl i => TickPrefix.emit (prefixPC loc) (prefixReg reg) keys
      (fun ph => switchPC loc (phaseNo ph) 0) i
  | .inr (.inl (i,j)) => TickMarkerSwitch.emit (switchPC loc i) (switchReg reg) (marker regions i)
      (idPC loc (TickIdentity.block w a regions).first) (historyPC loc (hEntry (phase i))) j
  | .inr (.inr (.inl i)) => (TickIdentity.block w a regions).emit (idPC loc) (idReg reg) Fin.elim0 (success loc) i
  | .inr (.inr (.inr (.inl _))) => .accept
  | .inr (.inr (.inr (.inr i))) => history i

def allPC (w k n : ℕ) (c : Clock) := (Fintype.equivFin (Labels w k n c)).toEmbedding

/-- Auxiliary and chunk lengths occur in instruction constants. The front
text contributes at most 300 labels and takes 85 registers. -/
theorem labels_le : Fintype.card (Labels w k n c) ≤ 300+n := by
  have h := TickPrefix.labels_le w k c
  simp only [Labels,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at h ⊢
  omega

theorem regs_le : Fintype.card (Reg w k c) ≤ 85 := by
  have h := TickPrefix.slots_le w k c
  simp only [Reg,Fintype.card_sum,Fintype.card_fin] at h ⊢
  omega

def machine (reg : Reg w k c ↪ Fin r) (data : Fin k → Word w) (keys : TickPrefix.Keys k)
    (a : ℕ) (regions : TickIdentity.Regions) (hEntry : Phase → Fin n)
    (history : Fin n → Instr w (Fintype.card (Labels w k n c)) r k) :
    Machine w (Fintype.card (Labels w k n c)) r k where
  entry := prefixPC (allPC w k n c) (.inl (0,0))
  code pc := emit (allPC w k n c) reg keys a regions hEntry history ((Fintype.equivFin _).symm pc)
  publicData := data

theorem installed (reg : Reg w k c ↪ Fin r) (data : Fin k → Word w) (keys : TickPrefix.Keys k)
    (a : ℕ) (regions : TickIdentity.Regions) (hEntry : Phase → Fin n)
    (history : Fin n → Instr w (Fintype.card (Labels w k n c)) r k) (i : Labels w k n c) :
    (machine reg data keys a regions hEntry history).code (allPC w k n c i) =
      emit (allPC w k n c) reg keys a regions hEntry history i := by
  simp [machine,allPC]

end ThreeFlat.RAM.TickFrontROM

end
end OAI
