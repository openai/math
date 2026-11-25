import OAI.Computability.VPVNP.RAMMemory
import OAI.Computability.VPVNP.RAMProgram
import OAI.ThreeFlat.Diagonal.ApproximateImage

namespace OAI
/-! # External memory addresses of the team and absolute step fields -/

namespace ThreeFlat.RAM.TickReadFields

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Diagonal.ApproximateImage

variable {w d nt ns np a : ℕ}

private abbrev rest (np a : ℕ) := np+(a+(a+(a+a)))

def teamPin (d ns np a : ℕ) (i : Fin nt) : Fin (pinCount d nt ns np a) :=
  Fin.natAdd d (Fin.castAdd (ns+rest np a) i)

def stepPin (d nt np a : ℕ) (i : Fin ns) : Fin (pinCount d nt ns np a) :=
  Fin.natAdd d (Fin.natAdd nt (Fin.castAdd (rest np a) i))

@[simp] theorem teamPin_val (i : Fin nt) : (teamPin d ns np a i).val = d+i.val := rfl

@[simp] theorem stepPin_val (i : Fin ns) : (stepPin d nt np a i).val = d+(nt+i.val) := rfl

variable (D : Fin d → Bool) (params : Fin np → Bool) (oldA newA oldC newC : Fin a → Bool)
  (team step : ℕ)

/-- The initialization header can contain arbitrary words before and after this tick. -/
def HasFields (hdr : ℕ → Word w) (off : ℕ) : Prop :=
  ∀ j : Fin (pinCount d nt ns np a), hdr (off+j.val) = Fin.ofNat _
    ((fields D (digits team nt) (digits step ns) params oldA newA oldC newC) j).toNat

variable {D params oldA newA oldC newC team step} {hdr : ℕ → Word w} {off S : ℕ}

private theorem get (loc : HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (j : Fin (pinCount d nt ns np a)) :
    initialMemory S hdr (off+j.val) = Fin.ofNat _
      ((fields D (digits team nt) (digits step ns) params oldA newA oldC newC) j).toNat := by
  have hj := j.isLt
  rw [initialMemory, ite_eq_left (by omega)]
  exact loc j

/-- Little-endian word cells at offset `off+d` hold the team identifier. -/
theorem team_bit (loc : HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (i : Fin nt) :
    initialMemory S hdr (off+d+i.val) = Fin.ofNat _ (team.testBit i.val).toNat := by
  simpa only [teamPin_val, Nat.add_assoc, fields, teamPin, Fin.append_left, Fin.append_right,
    digits, Fin.val_natAdd, Fin.val_castAdd] using get loc bound (teamPin d ns np a i)

/-- The absolute step immediately follows the team identifier. -/
theorem step_bit (loc : HasFields (nt:=nt) (ns:=ns) D params oldA newA oldC newC team step hdr off)
    (bound : off+pinCount d nt ns np a ≤ S) (i : Fin ns) :
    initialMemory S hdr (off+d+nt+i.val) = Fin.ofNat _ (step.testBit i.val).toNat := by
  simpa only [stepPin_val, Nat.add_assoc, fields, stepPin, Fin.append_left, Fin.append_right,
    digits, Fin.val_natAdd, Fin.val_castAdd] using get loc bound (stepPin d nt np a i)

end ThreeFlat.RAM.TickReadFields

end OAI
