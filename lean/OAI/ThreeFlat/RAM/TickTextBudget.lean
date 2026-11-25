import OAI.ThreeFlat.RAM.TickMachine

namespace OAI
/-! # Fixed text sizes for every physical phase of an age-dependent tick -/

namespace ThreeFlat.RAM.TickMachine

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr TickActiveROM BitLayout Contraction
open scoped Fin.CommRing

noncomputable section
variable {w k n m : ℕ}

private def labelEquiv {C S E T : Type} :
    Label w k n m C S E T ≃ (C ⊕ (T ⊕ (Fin n ⊕ (Fin 22 ⊕ (S ⊕ (Fin m ⊕ E)))))) where
  toFun
    | .control x => .inl x
    | .writeClock x => .inr (.inl x)
    | .navigate x => .inr (.inr (.inl x))
    | .bound x => .inr (.inr (.inr (.inl x)))
    | .readChunk x => .inr (.inr (.inr (.inr (.inl x))))
    | .prepare x => .inr (.inr (.inr (.inr (.inr (.inl x)))))
    | .run x => .inr (.inr (.inr (.inr (.inr (.inr x)))))
  invFun
    | .inl x => .control x
    | .inr (.inl x) => .writeClock x
    | .inr (.inr (.inl x)) => .navigate x
    | .inr (.inr (.inr (.inl x))) => .bound x
    | .inr (.inr (.inr (.inr (.inl x)))) => .readChunk x
    | .inr (.inr (.inr (.inr (.inr (.inl x))))) => .prepare x
    | .inr (.inr (.inr (.inr (.inr (.inr x))))) => .run x
  left_inv x := by cases x <;> rfl
  right_inv
    | .inl _ | .inr (.inl _) | .inr (.inr (.inl _))
    | .inr (.inr (.inr (.inl _))) | .inr (.inr (.inr (.inr (.inl _))))
    | .inr (.inr (.inr (.inr (.inr (.inl _)))))
    | .inr (.inr (.inr (.inr (.inr (.inr _))))) => rfl

variable {F : Type*} [Field F] [Fintype F] {p H J : ℕ}
variable (A : Layout) (c : Diagonal.TickChronology.Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)

theorem seed_binds : (TickWeightedBank.seed (k:=k) fit).binds = 3*(Fintype.card F*Fintype.card F)+3 := by
  have h := HistoryFieldSeed.fieldExpr_steps (K:=k) (codec (TickWeightedBank.shape F p H J) fit)
      (mulBase p H J)
  rw [Term.steps_eq] at h
  unfold TickWeightedBank.seed
  omega

theorem active_count :
    Fintype.card (Active (k:=k) (n:=n) (m:=m) A c fit) ≤
      3100 + 9*(Fintype.card F*Fintype.card F) + n + m := by
  have h := TickHistoryCore.labels_le (k:=k) A.auxRequest (A.header w)
  have s := TickGroupScanBank.labels_le w k A.scan
  have b := TickClockWriter.binds (w:=w) (k:=k) c A.bits A.teams A.clockWords
      (A.control : Word w) (A.control+1 : ℕ)
  simp only [TickHistoryCore.Labels, Fintype.card_sum, Fintype.card_fin] at h
  simp only [TickGroupScanBank.Labels, Fintype.card_sum, Fintype.card_fin] at s
  rw [Fintype.card_congr (labelEquiv (w:=w) (k:=k) (n:=n) (m:=m))]
  simp only [Fintype.card_sum,Fintype.card_fin,TickSeedTail.count,Term.labels_eq,seed_binds]
  unfold Layout.aux Layout.clock
  omega

/-- Each subroutine reuses the same physical register bank after its
predecessor has returned. The field term, guarded scans, and decoding occupy
fixed numbers of registers; the only variable procedure counts occur here. -/
def registers {nr mr u : ℕ}
    (size : 400+3*(Fintype.card F*Fintype.card F)+nr+mr ≤ u) : Registers A c fit nr mr u k := by
  have au : (A.aux w k).binds ≤ 308 := by
    have h := TickRequestStream.program_binds A.auxRequest (TickAuxRequestGen.row (k:=k) (A.header w))
    have j := TickAuxRequestGen.row_binds (k:=k) (A.header w)
    unfold Layout.aux
    omega
  have cl : (A.clock w k c).binds ≤ 180 := TickClockWriter.binds c A.bits A.teams A.clockWords _ _
  have scan := TickGroupScanBank.binds_le w k A.scan
  have coeff := seed_binds (k:=k) fit
  exact ⟨Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),
    Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),
    Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),
    Fin.castLEEmb (by omega),Fin.castLEEmb (by omega),Fin.castLEEmb (by omega)⟩

def frontRegisters {u : ℕ} (size : 85 ≤ u) : TickFrontROM.Reg w k c ↪ Fin u :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (TickFrontROM.regs_le.trans size))

/-- After adding the actual two procedure tables, this bound is constant in
the age for any fixed-size navigation and slot preparation text. -/
theorem text_count :
    Fintype.card (All (k:=k) (n:=n) (m:=m) A c fit) ≤
      3400 + 9*(Fintype.card F*Fintype.card F) + n + m := by
  have h := TickFrontROM.labels_le (w:=w) (k:=k) (c:=c)
    (n:=Fintype.card (Active (k:=k) (n:=n) (m:=m) A c fit))
  have a := active_count (k:=k) (n:=n) (m:=m) A c fit
  exact h.trans (by omega)

end

end ThreeFlat.RAM.TickMachine

end OAI
