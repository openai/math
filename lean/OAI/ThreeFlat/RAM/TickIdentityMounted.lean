import OAI.ThreeFlat.RAM.TickIdentity
import OAI.ThreeFlat.RAM.TickMountedPins
import OAI.ThreeFlat.RAM.TickBoundaryFields

namespace OAI
/-! # The identity branch on the mounted physical tick pins -/

namespace ThreeFlat.RAM.TickIdentity

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.ApproximateImage TickBoundaryFields

def physicalRegions (d nt ns np a : ℕ) : Regions :=
  ⟨base 2 d nt ns np a .oldAux,base 2 d nt ns np a .newAux,
    BitLayout.hiddenBase (pinCount d nt ns np a),
    base 2 d nt ns np a .oldChunk,base 2 d nt ns np a .newChunk⟩

theorem physicalFits {w d nt ns np a : ℕ} (room : 2+pinCount d nt ns np a+a < 2^w) :
    (physicalRegions d nt ns np a).Fits w a := by
  constructor <;> simp only [physicalRegions,base,Segment.number,BitLayout.hiddenBase,pinCount] at * <;> omega

theorem valid_mounted {w d nt ns np a : ℕ} (D : Fin d → Bool) (params : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (team step : ℕ) (room : 2+pinCount d nt ns np a+a < 2^w) :
    valid (physicalRegions d nt ns np a) (TickMountedPins.memory (w:=w)
      (fields D (digits team nt) (digits step ns) params oa na oc nc)) a ↔
      oa = (fun _ => false) ∧ na = (fun _ => false) ∧ oc = nc := by
  let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
  let m := TickMountedPins.memory (w:=w) pins
  have loc := TickMountedPins.has_fields (w:=w) (nt:=nt) (ns:=ns) D params oa na oc nc team step
  have read (s : Segment) (i : Fin a) : m (base 2 d nt ns np a s+i.val) =
      TickBitRelation.bitWord w ((s.select oa na oc nc) i) :=
    boundary_bit s i loc (le_refl _)
  have width : (1 : ℕ) < 2^w := by omega
  have nz : (1 : Word w) ≠ 0 := by
    intro eq
    have h := congrArg Fin.val eq
    have v : (1 : Word w).val = 1 := Nat.mod_eq_of_lt width
    simp only [v,Fin.val_zero] at h
    omega
  have inj : Function.Injective (TickBitRelation.bitWord w) := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact (nz h.symm).elim
    · exact (nz h).elim
    · rfl
  have eqz (b : Bool) : TickBitRelation.bitWord w b = 0 ↔ b = false := by
    change TickBitRelation.bitWord w b = TickBitRelation.bitWord w false ↔ b = false
    exact inj.eq_iff
  unfold valid ScanLoop.agree
  change (∀ i : Fin a, m (base 2 d nt ns np a .oldAux+i.val) = 0) ∧
    (∀ i : Fin a, m (base 2 d nt ns np a .newAux+i.val) = 0) ∧
    (∀ i : Fin a, m (base 2 d nt ns np a .oldChunk+i.val) = m (base 2 d nt ns np a .newChunk+i.val)) ↔ _
  simp only [read,Segment.select,eqz,inj.eq_iff,funext_iff]

open scoped Classical in
theorem mass_mounted {w d nt ns np a : ℕ} {F : Type*} [Semiring F] (field : FieldCode F w)
    (D : Fin d → Bool) (params : Fin np → Bool) (oa na oc nc : Fin a → Bool)
    (team step fuel : ℕ) (c : Config w 43 7)
    (entry : c.pc = (machine w a (physicalRegions d nt ns np a)).entry)
    (room : 2+pinCount d nt ns np a+a < 2^w) :
    let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
    let m := TickMountedPins.memory (w:=w) pins
    mass field (machine w a (physicalRegions d nt ns np a)).program (fuel+25+18*a) c m =
      if oa = (fun _ => false) ∧ na = (fun _ => false) ∧ oc = nc then 1 else 0 := by
  dsimp only
  let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
  let m := TickMountedPins.memory (w:=w) pins
  let A := physicalRegions d nt ns np a
  rw [mass_machine field A a fuel c m entry (physicalFits room)
    (fun i => TickMountedPins.memory_hidden pins i.val)]
  exact ite_congr (propext (valid_mounted D params oa na oc nc team step room)) (fun _ => rfl) (fun _ => rfl)


end ThreeFlat.RAM.TickIdentity

end OAI
