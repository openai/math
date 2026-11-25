import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRelease
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalActual
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyCost

/-! # Peak space and child-call charges of the complete selected repair program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims Space InterchangeROM InterchangeAddress
  NearSquareRoot.Interchange.Template InterchangeROMStageVolume Interchange.StageScript InterchangeSpectralFibre

def overheadRate (p n q : ℕ) := 256*(4+(7*n+2*q)*(2*p+6))

def releaseRate (p n q s L : ℕ) :=
  let o := overheadRate p n q
  3+L+o+(4*s+8)*(L+3*n*o+2)

theorem computable_releaseRate {T : Type} [Primcodable T] {p n q s L : T → ℕ}
    (hp : Computable p) (hn : Computable n) (hq : Computable q) (hs : Computable s) (hL : Computable L) :
    Computable fun x => releaseRate (p x) (n x) (q x) (s x) (L x) := by
  let add := Primrec.nat_add.to_comp
  let mul := Primrec.nat_mul.to_comp
  have o : Computable fun x => overheadRate (p x) (n x) (q x) :=
    mul.comp (.const 256) (add.comp (.const 4)
      (mul.comp (add.comp (mul.comp (.const 7) hn) (mul.comp (.const 2) hq))
        (add.comp (mul.comp (.const 2) hp) (.const 6))))
  exact add.comp (add.comp (add.comp (.const 3) hL) o)
    (mul.comp (add.comp (mul.comp (.const 4) hs) (.const 8))
      (add.comp (add.comp hL (mul.comp (mul.comp (.const 3) hn) o)) (.const 2)))

theorem resource_bounds (h : Tree) (N width p n q s L : ℕ) :
    let M := InterchangeROMStageVolume.mass h N width
    let r := 1+N*(2+width*(2*p+2))
    let ov := 256*(h.count+2+(7*n+2*q)*(r+1)+1)
    let C := releaseRate p n q s L
    1+(4*s+8)*(L*M+3*n*ov+2) ≤ C*M ∧ L*M+ov+1 ≤ C*M := by
  dsimp only
  let M := InterchangeROMStageVolume.mass h N width
  let o := overheadRate p n q
  have hpos : 1 ≤ M := by dsimp [M,InterchangeROMStageVolume.mass]; omega
  have hsmall : (1+N*(2+width*(2*p+2)))+1 ≤ (2*p+6)*M := by
    dsimp [M,InterchangeROMStageVolume.mass]; ring_nf; omega
  have hhdr : h.count+3 ≤ 4*M := by dsimp [M,InterchangeROMStageVolume.mass]; omega
  have hov : 256*(h.count+2+(7*n+2*q)*(1+N*(2+width*(2*p+2))+1)+1) ≤ o*M := by
    calc
      _ ≤ 256*(4*M+(7*n+2*q)*((2*p+6)*M)) := by
        apply Nat.mul_le_mul_left
        have e := Nat.mul_le_mul_left (7*n+2*q) hsmall
        omega
      _ = _ := by dsimp [o,overheadRate]; ring
  have inner : L*M+3*n*(256*(h.count+2+(7*n+2*q)*(1+N*(2+width*(2*p+2))+1)+1))+2 ≤
      (L+3*n*o+2)*M := by
    calc
      _ ≤ L*M+3*n*(o*M)+2*M := Nat.add_le_add (Nat.add_le_add_left
        (Nat.mul_le_mul_left (3*n) hov) (L*M)) (by omega)
      _ = _ := by ring
  constructor
  · calc
      _ ≤ M+(4*s+8)*((L+3*n*o+2)*M) :=
        Nat.add_le_add hpos (Nat.mul_le_mul_left _ inner)
      _ ≤ (3*M+L*M+o*M)+(4*s+8)*((L+3*n*o+2)*M) := by
        apply Nat.add_le_add_right
        omega
      _ = (3+L+o+(4*s+8)*(L+3*n*o+2))*M := by ring
  · calc
      _ ≤ L*M+o*M+M := Nat.add_le_add (Nat.add_le_add_left hov _) hpos
      _ ≤ (3*M+L*M+o*M)+(4*s+8)*((L+3*n*o+2)*M) := by
        omega
      _ = (3+L+o+(4*s+8)*(L+3*n*o+2))*M := by ring

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D : Type}
variable [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

abbrev wideBank (x : Data) (P G S : Tape) (f : ℕ) (pay : Series D) (u : x.Wide P G S f D) :=
  SweepBank.packed (SweepBank.layout P G S x.a x.m x.b f) pay u

abbrev shortBank (x : Data) (P G S : Tape) (f : ℕ) (pay : Series D) (u : x.Short P G S f D) :=
  SweepBank.packed (SweepBank.layout P G S x.a x.m x.b f) pay u

abbrev transfer (h : Data.Valid j threshold x) (P G S : Tape) (f : ℕ) (pay : Series D) :=
  Transition x.spec x.half (flags ∘ Prod.fst) (lift (directions false x.half))
    (lift (directions true x.half)) (Data.stagePayload h) (wideBank x P G S f pay) (shortBank x P G S f pay)

def phaseCalls (h : Data.Valid j threshold x) (a : Leaf) :=
  price (Raw.rowCount x.m * cost (Data.wordPrice h) (Data.predictorStage h))
    (x.labels * Raw.checkCount x.m) x.m (0,a)

def compiledRate (x : Data) (L : ℕ) := releaseRate x.modulusIndex (x.labels * rows x)
  (x.labels * checks x) (Sizes.pencilOrder x.m) L

theorem computable_compiledRate {L : Data → ℕ} (h : Computable L) :
    Computable fun x => compiledRate x (L x) :=
  computable_releaseRate Data.primrec_modulusIndex.to_comp
    (Primrec.nat_mul.to_comp.comp (Data.primrec_header 4).to_comp
      ((Raw.primrec_rowCount.comp (Data.primrec_header 2)).to_comp))
    (Primrec.nat_mul.to_comp.comp (Data.primrec_header 4).to_comp
      ((Raw.primrec_checkCount.comp (Data.primrec_header 2)).to_comp))
    ((Sizes.primrec_pencilOrder.comp (Data.primrec_header 2)).to_comp) h

/-- The checked numerical template pays for every invocation of the recursive machine.
Each of the tape and return peaks reserves only one live child. -/
theorem program_of_phases (h : Data.Valid j threshold x) (pay : Series D) (width : ℕ)
    (hw : pay.count ≤ width) (env : Env) (L childTime childCap childDepth : ℕ)
    (run : ∀ k u v, transfer h P G S f pay k u v → ∀ r base, DeckCap base r →
      let H := send (InterchangeROMAddress.header f P G S)
      let M := InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
      BoundedFits env (commands x k) (pile 0 (packet H u) r) (pile 0 (packet H v) r)
        (L*M + phaseCalls h k*childTime) (base+(L*M+childCap)) (L*M+childDepth))
    (u : x.Wide P G S f D) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let H := send (InterchangeROMAddress.header f P G S)
    let M := InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
    let localBound := compiledRate x L * M
    BoundedFits env (program x) (pile 0 (packet H (wideBank x P G S f pay u)) r)
      (pile 0 (packet H (wideBank x P G S f pay (swapPayload u))) r)
      (localBound + x.calls*childTime) (base+(localBound+childCap)) (localBound+childDepth) := by
  let ord := SweepBank.layout P G S x.a x.m x.b f
  let H := send (InterchangeROMAddress.header f P G S)
  let M := InterchangeROMStageVolume.mass H ord.count width
  let shape := 1+ord.count*(2+width*(2*x.modulusIndex+2))
  let n := x.labels * rows x
  let q := x.labels * checks x
  let s := Sizes.pencilOrder x.m
  let pc := Raw.rowCount x.m*cost (Data.wordPrice h) (Data.predictorStage h)
  let ac (k : Leaf) (_ : List Tree) : Allowance :=
    ⟨L*M+phaseCalls h k*childTime,L*M+childCap,L*M+childDepth⟩
  have bnd := bounded_from_actual n q shape (fun _ => LocalTable.Lift.bank_length ..)
    (fun _ => LocalTable.Lift.bank_length ..)
    (bank_small ord (fun _ => pay) Prod.mk width (fun _ => hw))
    (bank_small ord (fun _ => pay) Prod.mk width (fun _ => hw))
    s (commands x) ac H env run pc childTime (L*M) (L*M+childCap) (L*M+childDepth)
    (fun _ _ _ => ⟨le_rfl,le_rfl,le_rfl⟩) u r base hr
  dsimp only at bnd ⊢
  have he : schedule x.spec x.half (flags ∘ Prod.fst) (lift (directions false x.half))
      (lift (directions true x.half)) ((Data.stagePayload h)^[s]) u = swapPayload u := Data.schedule_payload h u
  set_option backward.isDefEq.respectTransparency false in
    rw [he] at bnd
  obtain ⟨ht,hs⟩ := resource_bounds H ord.count width x.modulusIndex n q s L
  have hcost : 4*s*pc+4*q*x.m ≤ x.calls := by
    simpa only [s,pc,q,checks,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Data.predictor_charge h
  apply bnd.mono (Nat.add_le_add ht (Nat.mul_le_mul_right childTime hcost))
  · let o := 256*(H.count+2+(7*n+2*q)*(shape+1)+1)
    change base+(L*M+childCap)+o ≤ base+(releaseRate x.modulusIndex n q s L*M + childCap)
    have z : L*M+o+1 ≤ releaseRate x.modulusIndex n q s L*M := hs
    calc
      base+(L*M+childCap)+o = base+(L*M+o)+childCap := by ac_rfl
      _ ≤ base+(releaseRate x.modulusIndex n q s L*M)+childCap :=
        Nat.add_le_add_right (Nat.add_le_add_left ((Nat.le_succ _).trans z) _) _
      _ = _ := Nat.add_assoc ..
  · let o := 256*(H.count+2+(7*n+2*q)*(shape+1)+1)
    change L*M+childDepth+o+1 ≤ releaseRate x.modulusIndex n q s L*M+childDepth
    calc
      L*M+childDepth+o+1 = (L*M+o+1)+childDepth := by ac_rfl
      _ ≤ _ := Nat.add_le_add_right hs _

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
