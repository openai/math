import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepCost

/-! # Effective scan factors for an entire packed spectral leaf -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress GeneratorSyntax LoomRegisters InterchangeBatch
open InterchangeROMRepair.Physical (Allowance)

def shapeCharge (b n j : ℕ) (h : Header) (hdr : Tree) (rows : ℕ) : ℕ :=
  maskTime b n j h rows + headerTime (numericSpec b n [(j,j)]) h pivotK pivotDegree +
    110*(hdr.count+3) + 2001*(send h).count + 2010

def scanRate (p half : ℕ) (inv : Bool) : ℕ :=
  (Physical.Broadcast.factor+10002)*(2*p+11)+SweepTable.factor p half inv

theorem computable_scanRate {X : Type} [Primcodable X] {p half : X → ℕ} {inv : X → Bool}
    (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Computable (fun x => scanRate (p x) (half x) (inv x)) :=
  Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const _)
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) hp)
      (Computable.const 11))) (SweepTable.computable_factor hp hh hi)

theorem charge_eq (b n j p half : ℕ) (inv : Bool) (h : Header) (hdr : Tree) (rows width : ℕ) :
    localCharge b n j p half inv h hdr rows width =
      shapeCharge b n j h hdr rows + scanRate p half inv*(rows*(width+1)+1) := by
  dsimp only [localCharge,shapeCharge,scanRate]
  ring

def charged (a : Allowance) (v : ℕ) : Allowance := ⟨a.time+v,a.cap+v,a.depth+v⟩

variable {I J D : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ) (pay : I → Series D)
  (j : J) (p half : ℕ) (inv : Bool)
  (x : (i : I) → domain (J:=J) (b:=b) P G B f i → D → ZMod (p+1)) (i : I)

/-- Separate the numeric cost of decoding the shape from the scan factor on ground-field data. -/
theorem native_linear_of_shape (parent : Cmd) (env : Env) (ac : Allowance) (K : ℕ)
    (hb : 2 ≤ b) (hp : solid (P i)) (hg : solid (G i)) (hs : solid (B i))
    (hw : (pay i).count ≤ l i)
    (hh : let q := request ord P G B f l pay j p x i
      let N := countRows (b:=b) ord P G B f i
      shapeCharge b n (ord j) (header (f i) (P i) (G i) (B i)) q.header N ≤ K*N)
    (hc : let q := request ord P G B f l pay j p x i
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) ac) :
    let rows := layoutRows (b:=b) ord P G B f i
    let h := send (header (f i) (P i) (G i) (B i))
    Run (parent::env) (nativeCommand b n (ord j) p half inv) (.fork h (row rows (pay i) (x i)))
      (row rows (pay i) fun k d =>
        InterchangeSpectralRequest.advance inv (half : ZMod (p+1)) j (fun k => x i k d) k)
      (charged ac ((K+scanRate p half inv)*(rows.count*(l i+1)+1))) := by
  intro rows h deck base hd
  let q := request ord P G B f l pay j p x i
  let a := nativeCost ord P G B f l pay j p half inv x i ac
  let V := rows.count*(l i+1)+1
  have weight : rows.count ≤ V := by dsimp [V]; rw [Nat.mul_add,Nat.mul_one]; omega
  have use := (native_bounded ord P G B f l pay j p half inv x i parent env ac hb hp hg hs hw hc)
    deck base hd
  have costs := native_cost_le ord P G B f l pay j p half inv x i hw ac
  dsimp only at hh costs
  rw [charge_eq] at costs
  let shape := shapeCharge b n (ord j) (header (f i) (P i) (G i) (B i)) q.header rows.count
  change a.time ≤ ac.time + (shape + scanRate p half inv*V) ∧
    a.cap ≤ ac.cap + (shape + scanRate p half inv*V) ∧
    a.depth ≤ ac.depth + (shape + scanRate p half inv*V) at costs
  have bound : shape ≤ K*V := hh.trans (Nat.mul_le_mul_left _ weight)
  apply use.mono
  · change a.time ≤ ac.time+(K+scanRate p half inv)*V
    rw [Nat.add_mul]; omega
  · change base+a.cap ≤ base+(ac.cap+(K+scanRate p half inv)*V)
    rw [Nat.add_mul]; omega
  · change a.depth ≤ ac.depth+(K+scanRate p half inv)*V
    rw [Nat.add_mul]; omega

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
