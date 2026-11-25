import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankEstimate

/-! # Computable time and space coefficients for both compiled check banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM InterchangeROMAddress InterchangeAddress InterchangeBatch
open Physical (Positions Allowance Bank sweep directions)
open InterchangeSpectralFibre (lift)

def price (a m l s b p half : ℕ) (inv : Bool) : ℕ × ℕ :=
  let n := 2*(l*s)
  let v := packetRate n p (Sweep.headerPrice b (a+m+a))
  let k := Sweep.rate b (a+m+a) p half inv
  (clockRate m n k v,spaceRate k v)

theorem computable_price {T : Type} [Primcodable T] {a m l s b p half : T → ℕ} {inv : T → Bool}
    (ha : Computable a) (hm : Computable m) (hl : Computable l) (hs : Computable s)
    (hb : Computable b) (hp : Computable p) (hh : Computable half) (hi : Computable inv) :
    Computable fun t => price (a t) (m t) (l t) (s t) (b t) (p t) (half t) (inv t) := by
  let add {f g : T → ℕ} := fun (hf : Computable f) (hg : Computable g) => Primrec.nat_add.to_comp.comp hf hg
  let mul {f g : T → ℕ} := fun (hf : Computable f) (hg : Computable g) => Primrec.nat_mul.to_comp.comp hf hg
  have n := mul (Computable.const 2) (mul hl hs)
  have j := add (add ha hm) ha
  have k := Sweep.computable_rate hb j hp hh hi
  have v := add (add (Sweep.computable_headerPrice hb j) (mul n (add (mul (Computable.const 2) hp)
    (Computable.const 12)))) (Computable.const 3)
  exact (add (Computable.const 1) (mul hm (add (add (mul (add n (Computable.const 2))
    (mul (Computable.const 160) v)) (mul n k)) (Computable.const 2)))).pair (add (mul (Computable.const 172) v) k)

variable {P G S : Dims.Tape} {p a m l s b f w : ℕ} {E : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "F" => Fin (a+m+a)

/-- The price bound uses the computed template coefficients and the actual
payload width. Additive time and peak occupancy range over the same ledger. -/
theorem charge_le (hm : 0 < m) (hb : 2 ≤ b) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ b)
    (pay : Series E) (hw : pay.count ≤ w) (half : ℕ) (inv : Bool) (child : Request b → Allowance)
    (x y : Bank R (Fin l) (X × E) (Fin s)) :
    let C := (layout P G S a m b f).count*(w+1)+1
    let k := price a m l s b p half inv
    let c := charge w half inv pay child x y
    let ledger := emitted w pay half inv x y
    c.time ≤ k.1*C + (ledger.map fun q => (child q).time).sum ∧
    c.cap ≤ k.2*C + (ledger.map fun q => (child q).cap).foldr max 0 ∧
    c.depth ≤ k.2*C + (ledger.map fun q => (child q).depth).foldr max 0 := by
  let hs := header f P G S
  let N := (layout P G S a m b f).count
  have ad := Sweep.shapeCharge_le (b:=b) (Equiv.refl F) (fun _ : Unit => P) (fun _ => G) (fun _ => S)
    (fun _ => f) (fun _ => w) (⟨0,by omega⟩ : F) (fun _ _ => .atom false) () hb ok
  have hd : (send hs).count ≤ Sweep.headerPrice b (a+m+a)*N := by
    apply le_trans _ ad
    dsimp only [Sweep.shapeCharge]
    change (send hs).count ≤ _ + _ + _ + 2001*(send hs).count + _
    omega
  have vw : N ≤ N*(w+1)+1 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have v := hd.trans (Nat.mul_le_mul_left _ vw)
  have loc := local_limits hb ok _ v pay hw half inv x y
  have tot := charge_split w half inv pay child x y
  dsimp only at loc tot ⊢
  exact ⟨tot.1.trans_le (Nat.add_le_add_right loc.1 _),
    tot.2.1.trans (Nat.add_le_add_right loc.2.1 _),tot.2.2.trans (Nat.add_le_add_right loc.2.2 _)⟩

theorem request_typed (w : ℕ) (pay : Series E) (j : F) (g : X → E → R) :
    let q := request w pay j g
    (allowed (fun _ : Unit => f) (fun _ => (layout P G S a m b f).count) (fun _ => w) () q ∧
      ∀ k, InterchangePayloadBank.Good (fun _ : Unit => pay) (fun z : R => InterchangeROMTable.numeral z.val)
        () (q.contents k)) ∧ inherited b P G S q :=
  ⟨⟨Sweep.child_allowed ..,fun _ => ⟨_,rfl⟩⟩,Sweep.child_inherited (Equiv.refl F) (fun _ : Unit => P)
    (fun _ => G) (fun _ => S) (fun _ => f) (fun _ => w) j _ ()⟩

/-- Native execution with the template-computed local prices and the recursive
clock/stack expenses of the emitted concrete requests. -/
theorem command_priced [Fact (p+1).Prime]
    (hm : 0 < m) (hb : 2 ≤ b) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ b)
    (pay : Series E) (hw : pay.count ≤ w) (parent : Cmd) (env : Env) (child : Request b → Allowance)
    (hc : ∀ q : Request b,
      (allowed (fun _ : Unit => f) (fun _ => (layout P G S a m b f).count) (fun _ => w) () q ∧
        ∀ k, InterchangePayloadBank.Good (fun _ : Unit => pay) (fun z : R => InterchangeROMTable.numeral z.val)
          () (q.contents k)) ∧ inherited b P G S q →
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) (child q))
    (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s)) :
    let h := send (header f P G S)
    let rows := layout P G S a m b f
    let C := rows.count*(w+1)+1
    let k := price a m l s b p half inv
    let qs := emitted w pay half inv x y
    Run (parent::env) (command a m l s b p half inv) (packet h (packed rows pay x ++ packed rows pay y))
      (packet h (packed rows pay (sweep (lift (directions inv (half:R))) x) ++
        packed rows pay (sweep (lift (directions inv (half:R))) y)))
      ⟨k.1*C+(qs.map fun q => (child q).time).sum,
       k.2*C+(qs.map fun q => (child q).cap).foldr max 0,
       k.2*C+(qs.map fun q => (child q).depth).foldr max 0⟩ := by
  intro h rows C k qs r base hr
  have hp : solid P := fun z hz => (ok z (by simp [hz])).1
  have hg : solid G := fun z hz => (ok z (by simp [hz])).1
  have hs : solid S := fun z hz => (ok z (by simp [hz])).1
  have run := command_bounded hb hp hg hs pay hw parent env child
    (fun j g => hc _ (request_typed w pay j g)) half inv x y r base hr
  have ht := charge_le hm hb ok pay hw half inv child x y
  exact run.mono ht.1 (Nat.add_le_add_left ht.2.1 _) ht.2.2

end InterchangeROMRepair.SweepBank

end

end NearSquareRoot
end Computability
end OAI
