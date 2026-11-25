import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankPrice

/-! # Open execution on the exact recursive ledger of a spectral sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM InterchangeROMAddress InterchangeAddress InterchangeBatch
open Physical (Positions Allowance Bank sweep directions)
open InterchangeSpectralFibre (lift)

open private fields_map from OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankNative

/-- Each row callback is required only for the field, lane and current data that reach it. -/
theorem fields_bounded_on {A J : Type} {D : A → Type} (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree)
    (op : J → (a : A) → D a → D a) (child : J → Cmd) (cost : J → (a : A) → D a → Allowance)
    (env : Env) (js : List J) (x : (a : A) → D a)
    (hc : ∀ q ∈ calls s op js x,
      Run env (child q.1) (.fork h (enc q.2.1 q.2.2)) (enc q.2.1 (op q.1 q.2.1 q.2.2))
        (cost q.1 q.2.1 q.2.2)) :
    Run env (fields s.count child js) (packet h (s.tab fun a => enc a (x a)))
      (packet h (s.tab fun a => enc a (eval op js x a))) (fieldCost s h enc op cost js x) := by
  induction js generalizing x with
  | nil => exact fun r base hr => BoundedFits.pass (hr.pile 0 _)
  | cons j js ih =>
    let y a := op j a (x a)
    have first := bank_bounded s h (fun a => enc a (x a)) (fun a => enc a (y a)) (child j)
      (fun a => cost j a (x a)) env (fun a => hc (j,⟨a,x a⟩)
        (List.mem_append_left _ (List.mem_map.mpr ⟨a,s.complete a,rfl⟩)))
    have rest := ih y (fun q hq => hc q (List.mem_append_right _ hq))
    exact Sweep.run_join first rest

variable {P G S : Dims.Tape} {p a m l s b f w : ℕ} {E : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "F" => Fin (a+m+a)

/-- The two physical check banks execute from the recursive answers on their emitted requests. -/
theorem command_bounded_on [Fact (p+1).Prime] (hb : 2 ≤ b) (hp : solid P) (hg : solid G) (hs : solid S)
    (pay : Series E) (hw : pay.count ≤ w) (parent : Cmd) (env : Env)
    (child : Request b → Allowance)
    (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s))
    (hc : ∀ q ∈ emitted w pay half inv x y,
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) (child q)) :
    let h := send (header f P G S)
    let rows := layout P G S a m b f
    Run (parent::env) (command a m l s b p half inv) (packet h (packed rows pay x ++ packed rows pay y))
      (packet h (packed rows pay (sweep (lift (directions inv (half:R))) x) ++
        packed rows pay (sweep (lift (directions inv (half:R))) y)))
      (fieldCost (banks l s) h (fun _ => Sweep.row rows pay) (fun j _ => update inv (half:R) j)
        (fun j _ => rowCost w half inv pay child j) (order a m inv) (streams x y)) := by
  let rows := layout P G S a m b f
  let h := send (header f P G S)
  let c j := Sweep.nativeCommand b (a+m+a) j p half inv
  have run := fields_bounded_on (banks l s) h (fun _ => Sweep.row rows pay)
    (fun j _ => update inv (half:R) j) (c ∘ Fin.val)
    (fun j _ => rowCost w half inv pay child j) (parent::env) (order a m inv) (streams x y) (by
      intro q hq
      exact Sweep.native_bounded (Equiv.refl F) (fun _ : Unit => P) (fun _ => G) (fun _ => S)
        (fun _ => f) (fun _ => w) (fun _ => pay) q.1 p half inv (fun _ => q.2.2) () parent env _
        hb hp hg hs hw (hc _ (List.mem_map.mpr ⟨q,hq,rfl⟩)))
  rw [←fields_map,slots_eq,banks_count,native_eval,tab_streams,tab_streams] at run
  exact run

/-- The price is charged over the same requests that supply the recursive executions. -/
theorem command_priced_on [Fact (p+1).Prime]
    (hm : 0 < m) (hb : 2 ≤ b) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ b)
    (pay : Series E) (hw : pay.count ≤ w) (parent : Cmd) (env : Env) (child : Request b → Allowance)
    (half : ℕ) (inv : Bool) (x y : Bank R (Fin l) (X × E) (Fin s))
    (hc : ∀ q ∈ emitted w pay half inv x y,
      Run (parent::env) parent ((Request.job b).issue q) ((Request.job b).reply q) (child q)) :
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
  have run := command_bounded_on hb hp hg hs pay hw parent env child half inv x y hc r base hr
  have ht := charge_le hm hb ok pay hw half inv child x y
  exact run.mono ht.1 (Nat.add_le_add_left ht.2.1 _) ht.2.2

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI
