import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankFields
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalPayload
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalBank
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepNative

/-! # Packed forward and reverse sweeps on both auxiliary check banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROM GeneratorSyntax InterchangeSpectralRequest InterchangeSpectralFibre

open Physical (Positions directions Allowance Bank sweep)

def order (a m : ℕ) (inv : Bool) : List (Fin (a+m+a)) :=
  let js := (List.finRange m).map (Interchange.RepairSchedule.mainSlots a m)
  if inv then js.reverse else js

def slots (a m : ℕ) (inv : Bool) : List ℕ :=
  let js := (List.range m).map (a + ·)
  if inv then js.reverse else js

theorem slots_eq (a m : ℕ) (inv : Bool) : (order a m inv).map Fin.val = slots a m inv := by
  have e : ((List.finRange m).map (Interchange.RepairSchedule.mainSlots a m)).map Fin.val = (List.range m).map (a+·) := by
    apply List.ext_getElem
    · simp
    · intro i h h'
      simp only [List.getElem_map,List.getElem_finRange,List.getElem_range]
      rfl
  cases inv with
  | false => exact e
  | true => exact (List.map_reverse).trans (congrArg List.reverse e)

@[simp] theorem order_length (a m : ℕ) (inv : Bool) : (order a m inv).length = m := by
  cases inv <;> simp [order]

def bools : Series Bool := Series.fixed [false,true] (by decide) (by decide)

def banks (l s : ℕ) := bools.cart (Series.natural (l*s))

theorem banks_count (l s : ℕ) : (banks l s).count = 2*(l*s) := by
  rw [banks,Series.count_cart,Series.count_natural]
  rfl

def compile (a m l s : ℕ) (inv : Bool) (child : ℕ → Cmd) : Cmd :=
  fields (2*(l*s)) child (slots a m inv)

theorem compile_within {R : ℕ} (hr : 3 ≤ R) (a m l s : ℕ) (inv : Bool) (child : ℕ → Cmd)
    (hc : ∀ j, Within R (child j)) : Within R (compile a m l s inv child) :=
  fields_within hr _ child hc _

theorem effective_compile {T : Type} [Primcodable T] {a m l s : T → ℕ} {inv : T → Bool}
    {child : T → ℕ → Cmd} (ha : Computable a) (hm : Computable m) (hl : Computable l) (hs : Computable s)
    (hi : Computable inv) (hc : Effective ltr (fun v : T × ℕ => child v.1 v.2)) :
    Effective ltr (fun t => compile (a t) (m t) (l t) (s t) (inv t) (child t)) := by
  apply effective_fields (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Primrec.nat_mul.to_comp.comp hl hs)) hc
  have hjs := computable_map (Primrec.list_range.to_comp.comp hm) (Primrec.nat_add.to_comp.comp (ha.comp Computable.fst) Computable.snd).to₂
  simpa only [slots,Bool.cond_eq_ite] using Computable.cond hi (Primrec.list_reverse.to_comp.comp hjs) hjs

private theorem fields_map {A B : Type} (n : ℕ) (c : B → Cmd) (f : A → B) (xs : List A) :
    fields n c (xs.map f) = fields n (c ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact congrArg (fun d => (bank n (c (f a))).join d) ih

variable {p l s a m b f : ℕ} {P G S : Dims.Tape} {D : Type}
local notation "X" => Positions P G S a m b f
local notation "R" => ZMod (p+1)
local notation "A" => Bool × Fin (l*s)

def lanes {T E : Type} (x y : Bank T (Fin l) E (Fin s)) (i : Bool × Fin (l*s)) (z : E) : T :=
  (if i.1 then y else x) i.2.divNat z i.2.modNat

def streams (x y : Bank R (Fin l) (X × D) (Fin s)) (i : A) (u : X) (d : D) : R :=
  lanes x y i (u,d)

def packed (rows : Series X) (pay : Series D) (x : Bank R (Fin l) (X × D) (Fin s)) :=
  Physical.LocalTable.Lift.bank rows (fun _ => pay) (fun u d => (u,d)) x

theorem tab_streams (rows : Series X) (pay : Series D) (x y : Bank R (Fin l) (X × D) (Fin s)) :
    (banks l s).tab (fun i => Sweep.row rows pay (streams x y i)) = packed rows pay x ++ packed rows pay y := by
  rw [banks,Series.grouped]
  simp only [bools,Series.tab,Series.fixed,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil]
  simp only [packed,Physical.LocalTable.Lift.bank,Physical.LocalTable.Lift.render,List.ofFn_eq_map]
  rfl

def update (inv : Bool) (half : R) (j : Fin (a+m+a)) (g : X → D → R) : X → D → R :=
  fun u d => advance inv half j (fun z => g z d) u

theorem slice (inv : Bool) (half : R) (js : List (Fin (a+m+a))) (x : X → D → R) (d : D) :
    (fun u => (js.foldl (fun g j => update inv half j g) x) u d) =
      js.foldl (fun g j => advance inv half j g) (fun u => x u d) := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih => exact ih (update inv half j x)

theorem native_eval [Fact (p+1).Prime] (inv : Bool) (half : R) (x y : Bank R (Fin l) (X × D) (Fin s)) :
    eval (fun j (_ : A) => update inv half j) (order a m inv) (streams x y) =
      streams (sweep (lift (directions inv half)) x) (sweep (lift (directions inv half)) y) := by
  funext i u d
  rw [eval_at]
  have e := congrFun (slice inv half (order a m inv) (streams x y i) d) u
  rw [e]
  rcases i with ⟨flag,i⟩
  cases flag <;> rfl

/-- Both check blocks use one pass per field and lane. The packet and its
spectator/payload order coincide with the ordinary five repair leaves. -/
theorem native_bounded [Fact (p+1).Prime] (rows : Series X) (pay : Series D) (h : Tree) (inv : Bool) (half : R)
    (child : ℕ → Cmd) (cost : Fin (a+m+a) → (X → D → R) → Allowance) (env : Env)
    (hc : ∀ j g, Run env (child j.val) (.fork h (Sweep.row rows pay g))
      (Sweep.row rows pay (update inv half j g)) (cost j g)) (x y : Bank R (Fin l) (X × D) (Fin s)) :
    Run env (compile a m l s inv child) (packet h (packed rows pay x ++ packed rows pay y))
      (packet h (packed rows pay (sweep (lift (directions inv half)) x) ++
        packed rows pay (sweep (lift (directions inv half)) y)))
      (fieldCost (banks l s) h (fun _ => Sweep.row rows pay) (fun j _ => update inv half j)
        (fun j _ => cost j) (order a m inv) (streams x y)) := by
  have e := fields_bounded (banks l s) h (fun _ => Sweep.row rows pay) (fun j _ => update inv half j)
    (child ∘ Fin.val) (fun j _ => cost j) env (fun j _ g => hc j g) (order a m inv) (streams x y)
  rw [← fields_map,slots_eq,banks_count,native_eval,tab_streams,tab_streams] at e
  exact e

theorem native_call_count (inv : Bool) (half : R) (x y : Bank R (Fin l) (X × D) (Fin s)) :
    (calls (banks l s) (fun j _ => update inv half j) (order a m inv) (streams x y)).length =
      2*l*s*m := by rw [calls_length,order_length,banks_count]; ac_rfl

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI
