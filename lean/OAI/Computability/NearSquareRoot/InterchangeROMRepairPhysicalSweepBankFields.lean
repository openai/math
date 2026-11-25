import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBank

/-! # Concatenating the field passes of a packed transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters InterchangeROM GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)

def fields {J : Type} (n : ℕ) (child : J → Cmd) (js : List J) : Cmd :=
  js.foldr (fun j c => (bank n (child j)).join c) .pass

theorem fields_within {J : Type} {R : ℕ} (hr : 3 ≤ R) (n : ℕ) (child : J → Cmd)
    (hc : ∀ j, Within R (child j)) (js : List J) : Within R (fields n child js) := by
  induction js with
  | nil => trivial
  | cons j js ih => exact ⟨bank_within hr (hc j) n,ih⟩

theorem effective_fields {X J : Type} [Primcodable X] [Primcodable J]
    {n : X → ℕ} {children : X → J → Cmd} {js : X → List J}
    (hn : Computable n) (hc : Effective ltr (fun v : X × J => children v.1 v.2))
    (hj : Computable js) : Effective ltr (fun x => fields (n x) (children x) (js x)) :=
  effective_foldr_join ltr (l:=js) (p:=fun x j => bank (n x) (children x j)) (z:=fun _ => .pass)
    hj (effective_bank (hn.comp Computable.fst) hc) (effective_const ltr .pass)

variable {J A : Type} {D : A → Type}

def eval (op : J → (a : A) → D a → D a) (js : List J) (x : (a : A) → D a) : (a : A) → D a :=
  js.foldl (fun y j a => op j a (y a)) x

theorem eval_at (op : J → (a : A) → D a → D a) (js : List J) (x : (a : A) → D a) (a : A) :
    eval op js x a = js.foldl (fun d j => op j a d) (x a) := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih => exact ih (fun b => op j b (x b))

def fieldCost (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree)
    (op : J → (a : A) → D a → D a) (cost : J → (a : A) → D a → Allowance) :
    List J → ((a : A) → D a) → Allowance
  | [], x => ⟨1,(packet h (s.tab fun a => enc a (x a))).count,0⟩
  | j::js, x =>
    let y a := op j a (x a)
    let u := packetCost h (s.tab fun a => enc a (x a)) (s.tab fun a => enc a (y a))
      (s.tab fun a => cost j a (x a))
    let v := fieldCost s h enc op cost js y
    ⟨u.time+v.time+2,max u.cap v.cap,max (u.depth+1) v.depth⟩

theorem fields_bounded (s : Series A) (h : Tree) (enc : (a : A) → D a → Tree)
    (op : J → (a : A) → D a → D a) (child : J → Cmd) (cost : J → (a : A) → D a → Allowance)
    (env : Env) (hc : ∀ j a d, Run env (child j) (.fork h (enc a d)) (enc a (op j a d)) (cost j a d))
    (js : List J) (x : (a : A) → D a) :
    Run env (fields s.count child js) (packet h (s.tab fun a => enc a (x a)))
      (packet h (s.tab fun a => enc a (eval op js x a))) (fieldCost s h enc op cost js x) := by
  induction js generalizing x with
  | nil => exact fun r base hr => BoundedFits.pass (hr.pile 0 _)
  | cons j js ih =>
    let y a := op j a (x a)
    let u := packetCost h (s.tab fun a => enc a (x a)) (s.tab fun a => enc a (y a))
      (s.tab fun a => cost j a (x a))
    let v := fieldCost s h enc op cost js y
    intro r base hr
    have head := bank_bounded s h (fun a => enc a (x a)) (fun a => enc a (y a)) (child j)
      (fun a => cost j a (x a)) env (fun a => hc j a (x a)) r base hr
    have tail := ih y r base hr
    exact (head.mono le_rfl (Nat.add_le_add_left (le_max_left u.cap v.cap) base) le_rfl).join
      (tail.mono le_rfl (Nat.add_le_add_left (le_max_right u.cap v.cap) base)
        (le_max_right (u.depth+1) v.depth)) (le_max_left ..)

/-- Chronological arguments of the individual row programs in every pass. -/
def calls (s : Series A) (op : J → (a : A) → D a → D a) :
    List J → ((a : A) → D a) → List (J × (a : A) × D a)
  | [], _ => []
  | j::js, x => s.tab (fun a => (j,⟨a,x a⟩)) ++ calls s op js (fun a => op j a (x a))

theorem calls_length (s : Series A) (op : J → (a : A) → D a → D a)
    (js : List J) (x : (a : A) → D a) : (calls s op js x).length = js.length*s.count := by
  induction js generalizing x with
  | nil => simp [calls]
  | cons j js ih => simp [calls,ih,Nat.succ_mul,Nat.add_comm]

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI
