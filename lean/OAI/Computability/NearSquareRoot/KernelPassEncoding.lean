import OAI.Computability.NearSquareRoot.KernelPass
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Nat.Pairing

/-! # Effective descriptions of normalized binary templates

Tables are encoded as finite vectors in a fixed binary order. The parser
takes an explicit recursion depth and rejects ill-typed serial and parallel
compositions. The round-trip lemma supplies a natural-number description
of each well-typed template. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

namespace Plan

private def columnIndex (A : ℕ) : Column A ≃ Fin (4^A) :=
  (Equiv.piCongrRight fun _ : Fin A => (finFunctionFinEquiv :
    (Fin 2 → Fin 2) ≃ Fin (2^2))).trans finFunctionFinEquiv

private def testsAt {A q : ℕ} (tests : Column A → Fin q → ZMod 2) :
    Fin (4^A) → Fin q → Fin 2 := fun i => tests ((columnIndex A).symm i)

private def tableAt {q : ℕ} (table : (Fin q → ZMod 2) → Coefficient) :
    Fin (2^q) → Coefficient := fun j => table (finFunctionFinEquiv.symm j)

private def castPlan {A i o j u : ℕ} (p : Plan A i o) : Option (Plan A j u) :=
  if hi : i = j then
    if ho : o = u then some (hi ▸ ho ▸ p) else none
  else none

@[simp] private theorem castPlan_self {A i o : ℕ} (p : Plan A i o) :
    castPlan (j:=i) (u:=o) p = some p := by simp [castPlan]

/-- Encode every instruction, including its complete finite truth tables. -/
def code {A i o : ℕ} : Plan A i o → ℕ
  | .mix c => Nat.pair 0 (Encodable.encode c)
  | .xor g => Nat.pair 1 (Encodable.encode g)
  | .scale q tests table => Nat.pair 2 (Nat.pair q
      (Encodable.encode (testsAt tests, tableAt table)))
  | .child a => Nat.pair 3 (Encodable.encode a)
  | @seq _ _ j _ p q => Nat.pair 4 (Encodable.encode (j,code p,code q))
  | @parallel _ i j o u p q => Nat.pair 5 (Encodable.encode (i,j,o,u,code p,code q))

/-- One more unit of parser fuel is needed per constructor on a path. -/
def depth {A i o : ℕ} : Plan A i o → ℕ
  | .seq p q | .parallel p q => max (depth p) (depth q) + 1
  | _ => 1

private def decodeScale (A q s : ℕ) : Option (Plan A 1 1) := do
  let (tests,table) ← Encodable.decode
    (α := (Fin (4^A) → Fin q → Fin 2) × (Fin (2^q) → Coefficient)) s
  return .scale q (tests ∘ columnIndex A) (table ∘ finFunctionFinEquiv)

private theorem decodeScale_code {A q : ℕ} (tests : Column A → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → Coefficient) :
    decodeScale A q (Encodable.encode (testsAt tests, tableAt table)) =
      some (.scale q tests table) := by
  simp [decodeScale]
  constructor
  · funext x
    exact congrArg tests ((columnIndex A).symm_apply_apply x)
  · funext x
    exact congrArg table (finFunctionFinEquiv.symm_apply_apply x)

/-- Parse a program of known row dimensions. -/
def decode (A : ℕ) : (fuel i o n : ℕ) → Option (Plan A i o)
  | 0, _, _, _ => none
  | fuel+1, i, o, n =>
      match Nat.unpair n with
      | (0,k) => Plan.mix <$> Encodable.decode k
      | (1,k) => do
          let g ← Encodable.decode (α := Fin A × Fin A) k
          castPlan (.xor g)
      | (2,k) => (decodeScale A (Nat.unpair k).1 (Nat.unpair k).2).bind castPlan
      | (3,k) => do
          let a ← Encodable.decode (α := Fin A) k
          castPlan (.child a)
      | (4,k) => do
          let (j,l,r) ← Encodable.decode (α := ℕ × ℕ × ℕ) k
          let p ← decode A fuel j o l
          let q ← decode A fuel i j r
          return p.seq q
      | (5,k) => do
          let (l,r,s,t,c,d) ← Encodable.decode (α := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) k
          let p ← decode A fuel l s c
          let q ← decode A fuel r t d
          castPlan (p.parallel q)
      | (_,_) => none

theorem decode_code {A i o : ℕ} (p : Plan A i o) (fuel : ℕ) (h : p.depth ≤ fuel) :
    decode A fuel i o p.code = some p := by
  induction p generalizing fuel with
  | mix c => cases fuel <;> simp_all [depth, decode, code]
  | xor g => cases fuel <;> simp_all [depth, decode, code]
  | child a => cases fuel <;> simp_all [depth, decode, code]
  | scale q tests table =>
    cases fuel <;> simp_all [depth, decode, code]
    exact decodeScale_code tests table
  | seq p q ihp ihq =>
    cases fuel with
    | zero => simp [depth] at h
    | succ fuel =>
      simp [depth] at h
      simp [code, decode, ihp _ h.1, ihq _ h.2]
  | parallel p q ihp ihq =>
    cases fuel with
    | zero => simp [depth] at h
    | succ fuel =>
      simp [depth] at h
      simp [code, decode, ihp _ h.1, ihq _ h.2]

end Plan
end KernelPass

end NearSquareRoot
end Computability
end OAI
