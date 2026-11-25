import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingSerializeRowsTable
import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingSerializeRowsHeader

/-! # Computable physical transition rows for the staged operand serializer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.SerializeRows

open CommonAlphabet IntegerMultiplication StagingSerialize
open ChunkControl (Driver)
open StagingProtection (Cell)

/-- Identify the finite instruction case, including the header letter selected
by the current header counter. -/
def mode (k q : ℕ) : ℕ :=
  if q < 9 then q else if q < 9+2^k then 9 else 10+headerLetter k (q-(9+2^k))

private theorem headerMode_val (l : Code.Ltr) : (headerMode l).val = 10+codeLetter l := by
  rcases l with (_|_)|_|_ <;> rfl

private theorem mode_rank (k : ℕ) (s : Phase k) : mode k (rank s) = (phaseMode s).val := by
  cases s with
  | turn | back | scan | returnIn | returnOut | ready | rejected => rfl
  | payload b => cases b <;> rfl
  | check j =>
    have bound := j.isLt
    simp [mode,phaseMode,show 9+j.val < 9+2^k by omega]
  | header j =>
    simp [mode,phaseMode,headerMode_val,headerLetter_get,
      show ¬9+2^k+j.val < 9 from not_lt_of_ge ((Nat.le_add_right 9 (2^k)).trans (Nat.le_add_right _ j.val)),
      show ¬9+2^k+j.val < 9+2^k from not_lt_of_ge (Nat.le_add_right _ _)]

private theorem compIf {X Y : Type} [Primcodable X] [Primcodable Y] {p : X → Prop}
    [DecidablePred p] {f g : X → Y} (hp : Computable fun x => decide (p x)) (hf : Computable f)
    (hg : Computable g) : Computable fun x => if p x then f x else g x :=
  (Computable.cond hp hf hg).of_eq fun _ => by simp

private theorem power : Computable fun k : ℕ => 2^k :=
  (KernelComputableAddress.primrec_pow (Primrec.const 2) Primrec.id).to_comp

private theorem compMode {X : Type} [Primcodable X] {k q : X → ℕ}
    (hk : Computable k) (hq : Computable q) : Computable fun x => mode (k x) (q x) := by
  have off := Primrec.nat_add.to_comp.comp (Computable.const 9) (power.comp hk)
  exact compIf (Primrec.nat_lt.decide.to_comp.comp hq (Computable.const 9)) hq
    (compIf (Primrec.nat_lt.decide.to_comp.comp hq off) (Computable.const 9)
      (Primrec.nat_add.to_comp.comp (Computable.const 10)
        (computable_headerLetter.comp hk (Primrec.nat_sub.to_comp.comp hq off))))

private theorem compDestination {X : Type} [Primcodable X] {k q t : X → ℕ}
    (hk : Computable k) (hq : Computable q) (ht : Computable t) :
    Computable fun x => destination (k x) (q x) (t x) := by
  have threshold := power.comp hk
  have off := Primrec.nat_add.to_comp.comp (Computable.const 9) threshold
  have len := Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) hk) (Computable.const 3)
  have jc := Computable.succ.comp (Primrec.nat_sub.to_comp.comp hq (Computable.const 9))
  have jh := Computable.succ.comp (Primrec.nat_sub.to_comp.comp hq off)
  exact compIf (Primrec.eq.decide.to_comp.comp ht (Computable.const 9))
    (compIf (Primrec.nat_lt.decide.to_comp.comp jc threshold)
      (Primrec.nat_add.to_comp.comp (Computable.const 9) jc) (Computable.const 0))
    (compIf (Primrec.eq.decide.to_comp.comp ht (Computable.const 10)) off
      (compIf (Primrec.eq.decide.to_comp.comp ht (Computable.const 11))
        (compIf (Primrec.nat_lt.decide.to_comp.comp jh len)
          (Primrec.nat_add.to_comp.comp off jh) (Computable.const 2)) ht))

variable (d : Driver) (a : CommonAlphabet.Numbering (Cell d))

private def field (get : ℕ × ℕ → ℕ) :=
  Routing.lookup₂ (Numbering.fin 14) (Numbering.bool.arrow a)
    (fun m h => get (instruction d a m h))

private theorem field_eq (get : ℕ × ℕ → ℕ) (m : Fin 14) (h : Bool → Cell d) :
    field d a get m.val ((Numbering.bool.arrow a).equiv h).val = get (instruction d a m h) :=
  Routing.lookup₂_rank _ _ _ m h

private theorem field_eff (get : ℕ × ℕ → ℕ) : Computable₂ (field d a get) :=
  (Routing.primrec_lookup₂ _ _ _).to_comp

def eval (k : ℕ) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let m := mode k p.1
  resolve k p.1 (field d a Prod.fst m p.2, field d a Prod.snd m p.2)

private theorem computable_eval : Computable₂ (eval d a) := by
  let X := ℕ × (ℕ × ℕ)
  have hk : Computable fun x : X => x.1 := Computable.fst
  have hq : Computable fun x : X => x.2.1 := Computable.fst.comp Computable.snd
  have hr : Computable fun x : X => x.2.2 := Computable.snd.comp Computable.snd
  have hm := compMode hk hq
  have token := (field_eff d a Prod.fst).comp hm hr
  have action := (field_eff d a Prod.snd).comp hm hr
  exact (compIf (Primrec.eq.decide.to_comp.comp token (Computable.const 12)) (Computable.const none)
    (Computable.option_some.comp ((compDestination hk hq token).pair action))).to₂

/-- Every numerical row agrees with both physical writes and head moves,
including halt at the accepting and rejecting controls. -/
theorem rows : EffectiveRows a Numbering.bool states (StagingSerialize.rule d) := by
  refine ⟨eval d a,computable_eval d a,fun k s h => ?_⟩
  change resolve k (rank s) (field d a Prod.fst (mode k (rank s)) _,field d a Prod.snd (mode k (rank s)) _) = _
  rw [mode_rank,field_eq,field_eq]
  exact resolves d a k s h

/-- The encoded split exponent may itself be any computable function of the
candidate index. -/
theorem rows_family (split : ℕ → ℕ) (hs : Computable split) :
    EffectiveRows a Numbering.bool (fun j => states (split j)) (fun j => StagingSerialize.rule d (split j)) := by
  obtain ⟨r,hr,h⟩ := rows d a
  exact ⟨fun j => r (split j), (hr.comp (hs.comp Computable.fst) Computable.snd).to₂,fun j => h (split j)⟩

end Generator.SerializeRows

end NearSquareRoot
end Computability
end OAI
