import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering
import OAI.Computability.NearSquareRoot.CommonAlphabetPublic
import OAI.Computability.NearSquareRoot.ScheduleGeneratorExpandFormula
import OAI.Computability.NearSquareRoot.ScheduleGeneratorOneHot

/-! # Correctness of the computed input-expansion rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.ExpandRows

open CommonAlphabet IntegerMultiplication
open Numbering (publicLetter bool ternary move)
variable {A : Type}

private theorem opt_none {G : Type} (g : Numbering G) : (g.option.equiv none).val = 0 := by
  change ((finSuccEquiv g.size).symm none).val = 0
  simp

private theorem opt_some {G : Type} (g : Numbering G) (x : G) :
    (g.option.equiv (some x)).val = (g.equiv x).val+1 := by
  change ((finSuccEquiv g.size).symm (some (g.equiv x))).val = _
  simp

private abbrev body (a : Numbering A) (w : ℕ) := (a.prod (.fin w)).sum (.fin w)

@[simp] theorem scan_rank (a : Numbering A) (w : ℕ) : ((a.expand w).equiv .scan).val = 0 :=
  opt_none _

@[simp] theorem back_rank (a : Numbering A) (w : ℕ) : ((a.expand w).equiv .back).val = 1 := by
  change ((body a w).option.option.option.equiv (some none)).val = _
  rw [opt_some,opt_none]

@[simp] theorem done_rank (a : Numbering A) (w : ℕ) : ((a.expand w).equiv .done).val = 2 := by
  change ((body a w).option.option.option.equiv (some (some none))).val = _
  rw [opt_some,opt_some,opt_none]

@[simp] theorem emit_rank (a : Numbering A) (w : ℕ) (x : A) (k : Fin w) :
    ((a.expand w).equiv (.emit x k)).val = k.val+w*(a.equiv x).val+3 := by
  change ((body a w).option.option.option.equiv (some (some (some (.inl (x,k)))))).val = _
  rw [opt_some,opt_some,opt_some]
  rfl

@[simp] theorem skip_rank (a : Numbering A) (w : ℕ) (k : Fin w) :
    ((a.expand w).equiv (.skip k)).val = a.size*w+k.val+3 := by
  change ((body a w).option.option.option.equiv (some (some (some (.inr k))))).val = _
  rw [opt_some,opt_some,opt_some]
  rfl

theorem size_eq (a : Numbering A) (w : ℕ) : (a.expand w).size = a.size*w+w+3 := rfl

private theorem srcRanks : (publicLetter.equiv none).val = 0 ∧
    (publicLetter.equiv (some none)).val = 1 ∧
    (publicLetter.equiv (some (some false))).val = 2 ∧
    (publicLetter.equiv (some (some true))).val = 3 := ⟨rfl,rfl,rfl,rfl⟩

private theorem pair_commands (s d : Public.Letter) (a b : TM.Move) :
    ((bool.arrow (publicLetter.prod move)).equiv (Expand.pair (s,a) (d,b))).val =
    commands (publicLetter.equiv s).val (publicLetter.equiv d).val (move.equiv a).val (move.equiv b).val := by
  rw [← Numbering.encodeBase_arrow, show bool.all = [false,true] from rfl]
  change Numbering.encodeBase 12 [((move.equiv a).val+3*(publicLetter.equiv s).val),
    ((move.equiv b).val+3*(publicLetter.equiv d).val)] = _
  simp [Numbering.encodeBase, Nat.ofDigits, commands]

private theorem emb_rank (d : Option Bool) :
    (publicLetter.equiv (Public.emb d)).val = embedDigit (ternary.equiv d).val := by
  rcases d with _ | (_ | _) <;> rfl

private theorem row_read (size w b₀ b₁ sep : ℕ) (enc : ℕ × ℕ → ℕ)
    (q : ℕ) (r : Bool → Public.Letter) :
    row size w b₀ b₁ sep enc (q,((bool.arrow publicLetter).equiv r).val) =
      rowCore size w b₀ b₁ sep enc q (publicLetter.equiv (r false)).val (publicLetter.equiv (r true)).val := by
  exact congrArg₂ (rowCore size w b₀ b₁ sep enc q) (Numbering.digit_arrow bool publicLetter r false)
    (Numbering.digit_arrow bool publicLetter r true)

/-- Every computed instruction gives the transition of the physical two-tape expander.
The numerical encoder is required to agree on the source letters and block positions. -/
theorem row_eq (a : Numbering A) (c : Code A) (varBit : Bool → A) (varSep : A)
    (enc : ℕ × ℕ → ℕ) (hc : ∀ (x : A) (k : Fin c.width),
      enc ((a.equiv x).val,k.val) = (ternary.equiv (c.enc x k)).val)
    (q : Expand.Phase A c.width) (r : Bool → Public.Letter) :
    row a.size c.width (a.equiv (varBit false)).val (a.equiv (varBit true)).val (a.equiv varSep).val enc
      (((a.expand c.width).equiv q).val, ((bool.arrow publicLetter).equiv r).val) =
    (Expand.rule c (Public.parse varBit varSep) Public.emb q r).map (fun z =>
      (((a.expand c.width).equiv z.1).val, ((bool.arrow (publicLetter.prod move)).equiv z.2).val)) := by
  rw [row_read]
  have hnon : 0 < c.width := c.pos
  cases q with
  | scan =>
    rw [scan_rank a c.width]
    rcases h : r false with _ | ( _ | (_ | _)) <;>
      simp [rowCore, Expand.rule, h, Public.parse, pair_commands, first, srcRanks] <;> rfl
  | back =>
    rw [back_rank a c.width]
    rcases h : r false with _ | ( _ | (_ | _)) <;>
      simp [rowCore, Expand.rule, h, Public.parse, pair_commands, first,srcRanks] <;> rfl
  | done => rw [done_rank a c.width]; rfl
  | skip k =>
    have above : ¬ a.size*c.width+k.val < a.size*c.width := by omega
    simp only [skip_rank,rowCore,Nat.add_sub_cancel_right,Nat.add_sub_cancel_left,above,↓reduceIte]
    simp [Expand.rule,atIndex,pair_commands]
    split <;>
      simp [add_assoc] <;> rfl
  | emit x k =>
    let z := (a.equiv x).val
    have hz := (a.equiv x).isLt
    have below : k.val+c.width*z < a.size*c.width := by
      calc
        _ < c.width+c.width*z := Nat.add_lt_add_right k.isLt _
        _ = (z+1)*c.width := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ hz
    have hd : (k.val+c.width*z)/c.width = z := by
      rw [Nat.add_mul_div_left _ _ hnon,Nat.div_eq_of_lt k.isLt,Nat.zero_add]
    have hm : (k.val+c.width*z)%c.width = k.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]
    simp only [emit_rank,rowCore,Nat.add_sub_cancel_right]
    simp [z] at below hd hm
    simp [below,hd,hm,hc,Expand.rule,atIndex,pair_commands,emb_rank]
    split <;>
      simp [add_assoc] <;> first | rfl | exact ⟨by omega,rfl⟩

/-- One-hot block expansion has uniformly computable rows whenever the source alphabet
cardinality and the four distinguished source-letter ranks are computable. -/
theorem oneHot_family {T : ℕ → Type} (a : ∀ j, Numbering (T j))
    (bit : ∀ j, Bool → T j) (sep blank : ∀ j, T j)
    (ha : Computable fun j => (a j).size)
    (hb₀ : Computable fun j => ((a j).equiv (bit j false)).val)
    (hb₁ : Computable fun j => ((a j).equiv (bit j true)).val)
    (hs : Computable fun j => ((a j).equiv (sep j)).val)
    (hblank : Computable fun j => ((a j).equiv (blank j)).val) :
    let codec j := oneHot (a j).equiv (blank j)
    let states j := (a j).expand (codec j).width
    ∃ rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ), Computable (fun j => (states j).size) ∧
      Computable₂ rows ∧ ∀ j q r,
      rows j (((states j).equiv q).val,((bool.arrow publicLetter).equiv r).val) =
        (Expand.rule (codec j) (Public.parse (bit j) (sep j)) Public.emb q r).map (fun z =>
          (((states j).equiv z.1).val,((bool.arrow (publicLetter.prod move)).equiv z.2).val)) := by
  let enc (j : ℕ) (p : ℕ × ℕ) := OneHot.encode p.1 ((a j).equiv (blank j)).val p.2
  have he : Computable₂ enc := OneHot.computable_encode (Computable.fst.comp Computable.snd)
    (hblank.comp Computable.fst) (Computable.snd.comp Computable.snd)
  have size : Computable fun j => ((a j).expand (a j).size).size := by
    simp only [size_eq]
    exact Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp ha ha) ha) (Computable.const 3)
  refine ⟨_, size, computable_row ha ha hb₀ hb₁ hs he, ?_⟩
  intro j
  exact row_eq (a j) (oneHot (a j).equiv (blank j)) (bit j) (sep j) (enc j)
    (OneHot.encode_oneHot (a j).equiv (blank j))

end Generator.ExpandRows

end NearSquareRoot
end Computability
end OAI
