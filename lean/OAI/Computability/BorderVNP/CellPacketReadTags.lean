import OAI.Computability.BorderVNP.CellPacketReadMany
import Mathlib.Tactic.FinCases

/-! # Literal binary constructor-tag dispatch for the sparse packet reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram

private theorem headF (p q : Program Register) {src out : List Bool} {ct : Fin 3 → List Bool}
    {s : Store Register} {c : ℕ} (r : Runs p (bank src out ct) s c) :
    Runs (.cases .input .skip p q) (bank (false :: src) out ct) s (c+1) := by
  apply Runs.cases_false (k := Register.input) (s := bank (false::src) out ct) (xs := src) rfl
  have he : Function.update (bank (false::src) out ct) .input src = bank src out ct := by
    funext k; cases k <;> rfl
  exact he.symm ▸ r

private theorem headT (p q : Program Register) {src out : List Bool} {ct : Fin 3 → List Bool}
    {s : Store Register} {c : ℕ} (r : Runs q (bank src out ct) s c) :
    Runs (.cases .input .skip p q) (bank (true :: src) out ct) s (c+1) := by
  apply Runs.cases_true (k := Register.input) (s := bank (true::src) out ct) (xs := src) rfl
  have he : Function.update (bank (true::src) out ct) .input src = bank src out ct := by
    funext k; cases k <;> rfl
  exact he.symm ▸ r

/-- Literal trie for the marker, little-endian bits, and terminating marker of tags zero to three. -/
def tagDispatch (p : Fin 4 → Program Register) : Program Register :=
  let node (f t : Program Register) := Program.cases Register.input .skip f t
  let tt (r : Program Register) := node .skip (node .skip r)
  node .skip (node (node (node (tt (p 2)) .skip) (node (tt (p 3)) (p 1))) (p 0))

/-- Every tag consumes its entire serialized numeral and executes exactly its selected branch. -/
theorem tagDispatch_run (p : Fin 4 → Program Register) (i : Fin 4) (src out : List Bool)
    (ct : Fin 3 → List Bool) (s : Store Register) (c : ℕ) (r : Runs (p i) (bank src out ct) s c) :
    Runs (tagDispatch p) (bank (wire [i.val] ++ src) out ct) s (c+(wire [i.val]).length) := by
  fin_cases i
  · exact headT _ _ (headT _ _ r)
  · exact headT _ _ (headF _ _ (headT _ _ (headT _ _ r)))
  · exact headT _ _ (headF _ _ (headF _ _ (headF _ _ (headT _ _ (headT _ _ r)))))
  · exact headT _ _ (headF _ _ (headT _ _ (headF _ _ (headT _ _ (headT _ _ r)))))

private theorem tag_cost (k : Fin 4) (n C c : ℕ) (hc : c ≤ C*(n+1)^2) :
    c+(wire [k.val]).length ≤ (C+1)*((wire [k.val]).length+n+1)^2 := by
  let t := (wire [k.val]).length
  have h₁ := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (show n+1 ≤ t+n+1 by omega) 2)
  have h₂ : t ≤ (t+n+1)^2 := by nlinarith only [Nat.zero_le ((t+n)^2),Nat.zero_le t,Nat.zero_le n]
  change c+t ≤ (C+1)*(t+n+1)^2
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Weaken a typed reader's clean-counter precondition for composition with other constructors. -/
def typedReserve {α : Type} {raw : α → List ℕ} {enc : α → List Bool} {K L : Finset (Fin 3)}
    (p : TypedReader raw enc K) (hk : K ⊆ L) : TypedReader raw enc L :=
  fun emit => (p emit).reserve hk

/-- Tagged sum of four literal packet payloads in the public constructor order. -/
def tagFields {α β γ δ : Type} (f : α → List ℕ) (g : β → List ℕ) (h : γ → List ℕ)
    (j : δ → List ℕ) : α ⊕ β ⊕ γ ⊕ δ → List ℕ :=
  Sum.elim (fun a => 0 :: f a) (Sum.elim (fun b => 1 :: g b) (Sum.elim (fun c => 2 :: h c) (fun d => 3 :: j d)))

private def withPrefix {α : Type} {raw : α → List ℕ} {enc : α → List Bool} {K : Finset (Fin 3)}
    (p : TypedReader raw enc K) (bs : List Bool) (emit : Emit) :
    Reader (fun x => wire (raw x)) (fun x => (bs ++ enc x).flatMap emit) K := by
  let lit : Reader (fun _ : α => []) (fun _ => bs.flatMap emit) K :=
    (Reader.literal _).reserve (Finset.empty_subset K)
  let r := lit.followed (p emit)
  exact ((Finset.union_self K) ▸ r).castCode (fun _ => rfl) (fun _ => List.flatMap_append.symm)

/-- A fixed bit-stack switch decodes all four constructor tags and emits their exact nested
sum prefixes under the caller's quote depth. -/
def typedTagged4 {α β γ δ : Type} {K : Finset (Fin 3)}
    {fa : α → List ℕ} {fb : β → List ℕ} {fc : γ → List ℕ} {fd : δ → List ℕ}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
    (pa : TypedReader fa ea K) (pb : TypedReader fb eb K) (pc : TypedReader fc ec K) (pd : TypedReader fd ed K) :
    TypedReader (tagFields fa fb fc fd) (sumCode ea (sumCode eb (sumCode ec ed))) K := by
  intro emit
  let a := withPrefix pa [false] emit
  let b := withPrefix pb [true,false] emit
  let c := withPrefix pc [true,true,false] emit
  let d := withPrefix pd [true,true,true] emit
  let progs : Fin 4 → Program Register := ![a.program,b.program,c.program,d.program]
  let C := a.scale + b.scale + c.scale + d.scale
  refine ⟨tagDispatch progs,C+1,?_⟩
  intro x rest out ct hk
  have call {σ : Type} {raw : σ → List ℕ} {enc : σ → List Bool}
      (i : Fin 4) (p : Reader (fun x => wire (raw x)) enc K) (x : σ)
      (he : progs i = p.program) (hs : p.scale ≤ C) :
      ∃ u ≤ (C+1)*((wire (i.val::raw x)).length+1)^2,
        Runs (tagDispatch progs) (bank (wire (i.val::raw x) ++ rest) out ct)
          (bank rest ((enc x).reverse ++ out) ct) u := by
    obtain ⟨t,ht,hr⟩ := p.runs x rest out ct hk
    have hW : wire (i.val::raw x) = wire [i.val] ++ wire (raw x) := wire_append [i.val] _
    have hrun := tagDispatch_run progs i (wire (raw x) ++ rest) out ct _ t (he.symm ▸ hr)
    refine ⟨t+(wire [i.val]).length,?_,?_⟩
    · rw [hW,List.length_append]
      exact tag_cost i _ _ _ (ht.trans (Nat.mul_le_mul_right _ hs))
    · simpa only [hW,List.append_assoc] using hrun
  rcases x with x | (x | (x | x))
  · exact call 0 a x rfl (by dsimp only [C]; omega)
  · exact call 1 b x rfl (by dsimp only [C]; omega)
  · exact call 2 c x rfl (by dsimp only [C]; omega)
  · exact call 3 d x rfl (by dsimp only [C]; omega)

/-- Boolean table rows consume a literal zero or one numeral, and emit the actual Boolean bit. -/
def typedBoolean : TypedReader (fun b : Bool => [b.toNat]) Procedure.boolCode ∅ := by
  intro emit
  let f : Reader (fun _ : Unit => []) (fun _ => emit false) ∅ := Reader.literal _
  let t : Reader (fun _ : Unit => []) (fun _ => emit true) ∅ := Reader.literal _
  let ps : Fin 4 → Program Register := ![f.program,t.program,.skip,.skip]
  refine ⟨tagDispatch ps,f.scale+t.scale+7,?_⟩
  intro b rest out ct _
  cases b with
  | false =>
    obtain ⟨c,h,r⟩ := f.runs () rest out ct (by simp)
    have run := tagDispatch_run ps 0 rest out ct _ c r
    refine ⟨c+2,?_,?_⟩
    · change c ≤ f.scale*(0+1)^2 at h
      change c+2 ≤ (f.scale+t.scale+7)*(2+1)^2
      omega
    · simpa [Procedure.boolCode] using run
  | true =>
    obtain ⟨c,h,r⟩ := t.runs () rest out ct (by simp)
    have run := tagDispatch_run ps 1 rest out ct _ c r
    refine ⟨c+4,?_,?_⟩
    · change c ≤ t.scale*(0+1)^2 at h
      change c+4 ≤ (f.scale+t.scale+7)*(4+1)^2
      omega
    · simpa [Procedure.boolCode] using run

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
