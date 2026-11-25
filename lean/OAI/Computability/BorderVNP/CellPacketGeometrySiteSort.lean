import OAI.Computability.BorderVNP.CellPacketGeometryLiveRun

/-! # One additional stable sort of public record fields by final owning site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteSort

open PackedHistogram ParseBatchLookup ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {N M R p q k w start : ℕ} {E : Type*} [Fintype E]

/-- Actual public pins and the final site ID of each original scalar in the
record-word block. The two cell-header and factor sections do not use these IDs. -/
abbrev Input (N M R q k w : ℕ) (E : Type*) := Schema.Pins N M k w E ⊕ (Fin R × Fin q)

/-- Word column of the unsorted public record section. -/
def pos (room : start+R ≤ N) (i : Fin R) : Fin N := ⟨start+i.val,by omega⟩

private def combined (room : start+R ≤ N) (i : Fin R) : Fin (w+k) → Input N M R q k w E :=
  prepend (fun j => .inl (.inl (pos room i,.inl j))) (fun j => .inl (.inl (pos room i,.inr j)))

private noncomputable def load (room : start+R ≤ N) (pad : Fin (2^q)) :
    Stable.Input p q (w+k) → Expr (Input N M R q k w E)
  | (i,j) => if h : i.val < R then
      .input (j.elim (fun a => .inr (⟨i.val,h⟩,a)) (combined room ⟨i.val,h⟩))
    else j.elim (fun a => .const ((numberWords q).symm pad a)) (fun _ => .const false)

private noncomputable def packed (room : start+R ≤ N) (pad : Fin (2^q)) :
    Frame (Input N M R q k w E) (Stable.Input p q (w+k)) :=
  (Frame.initial id).step (load room pad)

private def output (fit : R ≤ 2^p) :
    Schema.Pins N M k w E → (Input N M R q k w E) ⊕ (Bank p × Fin (w+k))
  | .inl (i,j) => if h : start ≤ i.val ∧ i.val-start < R then
      .inr (.inl ⟨i.val-start,by omega⟩,j.elim (highPin w) (lowPin k))
    else .inl (.inl (.inl (i,j)))
  | .inr z => .inl (.inl (.inr z))

/-- The extra Batcher pass operates only on actual scalar row fields. It
retains all other pins by wires, including the private pointers and report bank. -/
noncomputable def frame (room : start+R ≤ N) (fit : R ≤ 2^p) (pad : Fin (2^q)) :
    Frame (Input N M R q k w E) (Schema.Pins N M k w E) :=
  let sort := (sortedFrame p q (w+k)).subst (packed room pad)
  sort.withInput.select (output (start := start) fit)

/-- Exact finite gate cost of the extra sort up to the packed scalar input pins. -/
theorem frame_size (room : start+R ≤ N) (fit : R ≤ 2^p) (pad : Fin (2^q)) :
    (frame (M := M) (k := k) (w := w) (E := E) room fit pad).size ≤
      2^p*(q+(w+k))+(sortedFrame p q (w+k)).size := by
  have each (v : Stable.Input p q (w+k)) : (load (M := M) (E := E) room pad v).size ≤ 1 := by
    rcases v with ⟨i,j⟩
    by_cases h : i.val<R
    · simp [load,h,StatementCircuit.Expr.size]
    · cases j <;> simp [load,h,StatementCircuit.Expr.size]
  have h := Frame.step_size_le (Frame.initial (id : Input N M R q k w E → _)) (load room pad) 1 each
  simpa only [frame,Frame.select_size,Frame.withInput_size,Frame.subst_size,packed,Frame.initial_size,
    Stable.Input,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,mul_one,zero_add] using
    Nat.add_le_add_right h (sortedFrame p q (w+k)).size

/-- Unsorted key of a true field or of padding after all real site ordinals. -/
def key (sites : ℕ) (atSite : Fin R → ℕ) (i : Fin (2^p)) :=
  if h : i.val < R then atSite ⟨i.val,h⟩ else sites

private theorem packed_key (room : start+R ≤ N) (pad : Fin (2^q)) (x : Input N M R q k w E → Bool)
    (i : Fin (2^p)) : Stable.key ((packed room pad).eval x) i =
      key pad.val (fun a => value fun j => x (.inr (a,j))) i := by
  by_cases h : i.val<R
  · simp [Stable.key,packed,Frame.step_eval,load,h,key,StatementCircuit.Expr.eval]
  · simp [Stable.key,packed,Frame.step_eval,load,h,key,StatementCircuit.Expr.eval,value_encode]

private theorem packed_payload (room : start+R ≤ N) (pad : Fin (2^q)) (x : Input N M R q k w E → Bool)
    (i : Fin (2^p)) (hi : i.val < R) (j : Fin (w+k)) :
    (packed room pad).eval x (i,.inr j) =
      prepend (fun b => x (.inl (.inl (pos room ⟨i.val,hi⟩,.inl b))))
        (fun b => x (.inl (.inl (pos room ⟨i.val,hi⟩,.inr b)))) j := by
  simp only [packed,Frame.step_eval,load,hi,dite_eq_left,Sum.elim_inr,StatementCircuit.Expr.eval,Frame.initial_eval,id_eq,combined]
  exact congrFun (prepend_map x _ _) j

/-- A single actual sorting permutation controls both the final-cell label and
the numerical word of every real record. Other source and descriptor pins retain
their original values. -/
theorem frame_values (room : start+R ≤ N) (fit : R ≤ 2^p) (pad : Fin (2^q))
    (x : Input N M R q k w E → Bool) (width : 2^p ≤ 2^(w+k)) :
    let out := (frame room fit pad).eval x
    let sites := fun i : Fin R => value fun j => x (.inr (i,j))
    ∃ π : Equiv.Perm (Fin (2^p)),
      Monotone (fun i => 2*key pad.val sites (π i)*2^p+(π i).val) ∧
      (∀ i : Fin R, ∀ h : (π (i.castLE fit)).val < R, ∀ j : Fin k ⊕ Fin w,
        out (.inl (pos room i,j)) = x (.inl (.inl (pos room ⟨(π (i.castLE fit)).val,h⟩,j)))) ∧
      (∀ i : Fin N, (i.val < start ∨ start + R ≤ i.val) → ∀ j : Fin k ⊕ Fin w,
        out (.inl (i,j)) = x (.inl (.inl (i,j)))) ∧
      ∀ z, out (.inr z) = x (.inl (.inr z)) := by
  intro out sites
  let y := (packed (p := p) room pad).eval x
  obtain ⟨π,hπ,word,_⟩ := sortedFrame_values y width
  have keys (i : Fin (2^p)) : Stable.key y i = key pad.val sites i := packed_key room pad x i
  refine ⟨π,?_,?_,?_,?_⟩
  · simpa only [keys] using hπ
  · intro i hi j
    let target := i.castLE fit
    have bits := congrFun (value_injective (w+k) (word target))
    have range : start ≤ (pos room i).val ∧ (pos room i).val-start<R := by simp [pos]
    have back : (⟨(pos room i).val-start,by omega⟩ : Fin (2^p)) = target := Fin.ext (by simp [pos,target])
    have op : output (q := q) (M := M) (E := E) (start := start) fit (.inl (pos room i,j)) =
        .inr (.inl target,j.elim (highPin w) (lowPin k)) := by simp [output,range,back]
    simp only [out,frame,Frame.select_eval,op,Frame.withInput_eval_inr,Frame.subst_eval]
    change (sortedFrame p q (w+k)).eval y (.inl target,_) = _
    rw [bits]
    dsimp only [y]
    rw [packed_payload room pad x (π target) hi]
    cases j <;> simp [target]
  · intro i outside j
    have skip : ¬(start ≤ i.val ∧ i.val-start<R) := by omega
    simp [out,frame,output,skip]
  · intro z; simp [out,frame,output]

end CellPacketGeometry.SiteSort

end BorderVNP
end Computability
end OAI
