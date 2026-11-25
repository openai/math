import OAI.Computability.BorderVNP.PackedBankBox
import OAI.Computability.BorderVNP.PackedPoolCircuit

/-! # Emitting the address words of repeated paid boxes

The finite one-copy identity fixes the row and lane order. Each nonconstant
operand of a staging or box record is an affine function of its term's public
histogram word. A shared Boolean frame supplies the operands for every seed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidBox

open Crossing Crossing.CellBox CellSparse Word ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

/-- Copy count, box base, or one source/destination base of a strided equality. -/
abbrev Operand (d : ℕ) := Option (Option (Fin d × Bool))

variable {n : ℕ} (w : Fin n → ℕ)

private def affine : Operand (∑ r, w r) → Option (ℕ × ℕ)
  | none => none
  | some none => some (∑ r, w r, 0)
  | some (some (k,false)) =>
    let b := (finSigmaFinEquiv (n := w)).symm k
    some (start w b.1, b.2.val)
  | some (some (k,true)) => some (∑ r, w r, k.val)

/-- Natural values serialized into one site's public record operands. -/
def header (copies : ℕ) (h : Operand (∑ r, w r)) : ℕ :=
  match affine w h with
  | none => copies
  | some (s,k) => s*copies+k

/-- Dynamic base and count words, including the inert operands for a zero-copy
box, are bounded by the one-copy arity and the physical repeated width. -/
theorem header_le (copies : ℕ) (h : Operand (∑ r,w r)) :
    header w copies h ≤ copies + copies*(∑ r,w r) + ∑ r,w r := by
  rcases h with _ | (_ | ⟨k,b⟩)
  · simp only [header,affine]; omega
  · simp [header,affine,Nat.mul_comm copies]; omega
  · let z := (finSigmaFinEquiv (n := w)).symm k
    have hz : start w z.1 + z.2.val = k.val :=
      (finSigmaFinEquiv_apply (n := w) z).symm.trans
        (congrArg Fin.val ((finSigmaFinEquiv (n := w)).apply_symm_apply k))
    have hk := k.isLt
    cases b with
    | false =>
      change start w z.1 * copies + z.2.val ≤ _
      have hp := Nat.mul_le_mul_right copies (show start w z.1 ≤ ∑ r,w r by omega)
      rw [Nat.mul_comm (∑ r,w r)] at hp
      omega
    | true =>
      change (∑ r,w r)*copies + k.val ≤ _
      rw [Nat.mul_comm (∑ r,w r)]
      omega

/-- Decode emitted fields to the public records. All remaining operands come from
the fixed one-copy site, including the local directory ID and the two strides. -/
def decode (get : Operand (∑ r, w r) → ℕ) : List Record :=
  (List.ofFn (fun k : Fin (∑ r, w r) =>
    let b := (finSigmaFinEquiv (n := w)).symm k
    Record.equal (get none) 1 ⟨get (some (some (k,false))),w b.1,1⟩
      ⟨get (some (some (k,true))),∑ r, w r,1⟩)) ++
    [.box 0 (get (some none)) (get none) (∑ r, w r)]

variable {K : Type*} [Field K] {D m : ℕ} (e : PaidIdentity K D m)

/-- The emitted operands recover the entire public record list of the paid-term site. -/
theorem decode_header (pos : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) (copies : ℕ) :
    let w := widths (e.net a) v
    decode w (header w copies) = (siteDirectory e pos a v copies).records := by
  dsimp only
  simp only [decode,header,affine,siteDirectory,stageRecords,src,stagePort,arity]
  simp only [Nat.mul_comm copies, Nat.add_zero]

private def code (h : Operand (∑ r, w r)) : WidthExpr Unit :=
  match affine w h with
  | none => .field ()
  | some (s,k) => .binary .add (PoolCircuit.scaleExpr () s) (.const k)

private theorem code_eval (x : Unit → ℕ) (h : Operand (∑ r, w r)) :
    (code w h).eval x = header w (x ()) h := by
  cases ha : affine w h with
  | none => simp [code,header,ha,WidthExpr.eval]
  | some sk => rcases sk with ⟨s,k⟩; simp [code,header,ha,WidthExpr.eval,PoolCircuit.scale_eval,Op.apply]

private theorem code_fits (B : ℕ) (x : Unit → ℕ) (h : Operand (∑ r, w r))
    (hx : x () < 2^B) (hh : header w (x ()) h < 2^B) : (code w h).Fits B x := by
  cases ha : affine w h with
  | none => simpa only [code,ha,WidthExpr.Fits] using hx
  | some sk =>
    rcases sk with ⟨s,k⟩
    simp only [header,ha] at hh
    simp only [code,ha,WidthExpr.Fits]
    refine ⟨PoolCircuit.scale_fits _ _ _ _ hx (by omega), by omega, ?_⟩
    simpa only [Op.apply,PoolCircuit.scale_eval,WidthExpr.eval] using hh

/-- The fixed site/operand pins for a single seed. -/
abbrev Pin := Σ a : Fin e.count, Σ v : (e.net a).Site, Operand (arity e a v)

private noncomputable def pinCode (u : Pin e) : WidthExpr Unit := code (widths (e.net u.1) u.2.1) u.2.2

/-- Total expression size per seed, determined by the fixed one-copy identity alone. -/
noncomputable def nodeBound := ∑ u : Pin e, (pinCode e u).nodes

/-- One Boolean frame writes all dynamic operands of the internal paid sites.
The gate bound is linear in the number of seeds and quadratic in the word width. -/
theorem exists_frame {S σ : Type*} [Fintype S] [Fintype σ] (B : ℕ)
    (source : Frame σ (S × Fin e.count × Fin B)) :
    ∃ f : Frame σ (S × Pin e × Fin B),
      f.size ≤ source.size + 1 + Fintype.card S * (nodeBound e * (100*(B+1)^2)) ∧
      ∀ x s (u : Pin e),
        let c := value (fun j => source.eval x (s,u.1,j))
        let h := header (widths (e.net u.1) u.2.1) c u.2.2
        h < 2^B → value (fun j => f.eval x (s,u,j)) = h := by
  classical
  let leaf (t : S × Pin e) := ((pinCode e t.2).frame B).subst
    (Frame.initial fun i : Unit × Fin B => (t.1,t.2.1,i.2))
  obtain ⟨joint,hs,he⟩ := Crossing.exists_parallelFrames leaf
  let pins (i : S × Pin e × Fin B) : Σ _ : S × Pin e, Fin B := ⟨(i.1,i.2.1),i.2.2⟩
  refine ⟨(joint.select pins).subst source, ?_, ?_⟩
  · have hl (p : S × Pin e) : (leaf p).size ≤ (pinCode e p.2).nodes * (100*(B+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (pinCode e p.2).frame_size B
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hl t)
    have htotal : (∑ p : S × Pin e, (pinCode e p.2).nodes * (100*(B+1)^2)) =
        Fintype.card S * (nodeBound e * (100*(B+1)^2)) := by
      simp [Fintype.sum_prod_type,nodeBound,Finset.sum_mul]
    rw [htotal] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    exact (Nat.add_le_add_left (hs.trans (Nat.add_le_add_left hsum 1)) _).trans_eq (by omega)
  · intro x s u
    dsimp only
    intro hfit
    let z := fun i : Unit × Fin B => source.eval x (s,u.1,i.2)
    have hv : (fun j => ((joint.select pins).subst source).eval x (s,u,j)) =
        ((pinCode e u).frame B).eval z := by
      funext j
      simp [Frame.subst_eval,pins,he,leaf,z]
      congr 1
      funext k
      simp
    rw [hv]
    exact ((pinCode e u).frame_value B z
      (code_fits _ _ _ u.2.2 (value_lt _) hfit)).trans (code_eval _ _ _)

end Packing.PaidBox

end BorderVNP
end Computability
end OAI
