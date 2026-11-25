import OAI.Computability.BorderVNP.UnsignedTranscript
import OAI.Computability.VPVNP.VerifierMachineNetwork

/-! # Weighted CNF transcripts for multi-output crossing verifiers

A single gate table computes both the acceptance test and the output flags. For each
weighted occurrence a fresh copy bit is linked to its output reference. This permits
distinct projection weights even for repeated references. The unique transcript of
an accepted input contributes exactly its product of flagged variables and scalars.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FrameCNF

open VPVNP HardnessCNF TranscriptCNF MvPolynomial VerifierNetwork
open scoped Classical

variable {σ τ : Type*} [Fintype σ] [Fintype τ] {g : ℕ}

private abbrev Slots (σ τ : Type*) (g : ℕ) := Bool ⊕ σ ⊕ Fin g ⊕ τ
private abbrev width (σ τ : Type*) [Fintype σ] [Fintype τ] (g : ℕ) := Fintype.card (Slots σ τ g)
private noncomputable abbrev slots := Fintype.equivFin (Slots σ τ g)
private noncomputable abbrev cSlot (b : Bool) : Fin (width σ τ g) := slots (.inl b)
private noncomputable abbrev iSlot (j : σ) : Fin (width σ τ g) := slots (.inr (.inl j))
private noncomputable abbrev gSlot (j : Fin g) : Fin (width σ τ g) := slots (.inr (.inr (.inl j)))
private noncomputable abbrev oSlot (j : τ) : Fin (width σ τ g) := slots (.inr (.inr (.inr j)))
private noncomputable abbrev addr (r : Ref Bool σ g) : Fin (width σ τ g) :=
  address cSlot iSlot gSlot r

private noncomputable def formula (p : BooleanTranscript.Program σ g) (ok : Ref Bool σ g)
    (out : τ → Ref Bool σ g) : CNF (width σ τ g) :=
  [[(cSlot false, false)], [(cSlot true, true)], [(addr ok, true)]] ++
    programClauses cSlot iSlot p gSlot ++
    meetCNF (fun j => matchClauses (oSlot j) (fun _ : Unit => addr (out j)) (fun _ => true))

private noncomputable def copyWeights {R V : Type*} [One R] (w : Projection R τ V) :
    Projection R (Fin (width σ τ g)) V := fun i => match slots.symm i with
  | .inr (.inr (.inr j)) => w j
  | _ => .inr 1

private noncomputable def fill (p : BooleanTranscript.Program σ g) (out : τ → Ref Bool σ g)
    (x : σ → Bool) : Fin (width σ τ g) → Bool := fun i => match slots.symm i with
  | .inl b => b
  | .inr (.inl j) => x j
  | .inr (.inr (.inl j)) => p.run x j
  | .inr (.inr (.inr j)) => (out j).read id x (p.run x)

private theorem satisfied (p : BooleanTranscript.Program σ g) (ok : Ref Bool σ g)
    (out : τ → Ref Bool σ g) (z : Fin (width σ τ g) → Bool) :
    Satisfies (formula p ok out) z ↔
      z = fill p out (z ∘ iSlot) ∧ ok.read id (z ∘ iSlot) (p.run (z ∘ iSlot)) = true := by
  have core : Satisfies (formula p ok out) z ↔
      ((z (cSlot false) = false ∧ z (cSlot true) = true ∧ z (addr ok) = true) ∧
        Satisfies (programClauses cSlot iSlot p gSlot) z) ∧
        ∀ j, z (oSlot j) = z (addr (out j)) := by
    have pins : Satisfies [[(cSlot false, false)], [(cSlot true, true)], [(addr ok, true)]] z ↔
        z (cSlot false) = false ∧ z (cSlot true) = true ∧ z (addr ok) = true := by
      simp [Satisfies]
    have link (j : τ) : Satisfies (matchClauses (oSlot j)
        (fun _ : Unit => addr (out j)) (fun _ => true)) z ↔ z (oSlot j) = z (addr (out j)) := by
      rw [satisfies_matchClauses]
      simp only [forall_const]
      exact Bool.eq_iff_iff.symm
    simp only [formula, satisfies_append, pins, satisfies_meetCNF, link]
  rw [core]
  constructor
  · rintro ⟨⟨⟨hc0, hc1, hok⟩, hgate⟩, hout⟩
    have hc : ∀ b, z (cSlot b) = b := by intro b; cases b <;> assumption
    have hg := (satisfies_programClauses cSlot iSlot p gSlot z hc).mp hgate
    have readAddr (r : Ref Bool σ g) : z (addr r) = r.read id (z ∘ iSlot) (p.run (z ∘ iSlot)) := by
      rw [addr, address_read _ _ _ _ hc, hg]
    refine ⟨?_, (readAddr ok).symm.trans hok⟩
    funext i
    obtain ⟨j, rfl⟩ := slots.surjective i
    rcases j with b | x | v | o
    · simpa only [fill, Equiv.symm_apply_apply] using hc b
    · simp [fill]
    · simpa only [fill, Equiv.symm_apply_apply, Function.comp_apply] using congrFun hg v
    · simpa only [fill, Equiv.symm_apply_apply] using (hout o).trans (readAddr _)
  · rintro ⟨hz, hok⟩
    have val (j : Slots σ τ g) := congrFun hz (slots j)
    have hc (b : Bool) : z (cSlot b) = b := by simpa [fill] using val (.inl b)
    have hg : z ∘ gSlot = p.run (z ∘ iSlot) := by
      funext i
      simpa [fill, Function.comp_def] using val (.inr (.inr (.inl i)))
    have readAddr (r : Ref Bool σ g) : z (addr r) = r.read id (z ∘ iSlot) (p.run (z ∘ iSlot)) := by
      rw [addr, address_read _ _ _ _ hc, hg]
    refine ⟨⟨⟨hc false, hc true, (readAddr ok).trans hok⟩,
      (satisfies_programClauses cSlot iSlot p gSlot z hc).mpr hg⟩, fun j => ?_⟩
    rw [readAddr]
    simpa [fill] using val (.inr (.inr (.inr j)))

private theorem product_fill {R V : Type*} [CommRing R] (p : BooleanTranscript.Program σ g)
    (out : τ → Ref Bool σ g) (w : Projection R τ V) (x : σ → Bool) :
    (∏ i, if fill p out x i then (copyWeights w i).elim X C else 1) =
      ∏ j, if (out j).read id x (p.run x) then (w j).elim X C else 1 := by
  rw [← slots.prod_comp]
  simp [fill, copyWeights, Slots, Fintype.prod_sum_type]

private theorem weighted (p : BooleanTranscript.Program σ g) (ok : Ref Bool σ g)
    (out : τ → Ref Bool σ g) {R V : Type*} [CommRing R] (w : Projection R τ V) :
    weightedCNF (formula p ok out) (fun i => (copyWeights w i).elim X C) =
      ∑ x : σ → Bool, if ok.read id x (p.run x) then
        ∏ j, if (out j).read id x (p.run x) then (w j).elim X C else 1 else 0 := by
  classical
  have inputs (x : σ → Bool) : fill p out x ∘ iSlot = x := by funext j; simp [fill]
  have hinj : Function.Injective (fill p out) := by
    intro x y he
    simpa only [inputs] using congrArg (fun z => z ∘ iSlot) he
  rw [weightedCNF, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (fill p out))),
    Finset.sum_image hinj.injOn]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [satisfied, inputs]
    simp [product_fill]
  · intro z _ hmiss
    have h : ¬ Satisfies (formula p ok out) z := by
      intro hz
      exact hmiss (Finset.mem_image.mpr ⟨z ∘ iSlot, Finset.mem_univ _, ((satisfied ..).mp hz).1.symm⟩)
    simp [h]

private theorem same_cast_program {σ : Type*} {n m : ℕ} (h : n=m)
    (p : BooleanTranscript.Program σ n) (r s : Ref Bool σ n) :
    ((h ▸ (⟨p,r⟩ : BooleanTranscript.Circuit σ n) : BooleanTranscript.Circuit σ m).program) =
    ((h ▸ (⟨p,s⟩ : BooleanTranscript.Circuit σ n) : BooleanTranscript.Circuit σ m).program) := by
  cases h
  rfl

private theorem common_program {O : Type*} [Fintype O] (f : Frame σ O) (i j : O) :
    (f.circuit i).program = (f.circuit j).program := by
  unfold Frame.circuit CookCircuit.toTranscriptWith
  apply same_cast_program

/-- Weighted flags on one shared Boolean frame have a parsimonious weighted CNF
with linear width and literal count. Input references and output references can repeat. -/
theorem exists_weightedCNF {O R V : Type*} [Fintype O] [CommRing R] (f : Frame σ O)
    (accept : O) (outputs : τ → O) (w : Projection R τ V) :
    ∃ k ≤ 2 + Fintype.card σ + 4 * f.size + Fintype.card τ,
      ∃ c : CNF k, literalCount c ≤ 3 + 28 * f.size + 4 * Fintype.card τ ∧
      ∃ a : Projection R (Fin k) V,
        weightedCNF c (fun i => (a i).elim X C) =
          ∑ x : σ → Bool, if f.eval x accept then
            ∏ j, if f.eval x (outputs j) then (w j).elim X C else 1 else 0 := by
  let p := (f.circuit accept).program
  let ok := (f.circuit accept).output
  let out (j : τ) : Ref Bool σ (f.circuitSize accept) := (f.circuit (outputs j)).output
  have hsize := f.circuitSize_le accept
  refine ⟨width σ τ (f.circuitSize accept), ?_, formula p ok out, ?_, copyWeights w, ?_⟩
  · simp only [width, Slots, Fintype.card_sum, Fintype.card_bool, Fintype.card_fin]
    omega
  · have hg := literalCount_programClauses_le cSlot iSlot p (gSlot (τ := τ))
    have hl := literalCount_meetCNF_const
      (fun j => matchClauses (oSlot j) (fun _ : Unit => addr (out j)) (fun _ => true)) 4
      (fun _ => by simp [literalCount_matchClauses])
    unfold formula
    rw [literalCount_append, literalCount_append, hl]
    have hpin : literalCount [[(cSlot false, false)], [(cSlot true, true)],
        [(addr (τ := τ) ok, true)]] = 3 := rfl
    rw [hpin]
    omega
  · rw [weighted]
    have hok (x : σ → Bool) : ok.read id x (p.run x) = f.eval x accept :=
      f.circuit_eval accept x
    have hout (j : τ) (x : σ → Bool) : (out j).read id x (p.run x) = f.eval x (outputs j) := by
      rw [show p = (f.circuit (outputs j)).program from common_program f _ _]
      exact f.circuit_eval (outputs j) x
    simp only [hok, hout]

end Crossing.FrameCNF

end BorderVNP
end Computability
end OAI
