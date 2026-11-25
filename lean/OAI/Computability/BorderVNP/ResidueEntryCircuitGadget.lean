import OAI.Computability.BorderVNP.ResidueEntryCircuitRaw

/-! # Gadget multiplicities in the common residue evaluator

Section 11 supplies the multiplicities of a fixed list of advised field values.
The matrix scalar is their product, evaluated on the incoming binary words.
The circuit uses the same list and the same gates for all contractions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open VPVNP Homogenize ResidueBox ResidueIndex MvPolynomial
open scoped Classical

/-- Joint inputs with a little-endian multiplicity word for each advised gadget value. -/
abbrev GadgetInput (σ : Type*) (w : ℕ) (J : Type*) (m : ℕ) := EntryInput σ w ⊕ J × Fin m

variable {σ J ι E K : Type*} [Fintype J] [Fintype σ] [Fintype ι] [Field E] [Field K] [Fintype K]

/-- Multiply the advised gadget values raised to input-controlled exponents. -/
noncomputable def gadgetProduct (σ : Type*) (w m : ℕ) (gadgets : J → K) :
    MvPolynomial (GadgetInput σ w J m) K :=
  ∏ j, binaryPower (C (gadgets j)) m (fun t => X (.inr (j,t)))

omit [Fintype K] in
/-- The entire scalar product is a straight-line circuit of linear size in the
number of multiplicity bits. -/
theorem circuitSize_gadgetProduct (σ : Type*) (w m : ℕ) (gadgets : J → K) :
    circuitSize (gadgetProduct σ w m gadgets) ≤ Fintype.card J*(5*m+1) := by
  let R := MvPolynomial (GadgetInput σ w J m) K
  let t (j : J) : R := binaryPower (C (gadgets j)) m (fun i => X (.inr (j,i)))
  have ht (j : J) : circuitSize (t j) ≤ 5*m := by
    let p := (Program.nil : Program K (GadgetInput σ w J m) 0)
    obtain ⟨q, _, u, hu⟩ := binaryPower_wires p (C (gadgets j)) (hasWire_const p _) m
      (fun i => X (.inr (j,i))) (fun _ => hasWire_var p _)
    exact circuitSize_le_iff.mpr ⟨_, by simp, ⟨q,u⟩, hu⟩
  have hs (S : Finset J) : circuitSize (∏ j ∈ S, t j) ≤ S.card * (5*m+1) := by
    induction S using Finset.induction_on with
    | empty => simpa using (circuitSize_C (σ := GadgetInput σ w J m) (1 : K)).le
    | insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, Nat.add_mul, one_mul]
      have := ht j
      exact (circuitSize_binOp_le .mul ..).trans (by omega)
  exact hs Finset.univ

/-- One chart circuit works on raw index and gadget multiplicity inputs. The old
scalar slot is wired to one and the variable gadget product is applied at the output. -/
theorem exists_gadgetEntryCircuit (φ : E →+* K) (q H width w s m : ℕ) (hq : 0 < q)
    (hw : 2*H*q+3*H+q+width+1 < 2^w) (g : ι → MvPolynomial (Option σ) E)
    (hwidth : width = (q-1) * ∑ t, (g t).totalDegree) (hg : ∀ t, circuitSize (g t) ≤ s)
    (gadgets : J → E) :
    ∃ n ≤ entryGateBudget (Fintype.card ι) (Fintype.card (Option σ)) s
        (q-1).size (Fintype.card Kˣ-1).size w + Fintype.card J*(5*m+1)+1,
      ∃ c : Circuit K (GadgetInput σ w J m) n, ∀ (b : E) (e μ k : Exponent σ),
      Fits H e → Fits H μ → Fits H k → ∀ (x : Option σ → Kˣ) (δ : J → ℕ),
      (∀ j, δ j < 2^m) →
        c.eval id (Sum.elim (queryAssignment q H width w x (encode w H e μ k) 1 (φ b))
          (fun (j,i) => if (δ j).testBit i.val then 1 else 0)) =
        pathSummand φ q g (∏ j, gadgets j^(δ j)) b e μ k x := by
  let A := GadgetInput σ w J m
  let G := gadgetProduct σ w m (φ ∘ gadgets)
  obtain ⟨n,hn,c,hc⟩ := exists_rawEntryCircuit φ q H width w s hq hw g hwidth hg
  let c' := c.subst (fun i => Sum.inl (Sum.inl i : A)) id
  obtain ⟨u,hu⟩ := circuitSize_spec G
  refine ⟨n+circuitSize G+1, Nat.add_le_add_right (Nat.add_le_add hn
    (circuitSize_gadgetProduct σ w m (φ ∘ gadgets))) _, c'.combine .mul u, ?_⟩
  intro b e μ k he hm hk x δ hδ
  let input := queryAssignment q H width w x (encode w H e μ k) (1 : K) (φ b)
  let bits : J × Fin m → K := fun (j,i) => if (δ j).testBit i.val then 1 else 0
  let z := Sum.elim input bits
  have hbase : c'.eval id z = pathSummand φ q g 1 b e μ k x := by
    simp only [c', Circuit.eval_subst, Sum.elim_inl]
    change c.eval id (queryAssignment q H width w x (encode w H e μ k) 1 (φ b)) = _
    simpa only [map_one] using hc 1 b e μ k he hm hk x
  have hu' : u.eval id z = eval z G := by
    refine Eq.trans ?_ (congrArg (eval z) hu)
    rw [Circuit.polynomial, Circuit.eval_hom]
    congr 1 <;> funext i <;> simp
  have hbits (j : J) : (eval z ∘ (fun i : Fin m => X (Sum.inr (j,i)))) =
      fun i => if (δ j).testBit i.val then (1 : K) else 0 := by
    funext i
    rw [Function.comp_apply, eval_X]
    rfl
  have prod : eval z G = φ (∏ j, gadgets j ^ δ j) := by
    simp only [G, gadgetProduct, map_prod, map_binaryPower, eval_C, hbits, map_pow]
    exact Finset.prod_congr rfl (fun j _ => binaryPower_testBit _ _ _ (hδ j))
  change (c'.combine .mul u).eval id z = _
  rw [Circuit.eval_combine, hbase, hu', prod]
  simp only [BinOp.apply, pathSummand, map_one, one_mul]
  split_ifs <;> ring

end ResidueFourier

end BorderVNP
end Computability
end OAI
