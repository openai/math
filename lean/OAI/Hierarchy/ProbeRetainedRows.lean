import OAI.Hierarchy.ProtocolRAMStoredMarkFlags
import OAI.Hierarchy.ProbePurchasedOccurrence
import OAI.Hierarchy.ProbePurchasePopulation

namespace OAI
/-! # Distinct native rows for all bought strips in their admitted signed strata -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped BigOperators Classical Fin.CommRing
noncomputable section

/-- The retained native candidate row chosen for each bought strip is injective.
One physical signed coordinate suffices to separate any two records, since the
entire stock inventory address fits in its word and bought strips are disjoint. -/
theorem retainedEmbedding {z d k : ℕ} (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth start : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen after : Shelf.Mem z d)
    (hk : 0<k) (data : ∀ i : Key z d k,sh.PortData S π depth i after)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded after)
    (keys : count z d k≤2^(Native.wordBits z d Native.copies))
    (room : (depth+1)*paths z S.degree depth≤2^(Native.wordBits z d Native.copies))
    (stock : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k≤2^(Native.wordBits z d Native.copies)) :
    let marked := actualMarks sh phase T kind frozen (k:=k)
    let header := stratumHeader z d k S.degree depth start
    ∃ pick : LiveChains S π depth marked ↪ Fin header.count, ∀ path u,
      (allChainSlot (z:=z) (d:=d) sh S depth header u).eval after ((pick path).val:Word (Native.wordBits z d Native.copies)) =
      (PurchaseInventory.slot (stripAddress S π depth marked path u) : Word (Native.wordBits z d Native.copies)) := by
  intro marked header
  let rows := fun path : LiveChains S π depth marked => retainedBoard sh S π depth start phase T kind frozen after path data loaded keys room
  let pick (p : LiveChains S π depth marked) := (rows p).choose
  have read (p : LiveChains S π depth marked) := (rows p).choose_spec
  have ident : Function.Injective pick := by
    intro p q eqn
    let u : ChainStrip.Axes depth k := (0,⟨0,hk⟩,false)
    let H (i : Fin header.count) := (allChainSlot (z:=z) (d:=d) sh S depth header u).eval after (i.val:Word (Native.wordBits z d Native.copies))
    have same := (read p u).symm.trans ((congrArg H eqn).trans (read q u))
    have nat := congrArg Fin.val same
    rw [Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le stock),
      Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le stock)] at nat
    have addr := PurchaseInventory.slot_injective nat
    let emb := allSignedAddresses S π depth marked (actualMarks_unique sh phase T kind frozen)
    have dup : (p,u)=(q,u) := emb.injective addr
    exact congrArg Prod.fst dup
  exact ⟨⟨pick,ident⟩,read⟩

/-- Extra padded rows contribute nonnegative measured words. Accuracy is needed
only at the actual retained rows, once per acquired strip. -/
theorem sum_retained {P : Type*} [Fintype P] {rows Q n : ℕ} (pick : P ↪ Fin rows)
    (value : Fin rows→ℕ) (actual : P→ℝ) {ε : ℝ} (he : 0≤ε) (hQ : 0<Q)
    (small : Fintype.card P≤n) (accurate : ∀ p,actual p≤(value (pick p):ℝ)/Q+ε)
    (quiet : (∑ i,(value i:ℝ))<4*ε*n*Q) : (∑p,actual p)≤5*ε*n := by
  classical
  have part := Finset.sum_le_sum (s:=Finset.univ) fun p _ => accurate p
  have sub : (∑ p,(value (pick p):ℝ))≤∑ i,(value i:ℝ) := calc
    _ = ∑ i∈Finset.univ.map pick,(value i:ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  simp only [Finset.sum_add_distrib,←Finset.sum_div,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at part
  have mass := (div_lt_iff₀ (Nat.cast_pos.mpr hQ)).2 quiet
  have sampled := div_le_div_of_nonneg_right sub (Nat.cast_nonneg Q)
  have slack := mul_le_mul_of_nonneg_right (show (Fintype.card P:ℝ)≤n by exact_mod_cast small) he
  linarith

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
