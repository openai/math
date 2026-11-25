import OAI.Hierarchy.DescentSubroundExteriorTokens
import OAI.Hierarchy.DescentSeedExteriorTokens
import OAI.Hierarchy.DescentOrdinaryRecipeCount
import OAI.Hierarchy.DescentCoalescedRecords
import OAI.Hierarchy.DescentStageAtoms
import OAI.Hierarchy.DescentBundleSeed

namespace OAI
/-! # Actual operand nodes are the paid records together with the original exposed equalities -/

namespace Hierarchy.DescentKernelHistory
open DescentSixParty DescentResetTrunks DescentNamedContact Computability.BorderVNP.Crossing DescentNetworkPartition DescentHostDirectory GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {U F P C : Type} [Field F] [Fintype P] [Fintype C] {bits : P→ℕ} {d n : ℕ}

omit [Fintype P] in
theorem quotient_nodes_at (N : Network n P bits) (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d))
    (ball : ∀v,‖pos v‖≤1) (old : SiteBits (U:=U) N) (v : C) :
    Fintype.card ((quotientBits N loc pos ball old v).Node)=bin loc (fun i=>Fintype.card (old i).Node) v := by
  change Fintype.card (Σi : Fibre loc v,(old i.val).Node)=_
  rw [Fintype.card_sigma]
  exact width_bin loc (fun i : N.Site => Fintype.card (old i).Node) v

namespace BitDescription
variable {W : MarkedWorld F d P bits} {H : Type} (B : BitDescription W) (records : W.graph.Site→List H)
def Tokenized : Prop := ∀u,Fintype.card (B.recipe u).Node=(records u).length+W.exteriorTokens u

theorem Tokenized.selected {I V : Type} [Fintype I] (old : B.Tokenized records)
    (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (hz : ∀i,0<z i) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b)
    {Z : ℕ} (room : ∀i,z i≤Z) (pack : W.graph.Site→V) (p : I→Profile G.C) :
    (B.selected G pick z hz fit room pack p).Tokenized
      (StarKeys.newRecords W.graph pick (bestLayout (branchWidth G z p)) pack records z p) := by
  let X:=W.selected G pick z hz fit pack p
  let loc:=newSite W.graph pick (bestLayout (branchWidth G z p)) pack
  let src (u : W.graph.Site):=loc (.inl u)
  let fresh (t : I×Fin 6):=loc (.inr t)
  intro v
  refine (quotient_nodes_at (physical W.graph pick (branchWidth G z p)) loc
    (fun _ => (0 : EuclideanSpace ℝ (Fin d))) (fun _ => by simp)
    (physicalBits G W.toWorld pick z room p B.recipe) v).trans ?_
  refine Eq.trans ?_ (congrArg (fun a : ℕ => a + X.exteriorTokens v)
    (StarKeys.newRecords_length W.graph pick (bestLayout (branchWidth G z p)) pack
      records z p v)).symm
  have split :
      bin loc (fun u=>Fintype.card (physicalBits G W.toWorld pick z room p B.recipe u).Node) v=
        bin src (fun u=>Fintype.card (B.recipe u).Node) v + bin fresh (fun _=>1) v := by
    change (∑ u : W.graph.Site ⊕ (I × Fin 6), if loc u = v then
      Fintype.card (physicalBits G W.toWorld pick z room p B.recipe u).Node else 0) = _
    rw [Fintype.sum_sum_type]
    apply congrArg₂ Nat.add
    · apply Finset.sum_congr (by ext i; simp only [Finset.mem_univ])
      intro u _
      change (if src u = v then _ else 0) = (if src u = v then _ else 0)
      by_cases h : src u = v
      · simp only [ite_eq_left h]; exact @Fintype.card_congr _ _ _ _ (Equiv.refl (B.recipe u).Node)
      · simp only [ite_eq_right h]
    · apply Finset.sum_congr (by ext i; simp only [Finset.mem_univ])
      rintro ⟨i,j⟩ _
      change (if fresh (i,j)=v then Fintype.card Unit else 0)=
        (if fresh (i,j)=v then 1 else 0)
      rw [Fintype.card_unit]
  with_unfolding_all refine split.trans ?_
  have recorded : bin src (fun u=>Fintype.card (B.recipe u).Node) v=
      (∑u : Fibre src v,(records u.val).length)+X.exteriorTokens v := by
    have counts : (fun u => Fintype.card (B.recipe u).Node) =
        (fun u => (records u).length) + W.exteriorTokens := funext old
    refine (congrArg (fun w => bin src w v) counts).trans ?_
    refine (bin_add src (fun u => (records u).length) W.exteriorTokens v).trans ?_
    exact congrArg₂ Nat.add (width_bin src (fun u => (records u).length) v).symm
      (W.exterior_fiber (Z := X) src (fun _ => rfl) (fun _ => 1) v)
  refine (congrArg₂ Nat.add recorded (width_bin fresh (fun _ => 1) v).symm).trans ?_
  change (_+X.exteriorTokens v)+(∑_ : Fibre fresh v,1)=_+Fintype.card (Fibre fresh v)+X.exteriorTokens v
  simp [Nat.add_comm,Nat.add_left_comm]
  with_unfolding_all apply Finset.sum_congr
  · apply Finset.ext
    intro u
    exact ⟨fun _ => Finset.mem_univ u, fun _ => Finset.mem_univ u⟩
  · intro u _
    rfl

theorem Tokenized.coalesced {V : Type} [DecidableEq V] (old : B.Tokenized records)
    (key : W.graph.Site↪Key V) (flag : V→Bool) (k g : ℕ) :
    (B.coalesced key flag k g).Tokenized (W.coalescedRecords key flag k g records) := by
  intro v
  let f:=W.address key flag k g
  let post := W.coalesced key flag k g
  refine (quotient_nodes_at W.graph f (fun _ => (0 : EuclideanSpace ℝ (Fin d)))
    (fun _ => by simp) B.recipe v).trans ?_
  refine Eq.trans ?_ (congrArg (fun a : ℕ => a + post.exteriorTokens v)
    (W.coalescedRecords_length key flag k g records v)).symm
  have counts : (fun u => Fintype.card (B.recipe u).Node) =
      (fun u => (records u).length) + W.exteriorTokens := funext old
  with_unfolding_all refine (congrArg (fun w => bin f w v) counts).trans ?_
  refine (bin_add f (fun u => (records u).length) W.exteriorTokens v).trans ?_
  exact congrArg₂ Nat.add (width_bin f (fun u => (records u).length) v).symm
    (W.exterior_fiber (Z := post) f (fun _ => rfl) (fun _ => 1) v)

theorem Tokenized.split (old : B.Tokenized records) (m : W.graph.Edge→ℕ) (q : ℕ)
    (fit : ∀e∈W.core,W.graph.width e=m e*q) : (B.pieces m q fit).Tokenized records :=
  old

theorem Tokenized.renamed (old : B.Tokenized records) (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    (B.renamed s e).Tokenized (records∘s.symm) := by
  intro v
  obtain ⟨u,rfl⟩:=s.surjective v
  refine (old (s.symm (s u))).trans ?_
  apply congrArg (fun n : ℕ => (records (s.symm (s u))).length + n)
  rw [s.symm_apply_apply]
  unfold MarkedWorld.exteriorTokens bin
  apply Finset.sum_congr rfl
  intro i _
  change _=(if s (W.graph.attach i)=s u then _ else _)
  rw [s.injective.eq_iff]

open DescentInitialHost Catalyst CatalystSubstitution CorrectionBatch
theorem tokenized_seed {k p R s : ℕ} (X : Approximation F k p) (c : (initialGroup X R s).Choice) :
    (initial X R s c).Tokenized (seedRecords X c) := by
  rintro ⟨j,u|pin⟩
  · have notHub : seedHub X c ⟨j,Sum.inl u⟩=false := rfl
    have zero := ((initialGroup X R s).state c).exterior_eq_zero
      (seedHub X c) (seed_exterior_owners X c) ⟨j,Sum.inl u⟩ notHub
    exact (DescentBundleHistory.initial_nodes X R s c ⟨j,Sum.inl u⟩).trans
      (congrArg (fun n : ℕ => 1 + n) zero.symm)
  · refine (DescentBundleHistory.initial_nodes X R s c ⟨j,Sum.inr pin⟩).trans ?_
    change 1 = 0 + ((initialGroup X R s).state c).exteriorTokens ⟨j,Sum.inr pin⟩
    exact (seed_exterior_count X c j pin).symm.trans (Nat.zero_add _).symm

end BitDescription
end
end Hierarchy.DescentKernelHistory

end OAI
