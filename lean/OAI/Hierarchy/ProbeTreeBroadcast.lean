import OAI.ThreeFlat.CatalyticEmbedding
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths
import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.DiagonalProduct
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice

namespace OAI
/-! # Absorbing a finite hidden choice by genuine connected equality wires -/

noncomputable section
namespace Hierarchy.Probe

open scoped Classical BigOperators
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.CatalyticEmbedding

variable {k n : ℕ} {F : Type*} [Field F] [Nonempty (Fin k)]
  {E W : Type} [Fintype E] [Fintype W]

/-- Every assignment constant along the chosen broadcast links is constant
on the entire local ball. This works also when the ball has just one site. -/
def BroadcastConnected (G : PortGraph (Fin k) E) : Prop :=
  ∀ {W : Type} (x : Fin k → W), (∀ e, x (G.tail e) = x (G.head e)) → ∀ i j, x i = x j

omit [Nonempty (Fin k)] [Fintype E] in
theorem broadcastConnected_of_paths (G : PortGraph (Fin k) E)
    (paths : ∀ i j, Relation.EqvGen (fun a b => ∃ e, G.tail e = a ∧ G.head e = b) i j) :
    BroadcastConnected G := by
  intro W x eqn i j
  have all {a b} (h : Relation.EqvGen (fun a b => ∃ e, G.tail e = a ∧ G.head e = b) a b) :
      x a = x b := by
    induction h with
    | rel _ _ h => obtain ⟨e,rfl,rfl⟩ := h; exact eqn e
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ l r => exact l.trans r
  exact all (paths i j)

private theorem indicator_eq {K : Type*} [One K] [Zero K] {a b : Prop}
    {da : Decidable a} {db : Decidable b} (same : a↔b) : @ite K a da 1 0 = @ite K b db 1 0 := by
  cases da with
  | isTrue h => cases db with
                | isTrue _ => rfl
                | isFalse h' => exact False.elim (h' (same.mp h))
  | isFalse h => cases db with
                 | isFalse _ => rfl
                 | isTrue h' => exact False.elim (h (same.mpr h'))

/-- Copying the local color to every incident half-word is a single local
matrix at each site. Agreement along the links enforces one global color. -/
theorem broadcast_diagonal (G : PortGraph (Fin k) E) (conn : BroadcastConnected G)
    (code : W ↪ Fin (2^n)) :
    (Raw.diagonal (Fin k) F W).Restricts (G.rawWiring F (fun _ => Fin (2^n))) := by
  classical
  let root := Classical.arbitrary (Fin k)
  let sel (i : Fin k) (c : W) : G.State (fun _ => Fin (2^n)) i := fun _ => code c
  apply Raw.restrict_by_read (fun i c=>sel i c)
  intro x
  let ξ : Fin k→W:=x
  change (Raw.diagonal (Fin k) F W).coeff ξ = _
  rw [Raw.diagonal_coeff_at (K:=F) root ξ]
  have iff : (∀ i, ξ i=ξ root) ↔ ∀ e, code (ξ (G.tail e)) = code (ξ (G.head e)) :=
    ⟨fun h e => congrArg code ((h (G.tail e)).trans (h (G.head e)).symm),
      fun h i => conn ξ (fun e => code.injective (h e)) i root⟩
  exact indicator_eq iff

/-- The graph with the specified number of bits on each connected link
supplies the diagonal of the actual alphabet. -/
theorem broadcast_class (G : PortGraph (Fin k) E) (conn : BroadcastConnected G)
    (code : W ↪ Fin (2^n)) :
    (Fintype.card W : TensorClass.{0} (Fin k) F) ≤
      graphClass F (G.chordWidths (fun _ => n)) := by
  rw [← ofRaw_diagonal_eq_natCast (Fin k) F W,
      ← G.ofRaw_rawWiring_eq_graphClass F (fun _ => n)]
  exact ofRaw_le_iff.mpr (broadcast_diagonal G conn code)

/-- An ordinary sum of a family of local products is itself one physical
restriction after installing the common data and the broadcast word on the
tree. It retains the original summands with their individual coefficients. -/
theorem sum_restricts_broadcast {a b : Widths k} (G : PortGraph (Fin k) E)
    (conn : BroadcastConnected G) (code : W ↪ Fin (2^n))
    (z : W → (∀ i, State a i) → F)
    (tiles : ∀ w, ({raw F a with coeff := z w} : Raw (Fin k) F).Restricts (raw F b)) :
    ({raw F a with coeff := ∑ w, z w} : Raw (Fin k) F).Restricts
      (raw F (b + G.chordWidths (fun _ => n))) := by
  apply ofRaw_le_iff.mp
  rw [ofRaw_raw,graphClass_add]
  change ofCoeffs (∑ w, z w) ≤ _
  calc
    _ ≤ ∑ w, ofCoeffs (z w) := ordinary_sum_le z
    _ ≤ ∑ _ : W, graphClass F b := Finset.sum_le_sum fun w _ =>
      (ofRaw_le_iff.mpr (tiles w)).trans_eq (ofRaw_raw F b)
    _ = graphClass F b * (Fintype.card W : TensorClass.{0} (Fin k) F) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]
    _ ≤ _ := mul_mono le_rfl (broadcast_class G conn code)

/-- Partition the existing coefficient family by its public labels. Each
new branch is definitionally the sum of the coefficients on its fiber, and
each of those fibers has one common installed data tensor. -/
theorem group_restrictions {a : Widths k} {H L : Type} [Fintype H] [Fintype L]
    (tag : L → H) (b : H → Widths k) (z : L → (∀ i, State a i) → F)
    (sum : (raw F a).coeff = ∑ l, z l)
    (tiles : ∀ l, ({raw F a with coeff := z l} : Raw (Fin k) F).Restricts (raw F (b (tag l))))
    (G : PortGraph (Fin k) E) (conn : BroadcastConnected G)
    (code : ∀ h, {l // tag l = h} ↪ Fin (2^n)) :
    let branch (h : H) := ∑ l : {l // tag l=h}, z l.val
    (raw F a).coeff = ∑ h, branch h ∧ ∀ h,
      ({raw F a with coeff := branch h} : Raw (Fin k) F).Restricts
        (raw F (b h + G.chordWidths (fun _ => n))) := by
  constructor
  · exact sum.trans (Fintype.sum_fiberwise tag z).symm
  · intro h
    apply sum_restricts_broadcast G conn (code h) (fun l => z l.val)
    intro l
    simpa only [l.property] using tiles l.val

private theorem enumeration {I K : Type*} [AddCommMonoid K] (s t : Fintype I) (f : I→K) :
    (@Finset.univ I s).sum f=(@Finset.univ I t).sum f :=
  congrArg (fun e : Fintype I=>(@Finset.univ I e).sum f) (Subsingleton.elim s t)

private theorem coeff_point {T B K : Type*} [Fintype T] [AddCommMonoid K]
    (f : T→B→K) (x : B) : (∑a,f a) x=∑a,f a x := Finset.sum_apply _ _ _

/-- Applying the same post-composition matrices to every branch commutes
with the ordinary sum, including cancellation in positive characteristic. -/
theorem transport_sum {S : ℕ} [Nonempty (Fin S)] {H : Type*} [Fintype H]
    (X Y : Raw.{0} (Fin S) F) (branches : H → Raw.{0} (Fin S) F)
    (coeff : H → (∀ i, X.Leg i) → F) (total : X.coeff = ∑ h, coeff h)
    (repack : Y.Restricts X)
    (tiles : ∀ h, ({X with coeff := coeff h} : Raw (Fin S) F).Restricts (branches h)) :
    ∃ M : ∀ i, Y.Leg i → X.Leg i → F,
      let out (h : H) (x : ∀ i, Y.Leg i) := ∑ y, coeff h y * ∏ i, M i (x i) (y i)
      Y.coeff = ∑ h, out h ∧
        ∀ h, ({Y with coeff := out h} : Raw (Fin S) F).Restricts (branches h) := by
  obtain ⟨M,applyM⟩ := repack
  let out (h : H) (x : ∀i,Y.Leg i) := ∑y : ∀ i,X.Leg i,coeff h y*∏i,M i (x i) (y i)
  refine ⟨M,?_,?_⟩
  · funext x
    calc
      Y.coeff x = ∑ y : ∀i,X.Leg i,X.coeff y*∏i,M i (x i) (y i) :=
        (applyM x).trans (enumeration _ _ _)
      _ = ∑ y : ∀i,X.Leg i,∑ h,coeff h y*∏i,M i (x i) (y i) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [(congrFun total y).trans (coeff_point coeff y),Finset.sum_mul]
      _ = ∑ h,out h x := Finset.sum_comm
      _ = (∑h,out h) x := (coeff_point out x).symm
  · intro h
    exact restrict_trans (X := out h) (Y := coeff h) ⟨M,fun _ => enumeration _ _ _⟩ (tiles h)

/-- Re-embedding all local coefficients in an increasing enumeration of the
common named sites preserves the ordinary sum and its separate physical
restriction on the pushed source widths for each public branch. -/
theorem named_sum {S : ℕ} [Nonempty (Fin S)] (place : Fin k ↪o Fin S)
    {H : Type*} [Fintype H] (a : Widths k) (b : H → Widths k)
    (z : H → (∀ i, State a i) → F) (hz : (raw F a).coeff = ∑ h, z h)
    (tiles : ∀ h, ({raw F a with coeff := z h} : Raw (Fin k) F).Restricts (raw F (b h))) :
    ∃ Z : H → (∀ i, State (push place a) i) → F,
      (raw F (push place a)).coeff = ∑ h, Z h ∧
        ∀ h, ({raw F (push place a) with coeff := Z h} : Raw (Fin S) F).Restricts
          (raw F (push place (b h))) := by
  let X := raw F a
  let U (h : H) := ({X with coeff := z h} : Raw (Fin k) F).group place
  have comb : (X.group place).coeff = ∑ h, (U h).coeff := by
    change (fun x : (v : Fin S) → (p : {i // place i=v}) → X.Leg p.1 =>
      X.coeff ((groupIndexEquiv place X.Leg).symm x)) =
      ∑ h, (fun x => z h ((groupIndexEquiv place X.Leg).symm x))
    funext x
    change (raw F a).coeff _ = _
    exact (congrFun hz _).trans ((coeff_point z _).trans (coeff_point (fun h x=>z h ((groupIndexEquiv place X.Leg).symm x)) x).symm)
  have rep (v : Widths k) :
      ofRaw ((raw F v).group place) = ofRaw (raw F (push place v)) := by
    change groupMulHom (K := F) place (ofRaw (raw F v)) = _
    rw [ofRaw_raw,ofRaw_raw,group_graph]
  have terms (h : H) : (U h).Restricts (raw F (push place (b h))) :=
    ofRaw_le_iff.mp ((ofRaw_le_iff.mpr (Raw.group_restricts place (tiles h))).trans_eq (rep _))
  obtain ⟨M,all,restr⟩ := transport_sum (X.group place) (raw F (push place a))
    (fun h => raw F (push place (b h))) (fun h => (U h).coeff) comb
    (ofRaw_le_iff.mp (rep a).symm.le) terms
  exact ⟨_,all,restr⟩


end Hierarchy.Probe
end

end OAI
