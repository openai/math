import OAI.Computability.NearSquareRoot.InterchangeStageLedger
import OAI.Computability.NearSquareRoot.InterchangeStageScript

/-!
# Shared rectangle routing for one sum of address changes

Reserve positions are prepared once per source incidence. The query-dependent sums
stay in their rectangle coordinates except for terms incident to selected basis rows
and columns. Destination contributions from every query accumulate before the reserve
positions are restored.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.StageRoute

open StageLedger

variable {L B Q H E K Addr : Type} [DecidableEq L] [Fintype B] [Fintype L]
  [Fintype H] [Fintype Q] [AddCommGroup E] [Field K] [Module K E]

/-- Endpoint coordinate diagrams. All maps go from native to common coordinates.
`C` takes local rectangle addresses to one fixed address order. -/
structure Layout (r : B → Rectangle L) (Q Addr : Type) where
  S : Q → L → Equiv.Perm Addr
  T : Q → L → Equiv.Perm Addr
  C : Q → B → Equiv.Perm Addr
  prepareSrc : Endpoint r false → Equiv.Perm Addr
  prepareDst : Endpoint r true → Equiv.Perm Addr
  localSrc : Q → Endpoint r false → Equiv.Perm Addr
  localDst : Q → Endpoint r true → Equiv.Perm Addr
  source_triangle : ∀ j e,
    (prepareSrc e).trans ((localSrc j e).trans (C j e.2)) = S j e.1
  target_triangle : ∀ j e,
    (prepareDst e).trans ((localDst j e).trans (C j e.2)) = T j e.1

/-- Finite catalog of address conversions in a stage. The selected row and column
types carry only their incidences, so no dense matrix-row routes are generated. -/
inductive Move (r : B → Rectangle L) (Q : Type) (I J : H → L)
  | idle
  | prepare (e : Endpoint r false)
  | restore (e : Endpoint r true)
  | align (j : Q) (e : Endpoint r false)
  | unalign (j : Q) (e : Endpoint r true)
  | gather (j : Q) (t : RankTerm r true I)
  | distribute (j : Q) (t : RankTerm r false J)

namespace Layout

variable {r : B → Rectangle L} {I J : H → L}

def perm (g : Layout r Q Addr) : Move r Q I J → Equiv.Perm Addr
  | .idle => .refl _
  | .prepare e => g.prepareSrc e
  | .restore e => (g.prepareDst e).symm
  | .align j e => g.localSrc j e
  | .unalign j e => (g.localDst j e).symm
  | .gather j ⟨i, none⟩ => g.S j (I i)
  | .gather j ⟨_, some b⟩ => g.C j b
  | .distribute j ⟨i, none⟩ => (g.T j (J i)).symm
  | .distribute j ⟨_, some b⟩ => (g.C j b).symm

omit [DecidableEq L] [Fintype B] [Fintype L] [Fintype Q] [Fintype H] in
theorem source_at (g : Layout r Q Addr) (j : Q) (e : Endpoint r false) (a : Addr) :
    (g.prepareSrc e).symm ((g.localSrc j e).symm a) = (g.S j e.1).symm (g.C j e.2 a) := by
  rw [← g.source_triangle j e]
  simp

omit [DecidableEq L] [Fintype B] [Fintype L] [Fintype Q] [Fintype H] in
theorem dest_at (g : Layout r Q Addr) (j : Q) (e : Endpoint r true) (a : Addr) :
    g.C j e.2 (g.localDst j e (g.prepareDst e a)) = g.T j e.1 a :=
  DFunLike.congr_fun (g.target_triangle j e) a

end Layout

/-- The one copy shared by all destinations of a rectangle, in its local order. -/
def partialTable (r : B → Rectangle L) (data : (L ⊕ (Q × Endpoint r false)) → E) :
    (L ⊕ (Q × B)) → E
  | .inl v => data (.inl v)
  | .inr (j,b) => ∑ v : (r b).sources, data (.inr (j, ⟨v.1, b, v.2⟩))

/-- Choose a singleton from its original row or use the rectangle sum previously
computed in local order. -/
def gatherFrom (r : B → Rectangle L) (I : H → L) (j : Q) : RankTerm r true I → L ⊕ (Q × B)
  | ⟨i,none⟩ => .inl (I i)
  | ⟨_,some b⟩ => .inr (j,b.1)

/-- Sum in common order and apply the dense inverse minor there. -/
def mixTable (r : B → Rectangle L) (I : H → L) (M : Matrix H H K)
    (data : ((L ⊕ (Q × B)) ⊕ (Q × RankTerm r true I)) → E) :
    ((L ⊕ (Q × B)) ⊕ (Q × H)) → E
  | .inl u => data (.inl u)
  | .inr (j,i) => applyRows M (fun k =>
      data (.inr (j,⟨k,none⟩)) + ∑ b : Incident r true (I k), data (.inr (j,⟨k,some b⟩))) i

/-- Keep each direct singleton in the destination's native order. All indirect
contributions, including the negative rectangle correction, are combined locally. -/
def scatterTable (r : B → Rectangle L) (J : H → L)
    (data : ((L ⊕ (Q × B)) ⊕ (Q × RankTerm r false J)) → E) :
    ((L ⊕ (Q × L)) ⊕ (Q × B)) → E
  | .inl (.inl v) => data (.inl (.inl v))
  | .inl (.inr (j,w)) => ∑ i, if w = J i then data (.inr (j,⟨i,none⟩)) else 0
  | .inr (j,b) => (∑ i, if hi : J i ∈ (r b).sources then data (.inr (j, ⟨i, some ⟨b,hi⟩⟩)) else 0)
      - data (.inl (.inr (j,b)))

/-- Apply the stage's row matrices and accumulate the queries. The indirect
summand remains at the prepared destination until this table has run. -/
def sumQueries (r : B → Rectangle L) (A₀ : E →+ E) (A : Q → E →+ E)
    (data : ((L ⊕ (Q × L)) ⊕ (Q × Endpoint r true)) → E) : L ⊕ Endpoint r true → E
  | .inl w => A₀ (data (.inl (.inl w))) + ∑ j, A j (data (.inl (.inr (j,w))))
  | .inr e => ∑ j, A j (data (.inr (j,e)))

/-- Add all the repaired contributions at each destination. -/
def finishTable (r : B → Rectangle L) (data : (L ⊕ Endpoint r true) → E) (w : L) : E :=
  data (.inl w) + ∑ b : Incident r true w, data (.inr ⟨w,b⟩)

open StageScript

variable (r : B → Rectangle L) (I J : H → L)

/-- Prepare occupied reserves once and align each source copy with its query's
rectangle layout. The output includes one retained original per label. -/
def partials : Program (Move r Q I J) E L (L ⊕ (Q × B)) :=
  let prepare : Program (Move r Q I J) E L (L ⊕ Endpoint r false) :=
    .route (Sum.elim id Sigma.fst) (Sum.elim (fun _ => .idle) Move.prepare)
  let align : Program (Move r Q I J) E (L ⊕ Endpoint r false) (L ⊕ (Q × Endpoint r false)) :=
    .route (Sum.map id Prod.snd) (Sum.elim (fun _ => .idle) (fun (j,e) => .align j e))
  (prepare.seq align).seq (.table (partialTable r))

/-- Only singleton and incident terms of selected rows enter the common layout. -/
def mix (M : Matrix H H K) : Program (Move r Q I J) E (L ⊕ (Q × B))
    ((L ⊕ (Q × B)) ⊕ (Q × H)) :=
  let gather : Program (Move r Q I J) E (L ⊕ (Q × B))
        ((L ⊕ (Q × B)) ⊕ (Q × RankTerm r true I)) :=
    .route (Sum.elim id (fun (j,t) => gatherFrom r I j t))
      (Sum.elim (fun _ => .idle) (fun (j,t) => .gather j t))
  gather.seq (.table (mixTable r I M))

/-- Only singleton and incident terms of selected columns leave the common layout. -/
def scatter : Program (Move r Q I J) E ((L ⊕ (Q × B)) ⊕ (Q × H))
    ((L ⊕ (Q × L)) ⊕ (Q × B)) :=
  let distribute : Program (Move r Q I J) E ((L ⊕ (Q × B)) ⊕ (Q × H))
        ((L ⊕ (Q × B)) ⊕ (Q × RankTerm r false J)) :=
    .route (Sum.map id (fun (j,t) => (j,t.1)))
      (Sum.elim (fun _ => .idle) (fun (j,t) => .distribute j t))
  distribute.seq (.table (scatterTable r J))

/-- Undo query alignment, apply the row matrices and sum the queries before undoing
the reserved-coordinate placement. -/
def collect (A₀ : E →+ E) (A : Q → E →+ E) : Program (Move r Q I J) E
    ((L ⊕ (Q × L)) ⊕ (Q × B)) L :=
  let unalign : Program (Move r Q I J) E ((L ⊕ (Q × L)) ⊕ (Q × B))
        ((L ⊕ (Q × L)) ⊕ (Q × Endpoint r true)) :=
    .route (Sum.map id (fun (j,e) => (j,e.2.1)))
      (Sum.elim (fun _ => .idle) (fun (j,e) => .unalign j e))
  let restore : Program (Move r Q I J) E (L ⊕ Endpoint r true) (L ⊕ Endpoint r true) :=
    .route id (Sum.elim (fun _ => .idle) Move.restore)
  ((unalign.seq (.table (sumQueries r A₀ A))).seq restore).seq (.table (finishTable r))

/-- Literal grouped bank script for the sum-of-swaps stage. -/
def stage (M : Matrix H H K) (A₀ : E →+ E) (A : Q → E →+ E) :
    Program (Move r Q I J) E L L :=
  (((partials r I J).seq (mix r I J M)).seq (scatter r I J)).seq (collect r I J A₀ A)

/-- Only the rank-sized conversions repeat for each query. Price zero means
an instruction makes no recursive interchange calls. -/
def price (prepare : Endpoint r false → ℕ) (restore : Endpoint r true → ℕ)
    (gather : Q × RankTerm r true I → ℕ) (distribute : Q × RankTerm r false J → ℕ) :
    Move r Q I J → ℕ
  | .idle | .align .. | .unalign .. => 0
  | .prepare e => prepare e
  | .restore e => restore e
  | .gather j t => gather (j,t)
  | .distribute j t => distribute (j,t)

theorem stage_cost (M : Matrix H H K) (A₀ : E →+ E) (A : Q → E →+ E)
    (pre : Endpoint r false → ℕ) (post : Endpoint r true → ℕ)
    (gather : Q × RankTerm r true I → ℕ) (distribute : Q × RankTerm r false J → ℕ) :
    cost (price r I J pre post gather distribute) (stage r I J M A₀ A) =
      ((∑ e, pre e) + ∑ e, post e) + ((∑ t, gather t) + ∑ t, distribute t) := by
  classical
  simp [stage, partials, mix, scatter, collect, Fintype.sum_sum_type, price]
  omega

/-- Scalar sums represented by a rectangle and a rank row at a fixed common address. -/
def partialValue (x : L → E) (b : B) : E := ∑ v ∈ (r b).sources, x v

def mixedValue (M : Matrix H H K) (x : L → E) : H → E :=
  applyRows M fun i => x (I i) + ∑ b : Incident r true (I i), partialValue r x b

def singletonValue (y : H → E) (w : L) : E := ∑ i, if w = J i then y i else 0

def rectangleValue (x : L → E) (y : H → E) (b : B) : E :=
  (∑ i, if J i ∈ (r b).sources then y i else 0) - partialValue r x b

omit [Fintype L] in
private theorem incident_sum (w : L) (z : B → E) :
    ∑ b : Incident r true w, z b = ∑ b, if w ∈ (r b).destinations then z b else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) z).symm

theorem corrected_value (M : Matrix H H K)
    (hM : (rectangleMatrix (K := K) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (x : L → E) (w : L) :
    let y := mixedValue r I M x
    singletonValue J y w + ∑ b : Incident r true w, rectangleValue r J x y b = x w := by
  classical
  let P := rectangleMatrix (K := K) r
  let y := mixedValue r I M x
  have hy : y = applyRows M (applyRows (P.submatrix I id) x) := by
    apply congrArg (applyRows M)
    funext i
    rw [incident_sum r (I i) (partialValue r x)]
    exact (rectangleMatrix_apply (K := K) r x (I i)).symm
  have hs := selected_applyRows (K := K) r id J y w
  simp only [id_eq] at hs
  have hz : applyRows (P.submatrix id J) y w = x w + rectangleSum r x w := by
    rw [hy, ← applyRows_mul, ← applyRows_mul, hM]
    exact rectangleMatrix_apply r x w
  change singletonValue J y w + ∑ b : Incident r true w, rectangleValue r J x y b = x w
  simp only [rectangleValue, Finset.sum_sub_distrib]
  rw [← add_sub_assoc, incident_sum r w (partialValue r x),
    incident_sum r w (fun b => ∑ i, if J i ∈ (r b).sources then y i else 0)]
  change (singletonValue J y w + _) - rectangleSum r x w = x w
  unfold singletonValue
  rw [← hs, hz, add_sub_cancel_right]

variable {r : B → Rectangle L} (g : Layout r Q Addr) (X : L → Addr → E)

/-- Input rows at a fixed common address. -/
def aligned (j : Q) (z : Addr) (v : L) : E := X v ((g.S j v).symm z)

/-- Rectangle sums keep their own address layout. -/
def partialBank : (L ⊕ (Q × B)) → Addr → E
  | .inl v, a => X v a
  | .inr (j,b), a => partialValue r (aligned g X j (g.C j b a)) b

def mixedBank (M : Matrix H H K) : ((L ⊕ (Q × B)) ⊕ (Q × H)) → Addr → E
  | .inl u, a => partialBank g X u a
  | .inr (j,i), a => mixedValue r I M (aligned g X j a) i

def scatterBank (M : Matrix H H K) : ((L ⊕ (Q × L)) ⊕ (Q × B)) → Addr → E
  | .inl (.inl v), a => X v a
  | .inl (.inr (j,w)), a =>
      singletonValue J (mixedValue r I M (aligned g X j (g.T j w a))) w
  | .inr (j,b), a =>
      let x := aligned g X j (g.C j b a)
      rectangleValue r J x (mixedValue r I M x) b

omit [Fintype H] in
theorem eval_partials : eval g.perm (partials r I J) X = partialBank g X := by
  funext u a
  cases u with
  | inl => rfl
  | inr t =>
    rcases t with ⟨j,b⟩
    change (∑ v : (r b).sources,
      X v ((g.prepareSrc ⟨v.1,b,v.2⟩).symm ((g.localSrc j ⟨v.1,b,v.2⟩).symm a))) = _
    simp_rw [g.source_at]
    exact Finset.sum_coe_sort (r b).sources (aligned g X j (g.C j b a))

theorem eval_mix (M : Matrix H H K) :
    eval g.perm (mix r I J M) (partialBank g X) = mixedBank I g X M := by
  funext u a
  cases u with
  | inl => rfl
  | inr t =>
    rcases t with ⟨j,i⟩
    apply congrArg (fun z => applyRows M z i)
    funext k
    change X (I k) ((g.S j (I k)).symm a) +
      (∑ b : Incident r true (I k),
        partialValue r (aligned g X j (g.C j b ((g.C j b).symm a))) b) = _
    simp only [Equiv.apply_symm_apply]
    rfl

theorem eval_scatter (M : Matrix H H K) :
    eval g.perm (scatter r I J) (mixedBank I g X M) = scatterBank I J g X M := by
  funext u a
  rcases u with (w | ⟨j,b⟩)
  · rcases w with (w | ⟨j,w⟩)
    · rfl
    · change (∑ i, if w = J i then mixedValue r I M (aligned g X j (g.T j (J i) a)) i
          else 0) = ∑ i, if w = J i then mixedValue r I M (aligned g X j (g.T j w a)) i else 0
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · rw [hi]
      · rfl
  · rfl

/-- Running the finite bank script computes the full sum of swaps on every input
row and address. Only the equality between the selected submatrix product and the
label matrix is needed, allowing the nonsingular minor to be chosen once per stage. -/
theorem eval_stage (M : Matrix H H K)
    (hM : (rectangleMatrix (K := K) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (A₀ : E →+ E) (A : Q → E →+ E) (w : L) (a : Addr) :
    eval g.perm (stage r I J M A₀ A) X w a =
      A₀ (X w a) + ∑ j, A j (X w ((g.S j w).symm (g.T j w a))) := by
  simp only [stage, eval_seq, eval_partials, eval_mix, eval_scatter]
  let x j := aligned g X j (g.T j w a)
  let y j := mixedValue r I M (x j)
  change A₀ (X w a) + (∑ j, A j (singletonValue J (y j) w)) +
    (∑ b : Incident r true w, ∑ j, A j (scatterBank I J g X M (.inr (j,b.1))
      (g.localDst j ⟨w,b⟩ (g.prepareDst ⟨w,b⟩ a)))) = _
  have hd (b : Incident r true w) (j : Q) :
      scatterBank I J g X M (.inr (j,b.1)) (g.localDst j ⟨w,b⟩ (g.prepareDst ⟨w,b⟩ a)) =
        rectangleValue r J (x j) (y j) b := by
    simp only [scatterBank, g.dest_at j ⟨w,b⟩]
    rfl
  simp_rw [hd]
  rw [add_assoc, Finset.sum_comm (s := Finset.univ (α := Incident r true w)), ← Finset.sum_add_distrib]
  apply congrArg (A₀ (X w a) + ·)
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_sum, ← map_add]
  exact congrArg (A j) (corrected_value r I J M hM (x j) w)

/-- A single nonsingular minor supplies the finite scripts for all row matrices
and address layouts. If each native source/destination pair induces the query
swap, the script acts independently on every label by the prescribed pencil. -/
theorem exists_pencil (r : B → Rectangle L) :
    let P := rectangleMatrix (K := K) r
    ∃ I J : Fin P.rank → L, Function.Injective I ∧ Function.Injective J ∧
      IsUnit (P.submatrix I J) ∧
      ∀ (g : Layout r Q Addr) (swap : Q → Equiv.Perm Addr),
        (∀ j w a, (g.S j w).symm (g.T j w a) = swap j a) →
        ∀ (A₀ : E →+ E) (A : Q → E →+ E) (X : L → Addr → E) (w : L) (a : Addr),
          eval g.perm (stage r I J (P.submatrix I J)⁻¹ A₀ A) X w a =
            A₀ (X w a) + ∑ j, A j (X w (swap j a)) := by
  let P := rectangleMatrix (K := K) r
  obtain ⟨I, J, hi, hj, hunit, hM⟩ := exists_skeleton P
  refine ⟨I, J, hi, hj, hunit, ?_⟩
  intro g swap hswap A₀ A X w a
  exact (eval_stage I J g X _ hM A₀ A w a).trans (by simp only [hswap])

end Interchange.StageRoute

end NearSquareRoot
end Computability
end OAI
