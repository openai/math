import OAI.ThreeFlat.Diagonal.CompressorColoring
import Mathlib.Data.Finset.Card

namespace OAI
/-! # Deterministic descriptor scans on a base graph

The state is a table indexed by base vertex. One instruction reads the
previous table at the bounded set of neighbors, searches a fixed ordered
choice list, and replaces one entry. No vertex ordering or choice of a
fresh value is inferred from a field specialization.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Ordered
open Computability.VPVNP.Compression
variable {V A : Type*} {d n : ℕ}

/-- First candidate in the prescribed order outside the forbidden list. -/
def pick [DecidableEq A] (banned : List A) (fallback : A) : List A → A
  | [] => fallback
  | a :: tail => if a ∈ banned then pick banned fallback tail else a

theorem pick_fresh [DecidableEq A] (banned : List A) (fallback : A) (choices : List A)
    (existsGood : ∃ a ∈ choices, a ∉ banned) : pick banned fallback choices ∉ banned := by
  induction choices with
  | nil => obtain ⟨a,ha,_⟩ := existsGood; simp at ha
  | cons a rest ih =>
    by_cases h : a ∈ banned
    · rw [pick,ite_eq_left h]
      apply ih
      obtain ⟨b,hb,hg⟩ := existsGood
      exact ⟨b,(List.mem_cons.mp hb).resolve_left (fun eq => hg (eq.symm ▸ h)),hg⟩
    · simp [pick,h]

theorem contains_good [Fintype A] [DecidableEq A] (rank : Fin n ≃ A) (banned : List A)
    (small : banned.length < n) : ∃ a ∈ List.ofFn rank, a ∉ banned := by
  by_contra! none
  have full : banned.toFinset = Finset.univ := Finset.eq_univ_of_forall fun a => by
    obtain ⟨i, rfl⟩ := rank.surjective a
    exact List.mem_toFinset.mpr (none _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have h := banned.toFinset_card_le
  rw [full,Finset.card_univ,← Fintype.card_congr rank,Fintype.card_fin] at h
  omega

variable [DecidableEq V] [DecidableEq A]

/-- One table write per vertex, in the order given by `visits`. -/
def scan (visits : List V) (choices : List A) (fallback : A)
    (ban : V → (V → A) → List A) (initial : V → A) : V → A :=
  visits.foldl (fun table x => Function.update table x (pick (ban x table) fallback choices)) initial

variable (G : SlotGraph V d) (unary : V → A → Prop) (edge : V × Fin d → A → A → Prop)

private def Good (S : Finset V) (f : V → A) : Prop :=
  (∀ x ∈ S, unary x (f x)) ∧ ∀ e : V × Fin d, e.1 ∈ S → (G.target e).1 ∈ S →
    edge e (f e.1) (f (G.target e).1)

omit [DecidableEq A] in
private theorem good_update (S : Finset V) (f : V → A) (old : Good G unary edge S f)
    (x : V) (a : A) (hu : unary x a) (fw : ∀ i, edge (x,i) a (f (G.target (x,i)).1))
    (bw : ∀ i, edge (G.target.symm (x,i)) (f (G.target.symm (x,i)).1) a) :
    Good G unary edge (insert x S) (Function.update f x a) := by
  constructor
  · intro y hy
    by_cases eq : y = x
    · subst y; simpa using hu
    · simpa [Function.update_of_ne eq] using old.1 y ((Finset.mem_insert.mp hy).resolve_left eq)
  · intro e hs ht
    by_cases es : e.1 = x
    · have et : (G.target e).1 ≠ x := es ▸ G.ends_ne e
      obtain ⟨u,i⟩ := e
      change u = x at es
      subst u
      simpa [Function.update_of_ne et] using fw i
    · by_cases et : (G.target e).1 = x
      · have pair : (x,(G.target e).2) = G.target e := Prod.ext et.symm rfl
        have h := bw (G.target e).2
        rw [pair, Equiv.symm_apply_apply] at h
        simpa [Function.update_of_ne es,et] using h
      · simpa [Function.update_of_ne es,Function.update_of_ne et] using
          old.2 e ((Finset.mem_insert.mp hs).resolve_left es) ((Finset.mem_insert.mp ht).resolve_left et)

/-- A complete ordered scan enforces every local constraint. The initial
table may contain arbitrary public defaults. -/
theorem scan_valid [Fintype A] (visits : List V) (allVisited : ∀ x, x ∈ visits)
    (rank : Fin n ≃ A) (fallback : A) (ban : V → (V → A) → List A)
    (small : ∀ x f, (ban x f).length < n)
    (fresh : ∀ x f a, a ∉ ban x f → unary x a ∧
      (∀ i, edge (x,i) a (f (G.target (x,i)).1)) ∧
      ∀ i, edge (G.target.symm (x,i)) (f (G.target.symm (x,i)).1) a)
    (initial : V → A) :
    let f := scan visits (List.ofFn rank) fallback ban initial
    (∀ x, unary x (f x)) ∧ ∀ e, edge e (f e.1) (f (G.target e).1) := by
  have go (rest : List V) (S : Finset V) (f : V → A) (ok : Good G unary edge S f) :
      Good G unary edge (S ∪ rest.toFinset) (scan rest (List.ofFn rank) fallback ban f) := by
    induction rest generalizing S f with
    | nil => simpa [scan] using ok
    | cons x xs ih =>
      let a := pick (ban x f) fallback (List.ofFn rank)
      have chosen : a ∉ ban x f := pick_fresh _ _ _ (contains_good rank _ (small x f))
      obtain ⟨ua,fw,bw⟩ := fresh x f a chosen
      have setEq : S ∪ (x::xs).toFinset = (insert x S) ∪ xs.toFinset := by
        ext y
        simp only [Finset.mem_union,List.toFinset_cons,Finset.mem_insert]
        tauto
      rw [setEq]
      exact ih _ _ (good_update G unary edge S f ok x a ua fw bw)
  have ok := go visits ∅ initial (by simp [Good])
  exact ⟨fun x => ok.1 x (by simp [allVisited]),fun e => ok.2 e (by simp [allVisited]) (by simp [allVisited])⟩

end ThreeFlat.Diagonal.CompressorPacking.Ordered

end OAI
