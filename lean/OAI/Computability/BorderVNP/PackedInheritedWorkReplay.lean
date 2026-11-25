import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedHistoryCorrect

/-! # Propagating the installed private programs along the actual encoded tree

The induction follows the canonical histogram guess for each node. The
child program arrays are those of the true geometric replay, including
the change of external port indexing at a parallel boundary. The output
is the evaluated Boolean circuit on that guess.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Diagonal.ExternalSew Diagonal.CellEntries
open Epoch.Round VPVNP.VerifierNetwork
open scoped Classical
attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K I P : Type} [Field K] [Fintype I] [Fintype P] {bits : P → ℕ}
variable {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ} {e : PaidIdentity K D m}
variable {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
variable (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)
variable {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
variable (codec : Codec F.system G) (step : Steps k b W G)

/-- A property of both the physical output words and the complete private
program family installed at this particular state. -/
abbrev PrivateOutput (view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n))
    (W : ℕ → Type) := ∀ n (a : A n), Site.Programs (view n a).pack.layout → (W n → Bool) → Prop

variable (read : PrivateOutput view W)

/-- Restrict the installed initial bank to one child of the current parallel
leaf collection, keeping the exact width transport used by the private replay. -/
noncomputable def privateChild {n : ℕ} (a : Leaves k (A 0) (n+1))
    (initial : Site.Programs (parallelLeaves (fun t => (view 0 t).pack) (n+1) a).layout) (j : Fin k) :
    Site.Programs (parallelLeaves (fun t => (view 0 t).pack) n (a j)).layout :=
  let children := fun i : Fin k => (parallelLeaves (fun t => (view 0 t).pack) n (a i)).layout
  fun v => (initial ⟨j,v⟩).castWidth ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq children j v))

variable {σ : Type} [Fintype σ] (x : σ → Bool)

/-- Leaf widths are supplied by the actual initial-bank circuits. -/
def PrivateLeaves : (n : ℕ) → (a : Leaves k (A 0) n) →
    Site.Programs (parallelLeaves (fun t => (view 0 t).pack) n a).layout →
    Leaves k (Frame σ (W 0)) n → Prop
  | 0, a, initial, f => read 0 a (fun v => (initial v).castWidth (incoming_instances _ _)) (f.eval x)
  | n+1, a, initial, fs => ∀ j, PrivateLeaves n (a j) (privateChild a initial j) (fs j)

/-- Apply the verified successor readback on each real node in order. Its
predecessor banks are exactly those of the recursively installed programs.
Every earlier rectangle is a shared subcircuit of the result. -/
theorem private_output
    (next : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
      (programs : ∀ j, Site.Programs (view i.val (c j)).pack.layout) (y : Fin k → W i.val → Bool),
      (∀ j, read i.val (c j) (programs j) (y j)) →
      read (i.val+1) (F.advance i c q) (F.savePrivatePrograms store rows number i c q programs)
        (fun z => (step i.val i.isLt).eval (Sum.elim (fun t => y t.1 t.2) (codec.word i.val i.isLt c q)) (.inl z)))
    (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun t => (view 0 t).pack) n a).layout)
    (fs : Leaves k (Frame σ (W 0)) n) (h : PrivateLeaves read x n a initial fs)
    (q : (F.system.histories n hn a).Index) :
    read n (RowTrace.state F.system n hn a q) (F.replayPrivatePrograms store rows number n hn a initial q)
      (output step n hn fs x (encode codec n hn a q)) := by
  induction n with
  | zero =>
    rw [show output step 0 hn fs x (encode codec 0 hn a q) = fs.eval x from output_zero step fs x _]
    exact h
  | succ n ih =>
    let i : Fin b := ⟨n,Nat.lt_of_succ_le hn⟩
    let c (j : Fin k) := RowTrace.state F.system n i.isLt.le (a j) (q.1 j)
    let old (j : Fin k) := F.replayPrivatePrograms store rows number n i.isLt.le (a j)
      (privateChild a initial j) (q.1 j)
    let y (j : Fin k) := output step n i.isLt.le (fs j) x (encode codec n i.isLt.le (a j) (q.1 j))
    have ok (j : Fin k) : read n (c j) (old j) (y j) := ih i.isLt.le (a j) _ (fs j) (h j) (q.1 j)
    have hout : output step (n+1) hn fs x (encode codec (n+1) hn a q) =
        fun z => (step n i.isLt).eval (Sum.elim (fun t => y t.1 t.2) (codec.word n i.isLt c q.2)) (.inl z) :=
      funext (output_succ step n hn fs x (encode codec (n+1) hn a q))
    rw [hout]
    exact next i c q.2 old y ok

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
