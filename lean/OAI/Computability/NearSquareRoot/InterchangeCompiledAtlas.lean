import OAI.Computability.NearSquareRoot.InterchangeSupportDomain
import OAI.Computability.NearSquareRoot.InterchangeStageWords

/-!
# Simultaneous physical specialization of a rectangle atlas

The catalog includes both labels at every query, including labels absent from
the chosen rank minor. Commutativity of the rational endpoint diagrams thus
survives a single common specialization. Forward and backward directions use
the same stored finite instruction lists.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.RectangleAtlas

open IntegerMultiplication.Port StageLedger StageRoute InterchangeStageLift Support

variable {L B H : Type} {r : B → Rectangle L} {a m b : ℕ}

abbrev Chart (r : B → Rectangle L) (m : ℕ) :=
  (Bool × Fin m × L) ⊕ (Fin m × B) ⊕ ((s : Bool) × Endpoint r s) ⊕
    (Fin m × ((s : Bool) × Endpoint r s))

namespace Chart

def label (s : Bool) (j : Fin m) (v : L) : Chart r m := .inl (s,j,v)
def common (j : Fin m) (t : B) : Chart r m := .inr (.inl (j,t))
def prepare {s : Bool} (u : Endpoint r s) : Chart r m := .inr (.inr (.inl ⟨s,u⟩))
def localMap {s : Bool} (j : Fin m) (u : Endpoint r s) : Chart r m := .inr (.inr (.inr (j,⟨s,u⟩)))

noncomputable def word (A : RectangleAtlas r a) : Chart r m → Support.Word (Fin (a+m+a)) Fin.val
  | .inl (s,j,v) => A.labelWord s j v
  | .inr (.inl (j,t)) => A.commonWord j t
  | .inr (.inr (.inl ⟨_,u⟩)) => A.prepareWord m u
  | .inr (.inr (.inr (j,⟨_,u⟩))) => A.localWord j u

end Chart

structure Frame (A : RectangleAtlas r a) (m b : ℕ) where
  chart : (c : Chart r m) → (f : ℕ) →
    Duplex (Fin (a+m+a)) (Tower b f) ≃ₗ[Tower b f] Duplex (Fin (a+m+a)) (Tower b f)
  token : ∀ c f, AddressToken (coordinateAddress (Chart.word A c).address) (coordinateAddress (chart c f))
  runs : ∀ c, Runs Fin.val (Chart.word A c).price (chart c)

/-- One prime and instruction catalog for the entire atlas, independently of
the recursive width or a subsequent selection of rank rows and columns. -/
theorem compile_frame [DecidableEq L] [Fintype L] [Fintype B] (A : RectangleAtlas r a)
    (m W : ℕ) (extra : Finset ℚ) :
    ∃ b, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ q ∈ extra, (code q = none ↔ q = 0) ∧ ∀ f, Token q ((code q).stamp f)) ∧
      Nonempty (Frame A m b) := by
  classical
  obtain ⟨b,hb,hW,code,hcode,h⟩ := compile_words (Chart.word A (m := m)) Fin.val_injective W extra
  choose E ht hr using h
  exact ⟨b,hb,hW,code,hcode,⟨⟨E,ht,hr⟩⟩⟩

namespace Frame

variable {A : RectangleAtlas r a} (g : Frame A m b)

private theorem triangle (s : Bool) (j : Fin m) (u : Endpoint r s) (f : ℕ) :
    (g.chart (Chart.prepare u) f).trans ((g.chart (Chart.localMap j u) f).trans
      (g.chart (Chart.common j u.2) f)) = g.chart (Chart.label s j u.1) f := by
  apply coordinateAddress_injective
  have eqR : (Chart.word A (Chart.prepare (m:=m) u)).address.trans
      ((Chart.word A (Chart.localMap j u)).address.trans (Chart.word A (Chart.common j u.2)).address) =
      (Chart.word A (Chart.label s j u.1)).address := by
    apply LinearEquiv.toEquiv_injective
    change ((A.prepareWord m u).address.toEquiv).trans
      (((A.localWord j u).address.toEquiv).trans (A.commonWord j u.2).address.toEquiv) =
        (A.labelWord s j u.1).address.toEquiv
    simpa only [prepareWord_address,localWord_address,commonWord_address] using
      (A.physical_triangle j u).trans (A.labelWord_address s j u.1).symm
  have h := (g.token (Chart.prepare u) f).trans ((g.token (Chart.localMap j u) f).trans (g.token (Chart.common j u.2) f))
  simp only [coordinateAddress_trans,eqR] at h
  exact h.unique (g.token _ f)

/-- The atlas as actual permutations of the full prime-power field arrays. -/
noncomputable def layout (f : ℕ) : Layout r (Fin m) (Duplex (Fin (a+m+a)) (Tower b f)) where
  S j v := (g.chart (Chart.label false j v) f).toEquiv
  T j v := (g.chart (Chart.label true j v) f).toEquiv
  C j t := (g.chart (Chart.common j t) f).toEquiv
  prepareSrc u := (g.chart (Chart.prepare u) f).toEquiv
  prepareDst u := (g.chart (Chart.prepare u) f).toEquiv
  localSrc j u := (g.chart (Chart.localMap j u) f).toEquiv
  localDst j u := (g.chart (Chart.localMap j u) f).toEquiv
  source_triangle j u := congrArg LinearEquiv.toEquiv (g.triangle false j u f)
  target_triangle j u := congrArg LinearEquiv.toEquiv (g.triangle true j u f)

theorem runs_move {I J : H → L} (v : Move r (Fin m) I J) :
    ∃ ops : List (Lag (Fin (a+m+a)) b), (∀ op ∈ ops, op.legal Fin.val) ∧
      (ops.map Lag.prices).sum ≤ (A.routeWord v).price ∧
      ∀ f x, ops.foldl (Lag.fire f) x = (g.layout f).perm v x := by
  cases v with
  | idle => exact ⟨[],by simp,by simp,fun _ _ => rfl⟩
  | prepare u => exact g.runs (Chart.prepare u)
  | restore u => exact (g.runs (Chart.prepare u)).symm
  | align j u => exact g.runs (Chart.localMap j u)
  | unalign j u => exact (g.runs (Chart.localMap j u)).symm
  | gather j t =>
    rcases t with ⟨k,_ | t⟩
    · exact g.runs (Chart.label false j (I k))
    · exact g.runs (Chart.common j t)
  | distribute j t =>
    rcases t with ⟨k,_ | t⟩
    · exact (g.runs (Chart.label true j (J k))).symm
    · exact (g.runs (Chart.common j t)).symm

/-- Specializing the atlas preserves the exact one-pair pivot at every
diagonal label, including all unselected reserve and main fields. -/
theorem layout_diagonal (j : Fin m) (v : L) (f : ℕ) :
    ((g.layout f).S j v).trans ((g.layout f).T j v).symm =
      perm (querySlots a j) (querySwap a (Tower b f)) := by
  let F := (A.labelWord false j v).address.trans (A.labelWord true j v).address.symm
  let G := (g.chart (Chart.label false j v) f).trans (g.chart (Chart.label true j v) f).symm
  apply specialize_mainSwap a j F G
  · exact A.physical_diagonal j v
  · simpa only [coordinateAddress_trans,coordinateAddress_symm,F,G,Chart.word,Chart.label] using
      (g.token (Chart.label false j v) f).trans (g.token (Chart.label true j v) f).symm

open IntegerMultiplication.Loom IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic NearSquareRoot.InterchangeSlots

/-- The actual recreation of every stage move agrees with the same modular
layout for arbitrary prefix, gap and suffix tapes. -/
theorem native_move [NeZero b] {I J : H → L} (v : Move r (Fin m) I J) :
    let ord := Equiv.refl (Fin (a+m+a))
    ∃ (ops : List (Lag (Fin (a+m+a)) b)) (legal : ∀ op ∈ ops, op.legal (ranking ord)),
      (ops.map Lag.prices).sum ≤ (A.routeWord v).price ∧
      ∀ (P G B : Tape) (f : ℕ), recreation ord P G B f ops legal =
        (extendLayout P G B (g.layout f)).perm v := by
  obtain ⟨ops,hlegal,hprice,heff⟩ := g.runs_move v
  refine ⟨ops,hlegal,hprice,fun P G B f => ?_⟩
  apply Equiv.ext
  intro x
  apply square.injective
  rw [extendLayout_perm,square_extendDomain]
  exact (fore (Equiv.refl _) ops hlegal x).trans (congrArg (fun y => (y,watcher x)) (heff f (chase x)))

theorem native_diagonal [NeZero b] (j : Fin m) (v : L) (P G B : Tape) (f : ℕ) :
    let A := extendLayout P G B (g.layout f)
    let op : Lag (Fin (a+m+a)) b := .pivot (mainRank a j) (mainRank a j)
    (A.S j v).trans (A.T j v).symm =
      recreation (Equiv.refl _) P G B f [op] (by simp [op,Lag.legal]) := by
  dsimp only
  rw [extendLayout_diagonal _ _ _ _ _ _ (g.layout_diagonal j v f)]
  apply Equiv.ext
  intro x
  apply square.injective
  rw [square_extendDomain]
  exact (congrArg (fun v => (v,watcher x)) (update_querySwap f a j (chase x))).trans
    (fore (Equiv.refl _) [.pivot (mainRank a j) (mainRank a j)] (by simp [Lag.legal]) x).symm

end Frame

end Interchange.RectangleAtlas

end NearSquareRoot
end Computability
end OAI
