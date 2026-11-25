import OAI.Computability.NearSquareRoot.InterchangeRomEquality

/-!
# Verifying an atlas from its finite native instruction lists

The tests compare the two endpoint triangles and the diagonal pivot on rational
coordinate vectors. Thus they inspect a bounded number of entries even though
the same lists will be run at unbounded field widths.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.AddressROM

open IntegerMultiplication.Port StageLedger RectangleAtlas InterchangeSlots InterchangeStageLift

variable {L B : Type} {r : B → Rectangle L} {a m b : ℕ}

abbrev Catalog (r : B → Rectangle L) (a m b : ℕ) :=
  Chart r m → List (Lag (Fin (a+m+a)) b)

def affordable (a : ℕ) : Chart r m → ℕ
  | .inr (.inr (.inr _)) => 0
  | _ => 54*(a+2)

private def lawful (op : Lag (Fin (a+m+a)) b) : Bool :=
  match op with
  | .gather q t _ => decide ((t.1 = false ∧ q.1 = true) ∨ (t.1 = q.1 ∧ t.2.val < q.2.val))
  | _ => true

private theorem lawful_iff (op : Lag (Fin (a+m+a)) b) : lawful op = true ↔ op.legal Fin.val := by
  cases op <;> simp [lawful,Lag.legal,Lag.early]

def shapeOK (words : Catalog r a m b) (c : Chart r m) : Bool :=
  (words c).all lawful && decide (((words c).map Lag.prices).sum ≤ affordable a c)

def edgeOK (words : Catalog r a m b) (s : Bool) (j : Fin m) (u : Endpoint r s) : Bool :=
  equal (words (Chart.prepare u) ++ words (Chart.localMap j u) ++ words (Chart.common j u.2))
    (words (Chart.label s j u.1))

def pivotOK (words : Catalog r a m b) (j : Fin m) (v : L) : Bool :=
  equal ((Lag.pivot (mainRank a j) (mainRank a j)) :: words (Chart.label true j v))
    (words (Chart.label false j v))

/-- One total Boolean test on finite chart data. -/
def valid [DecidableEq L] [Fintype L] [Fintype B] (words : Catalog r a m b) : Bool :=
  decide ((∀ c, shapeOK words c = true) ∧ (∀ s j u, edgeOK words s j u = true) ∧
    ∀ j v, pivotOK words j v = true)

def run (words : Catalog r a m b) (c : Chart r m) (f : ℕ)
    (x : Duplex (Fin (a+m+a)) (Tower b f)) := (words c).foldl (Lag.fire f) x

/-- The verified conditions in precisely the form used by the native predictor. -/
theorem valid_iff [DecidableEq L] [Fintype L] [Fintype B] (hb : 1 < b) (w : Catalog r a m b) :
    valid w = true ↔
      (∀ c, (∀ op ∈ w c, op.legal Fin.val) ∧ ((w c).map Lag.prices).sum ≤ affordable a c) ∧
      (∀ s j (u : Endpoint r s) f x,
        run w (Chart.common j u.2) f (run w (Chart.localMap j u) f (run w (Chart.prepare u) f x)) =
          run w (Chart.label s j u.1) f x) ∧
      (∀ j v f x, run w (Chart.label true j v) f (Lag.fire f x (.pivot (mainRank a j) (mainRank a j))) =
        run w (Chart.label false j v) f x) := by
  rw [valid, decide_eq_true_iff]
  simp only [decide_eq_true_iff,shapeOK,Bool.and_eq_true,List.all_eq_true,lawful_iff,
    edgeOK,pivotOK,equal_iff hb,List.foldl_append,List.foldl_cons,run]

private theorem price_ok (A : RectangleAtlas r a) (c : Chart r m) :
    (Chart.word A c).price ≤ affordable a c := by
  rcases c with ⟨s,j,v⟩ | ⟨j,t⟩ | ⟨s,u⟩ | ⟨j,s,u⟩
  · simp [Chart.word,affordable]
  · have := A.size t
    simp [Chart.word,affordable]; omega
  · have := A.size u.2
    simp [Chart.word,affordable]; omega
  · simp [Chart.word,affordable]

/-- Every frame furnished by the Hamming construction supplies a passing
finite certificate, retaining the exact chart maps at every recursive width. -/
theorem complete_with_prices [DecidableEq L] [Fintype L] [Fintype B] (hb : 1 < b)
    {A : RectangleAtlas r a} (g : Frame A m b) :
    ∃ w : Catalog r a m b, valid w = true ∧ (∀ c, ((w c).map Lag.prices).sum ≤ (Chart.word A c).price) ∧
      ∀ c f x, run w c f x = g.chart c f x := by
  choose w legal cost act using g.runs
  refine ⟨w, (valid_iff hb w).mpr ⟨fun c => ⟨legal c,(cost c).trans (price_ok A c)⟩,?_,?_⟩,cost,act⟩
  · intro s j u f x
    simp only [run,act]
    cases s
    · exact DFunLike.congr_fun ((g.layout f).source_triangle j u) x
    · exact DFunLike.congr_fun ((g.layout f).target_triangle j u) x
  · intro j v f x
    simp only [run,act]
    have h := DFunLike.congr_fun (g.layout_diagonal j v f) x
    change (g.chart (Chart.label true j v) f).symm (g.chart (Chart.label false j v) f x) =
      update _ _ x at h
    rw [update_querySwap] at h
    exact (congrArg (g.chart (Chart.label true j v) f) h.symm).trans
      ((g.chart (Chart.label true j v) f).apply_symm_apply _)

theorem complete [DecidableEq L] [Fintype L] [Fintype B] (hb : 1 < b)
    {A : RectangleAtlas r a} (g : Frame A m b) :
    ∃ w : Catalog r a m b, valid w = true ∧ ∀ c f x, run w c f x = g.chart c f x := by
  obtain ⟨w,hw,_,hr⟩ := complete_with_prices hb g
  exact ⟨w,hw,hr⟩

end Interchange.AddressROM

end NearSquareRoot
end Computability
end OAI
