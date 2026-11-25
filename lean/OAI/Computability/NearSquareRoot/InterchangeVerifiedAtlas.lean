import OAI.Computability.NearSquareRoot.InterchangeAtlasVerifier

/-! # Native rectangle layouts and routing programs read from a passing certificate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.AddressROM

open IntegerMultiplication.Port StageLedger StageRoute RectangleAtlas Support InterchangeSlots InterchangeStageLift

variable {L B H : Type} [DecidableEq L] [Fintype L] [Fintype B]
  {r : B → Rectangle L} {a m b : ℕ} (w : Catalog r a m b) (hb : 1 < b) (hw : valid w = true)

include hb hw in
private theorem legal_at (c : Chart r m) : ∀ op ∈ w c, op.legal Fin.val :=
  ((valid_iff hb w).mp hw).1 c |>.1

private noncomputable def chartEquiv (c : Chart r m) (f : ℕ) :
    Equiv.Perm (Duplex (Fin (a+m+a)) (Tower b f)) := by
  letI : NeZero b := ⟨by omega⟩
  let g := run w c f
  have left : Function.LeftInverse
      (fun x => ((w c).reverse.map Lag.rewind).foldl (Lag.fire f) x) g :=
    fun x => Lag.backlist f x (w c) Fin.val (legal_at w hb hw c)
  exact Equiv.ofBijective g (Finite.injective_iff_bijective.mp left.injective)

noncomputable def layout (f : ℕ) : Layout r (Fin m) (Duplex (Fin (a+m+a)) (Tower b f)) where
  S j v := chartEquiv w hb hw (Chart.label false j v) f
  T j v := chartEquiv w hb hw (Chart.label true j v) f
  C j t := chartEquiv w hb hw (Chart.common j t) f
  prepareSrc u := chartEquiv w hb hw (Chart.prepare u) f
  prepareDst u := chartEquiv w hb hw (Chart.prepare u) f
  localSrc j u := chartEquiv w hb hw (Chart.localMap j u) f
  localDst j u := chartEquiv w hb hw (Chart.localMap j u) f
  source_triangle j u := Equiv.ext (((valid_iff hb w).mp hw).2.1 false j u f)
  target_triangle j u := Equiv.ext (((valid_iff hb w).mp hw).2.1 true j u f)

theorem diagonal (j : Fin m) (v : L) (f : ℕ) :
    ((layout w hb hw f).S j v).trans ((layout w hb hw f).T j v).symm =
      perm (querySlots a j) (querySwap a (Tower b f)) := by
  apply Equiv.ext
  intro x
  apply ((layout w hb hw f).T j v).injective
  change ((layout w hb hw f).T j v) (((layout w hb hw f).T j v).symm (((layout w hb hw f).S j v) x)) = _
  rw [Equiv.apply_symm_apply]
  change run w (Chart.label false j v) f x = run w (Chart.label true j v) f (update _ _ x)
  rw [update_querySwap]
  exact (((valid_iff hb w).mp hw).2.2 j v f x).symm

def reverseList (l : List (Lag (Fin (a+m+a)) b)) := l.reverse.map Lag.rewind

/-- No semantic choice enters the list supplied to the address interpreter. -/
def instructions {I J : H → L} : Move r (Fin m) I J → List (Lag (Fin (a+m+a)) b)
  | .idle => []
  | .prepare u => w (Chart.prepare u)
  | .restore u => reverseList (w (Chart.prepare u))
  | .align j u => w (Chart.localMap j u)
  | .unalign j u => reverseList (w (Chart.localMap j u))
  | .gather j ⟨i,none⟩ => w (Chart.label false j (I i))
  | .gather j ⟨_,some t⟩ => w (Chart.common j t.1)
  | .distribute j ⟨i,none⟩ => reverseList (w (Chart.label true j (J i)))
  | .distribute j ⟨_,some t⟩ => reverseList (w (Chart.common j t.1))

private theorem reverse_act (c : Chart r m) (f : ℕ) (x : Duplex (Fin (a+m+a)) (Tower b f)) :
    (reverseList (w c)).foldl (Lag.fire f) x = (chartEquiv w hb hw c f).symm x := by
  have h := Lag.backlist f ((chartEquiv w hb hw c f).symm x) (w c) Fin.val (legal_at w hb hw c)
  change (reverseList (w c)).foldl (Lag.fire f) (chartEquiv w hb hw c f ((chartEquiv w hb hw c f).symm x)) = _ at h
  simpa using h

theorem instructions_act {I J : H → L} (v : Move r (Fin m) I J) (f : ℕ)
    (x : Duplex (Fin (a+m+a)) (Tower b f)) :
    (instructions w v).foldl (Lag.fire f) x = (layout w hb hw f).perm v x := by
  cases v with
  | idle | prepare | align => rfl
  | restore | unalign => exact reverse_act w hb hw _ f x
  | gather j t => rcases t with ⟨i,_ | d⟩ <;> rfl
  | distribute j t => rcases t with ⟨i,_ | d⟩ <;> exact reverse_act w hb hw _ f x

include hb hw in
private theorem reverse_legal (c : Chart r m) : ∀ v ∈ reverseList (w c), v.legal Fin.val := by
  intro v hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  exact Lag.rewind_legal _ u (legal_at w hb hw c u (List.mem_reverse.mp hu))

private theorem reverse_cost (z : List (Lag (Fin (a+m+a)) b)) :
    ((reverseList z).map Lag.prices).sum = (z.map Lag.prices).sum := by
  have eq : Lag.prices ∘ (Lag.rewind (J:=Fin (a+m+a)) (p:=b)) = Lag.prices := by
    funext op; cases op <;> rfl
  simp only [reverseList,List.map_map,eq,List.map_reverse,List.sum_reverse]

include hb hw in
theorem instructions_legal {I J : H → L} (v : Move r (Fin m) I J) :
    ∀ op ∈ instructions w v, op.legal Fin.val := by
  cases v with
  | idle => simp [instructions]
  | prepare | align => exact legal_at w hb hw _
  | restore | unalign => exact reverse_legal w hb hw _
  | gather j t => rcases t with ⟨i,_ | d⟩ <;> exact legal_at w hb hw _
  | distribute j t => rcases t with ⟨i,_ | d⟩ <;> exact reverse_legal w hb hw _

def cap {I J : H → L} (a : ℕ) : Move r (Fin m) I J → ℕ
  | .idle | .align .. | .unalign .. => 0
  | _ => 54*(a+2)

include hb hw in
theorem instructions_cost {I J : H → L} (v : Move r (Fin m) I J) :
    ((instructions w v).map Lag.prices).sum ≤ cap a v := by
  have cost (c : Chart r m) := (((valid_iff hb w).mp hw).1 c).2
  cases v with
  | idle => exact Nat.zero_le _
  | prepare u => exact cost (Chart.prepare u)
  | align j u => exact cost (Chart.localMap j u)
  | restore u => simpa only [instructions,reverse_cost,cap,affordable,Chart.prepare,Chart.localMap,Chart.common,Chart.label] using cost (Chart.prepare u)
  | unalign j u => simpa only [instructions,reverse_cost,cap,affordable,Chart.prepare,Chart.localMap,Chart.common,Chart.label] using cost (Chart.localMap j u)
  | gather j t =>
    rcases t with ⟨i,_ | d⟩
    · exact cost (Chart.label false j (I i))
    · exact cost (Chart.common j d.1)
  | distribute j t =>
    rcases t with ⟨i,_ | d⟩
    · simpa only [instructions,reverse_cost,cap,affordable,Chart.prepare,Chart.localMap,Chart.common,Chart.label] using cost (Chart.label true j (J i))
    · simpa only [instructions,reverse_cost,cap,affordable,Chart.prepare,Chart.localMap,Chart.common,Chart.label] using cost (Chart.common j d.1)

open IntegerMultiplication.Loom IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic

theorem native_move [NeZero b] {I J : H → L} (v : Move r (Fin m) I J)
    (P G B : Tape) (f : ℕ) :
    let ord := Equiv.refl (Fin (a+m+a))
    recreation ord P G B f (instructions w v) (instructions_legal w hb hw v) =
      (extendLayout P G B (layout w hb hw f)).perm v := by
  intro ord
  apply Equiv.ext
  intro x
  apply square.injective
  rw [extendLayout_perm,square_extendDomain]
  exact (fore ord (instructions w v) (instructions_legal w hb hw v) x).trans
    (congrArg (fun y => (y,watcher x)) (instructions_act w hb hw v f (chase x)))

theorem native_diagonal [NeZero b] (j : Fin m) (v : L) (P G B : Tape) (f : ℕ) :
    let native := extendLayout P G B (layout w hb hw f)
    let op : Lag (Fin (a+m+a)) b := .pivot (mainRank a j) (mainRank a j)
    (native.S j v).trans (native.T j v).symm =
      recreation (Equiv.refl _) P G B f [op] (by simp [op,Lag.legal]) := by
  dsimp only
  rw [extendLayout_diagonal _ _ _ _ _ _ (diagonal w hb hw j v f)]
  apply Equiv.ext
  intro x
  apply square.injective
  rw [square_extendDomain]
  exact (congrArg (fun z => (z,watcher x)) (update_querySwap f a j (chase x))).trans
    (fore (Equiv.refl _) [.pivot (mainRank a j) (mainRank a j)] (by simp [Lag.legal]) x).symm

end Interchange.AddressROM

end NearSquareRoot
end Computability
end OAI
