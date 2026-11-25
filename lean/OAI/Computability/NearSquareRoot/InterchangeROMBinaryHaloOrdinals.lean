import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloTypes
import OAI.Computability.IntegerMultiplication.Strip.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Lexicographic addresses for padding the two interchangeable fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo

open BoxMaskedRecords

abbrev Addr (s : Shape) (w : ℕ) := Fin s.P × Fin w × Fin s.G × Fin w × Fin s.B

def rank (s : Shape) (w : ℕ) : Addr s w ≃ Fin (s.P*w*s.G*w*s.B) :=
  let join {p q r : ℕ} {X : Type} (f : X ≃ Fin r) : Fin p × (Fin q × X) ≃ Fin (p*(q*r)) :=
    ((Equiv.refl _).prodCongr (((Equiv.refl _).prodCongr f).trans finProdFinEquiv)).trans finProdFinEquiv
  (join (join (Equiv.refl (Fin s.B)))).trans (finCongr (by ac_rfl))

def digits {s : Shape} {w : ℕ} (x : Addr s w) : List ℕ :=
  [x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2]

theorem rank_val (s : Shape) (w : ℕ) (x : Addr s w) : (rank s w x).val =
    BoxRank.position [s.P,w,s.G,w,s.B] (digits x) := by
  simp [rank, digits, BoxRank.position, finProdFinEquiv, Equiv.trans_apply]
  ring

def swap {s : Shape} {w : ℕ} (x : Addr s w) : Addr s w :=
  (x.1, x.2.2.2.1, x.2.2.1, x.2.1, x.2.2.2.2)

def embed {s : Shape} (h : s.D ≤ s.E) (x : Addr s s.D) : Addr s s.E :=
  (x.1, x.2.1.castLE h, x.2.2.1, x.2.2.2.1.castLE h, x.2.2.2.2)

def stream {s : Shape} {w : ℕ} {A : Type} (f : Addr s w → A) := List.ofFn (f ∘ (rank s w).symm)

def occupied {s : Shape} (x : Addr s s.E) : Prop := x.2.1.val < s.D ∧ x.2.2.2.1.val < s.D

instance {s : Shape} (x : Addr s s.E) : Decidable (occupied x) := inferInstanceAs (Decidable (_ ∧ _))

def restrict {s : Shape} (x : Addr s s.E) (hx : occupied x) : Addr s s.D :=
  (x.1, ⟨x.2.1.val,hx.1⟩, x.2.2.1, ⟨x.2.2.2.1.val,hx.2⟩, x.2.2.2.2)

def padded {s : Shape} {A : Type} (pad : A) (f : Addr s s.D → A) (x : Addr s s.E) : A :=
  if hx : occupied x then f (restrict x hx) else pad

private theorem physical_axes (s : Shape) (h : s.D ≤ s.E) : s.axes.map BoxOrder.total = [s.P,s.E,s.G,s.E,s.B] := by
  simp [Shape.axes, BoxOrder.total, Nat.add_sub_of_le h]

private theorem dense_axes (s : Shape) : s.axes.map Prod.fst = [s.P,s.D,s.G,s.D,s.B] := rfl

private theorem digits_lt (s : Shape) (h : s.D ≤ s.E) (x : Addr s s.E) :
    List.Forall₂ (fun d p => d < BoxOrder.total p) (digits x) s.axes := by
  simp [digits, Shape.axes, List.forall₂_cons, BoxOrder.total, Nat.add_sub_of_le h]

private theorem digits_valid (s : Shape) (x : Addr s s.E) :
    List.Forall₂ (fun d p => d < p.1) (digits x) s.axes ↔ occupied x := by
  simp [digits, Shape.axes, List.forall₂_cons, occupied]

theorem mask_at (s : Shape) (h : s.D ≤ s.E) (x : Addr s s.E) :
    s.mask[(rank s s.E x).val]? = some true ↔ occupied x := by
  have H := (BoxOrder.padded_position (digits_lt s h x)).2
  rw [physical_axes s h, ←rank_val] at H
  exact H.trans (digits_valid s x)

theorem ordinal_at (s : Shape) (h : s.D ≤ s.E) (x : Addr s s.E) (hx : occupied x) :
    (s.mask.take (rank s s.E x).val).count true = (rank s s.D (restrict x hx)).val := by
  have H := (BoxOrder.valid_position ((digits_valid s x).mpr hx)).2.2
  rw [physical_axes s h, ←rank_val, dense_axes] at H
  exact H.trans (rank_val s s.D (restrict x hx)).symm

private theorem expandWith_eq {A : Type} (m : List Bool) (rows : List A) (pad : A)
    (h : m.count true = rows.length) : expandWith (m, rows, pad) = expand pad (m, rows) := by
  let xs := m.zip (expand pad (m,rows))
  have hx : xs.map Prod.fst = m := by simp [xs,List.map_fst_zip]
  have hy : xs.map Prod.snd = expand pad (m,rows) := by simp [xs,List.map_snd_zip]
  have hc := compress_tagged pad xs
  rw [hx,hy,compress_expand _ _ _ _ h] at hc
  rw [←hx, hc, expandWith_tagged, expand_tagged]

private theorem stream_get {s : Shape} {w : ℕ} {A : Type} (f : Addr s w → A) (x : Addr s w) :
    (stream f)[(rank s w x).val]? = some (f x) := by simp [stream]

theorem expandWith_stream {s : Shape} (h : s.D ≤ s.E) {A : Type} (pad : A) (f : Addr s s.D → A) :
    expandWith (s.mask,stream f,pad) = stream (padded pad f) := by
  rw [expandWith_eq _ _ _ (by simp [stream,Shape.denseVolume])]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < s.volume
  · let x := (rank s s.E).symm ⟨i,hi⟩
    have he : (rank s s.E x).val = i := by simp [x]
    rw [←he,stream_get]
    have hb : (rank s s.E x).val < s.mask.length := by rw [mask_length s h]; exact (rank s s.E x).isLt
    rw [get_expand _ _ _ _ hb]
    have hm := mask_at s h x
    rw [List.getElem?_eq_getElem hb, Option.some.injEq] at hm
    by_cases hx : occupied x
    · simp [hm.mpr hx, ordinal_at s h x hx, stream_get, padded, hx]
    · have hz : s.mask[(rank s s.E x).val] = false := Bool.eq_false_iff.mpr (fun ht => hx (hm.mp ht))
      simp [hz,padded,hx]
  · have e := Nat.le_of_not_gt hi
    rw [List.getElem?_eq_none (by simpa only [length_expand, mask_length s h] using e),
      List.getElem?_eq_none (by simpa only [stream,List.length_ofFn, Shape.volume] using e)]

/-- Cropping depends only on the entries whose validity bit is set. -/
private theorem compress_congr {A : Type} (pad : A) (m : List Bool) {n : ℕ} (hn : n = m.length)
    (g g' : Fin n → A) (he : ∀ i : Fin n, m[i.val]? = some true → g i = g' i) :
    compress pad (m,List.ofFn g) = compress pad (m,List.ofFn g') := by
  let test (i : Fin n) := m[i.val]?.getD false
  let tags (f : Fin n → A) := (List.finRange n).map (fun i => (test i,f i))
  have fst (f : Fin n → A) : (tags f).map Prod.fst = m := by
    apply List.ext_getElem
    · simp [tags,hn]
    · intro i _ hi
      simp [tags,test,List.getElem?_eq_getElem hi]
  have snd (f : Fin n → A) : (tags f).map Prod.snd = List.ofFn f := by
    simp [tags,List.ofFn_eq_map,Function.comp_def]
  have hc (f : Fin n → A) := compress_tagged pad (tags f)
  simp only [fst,snd] at hc
  rw [hc,hc]
  simp only [selected,tags,List.filter_map,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  have h := (List.mem_filter.mp hi).2
  change m[i.val]?.getD false = true at h
  have hi' : i.val < m.length := hn ▸ i.isLt
  apply he
  rw [List.getElem?_eq_getElem hi'] at h ⊢
  exact congrArg some h

/-- Extraction from any padded array reads its compact subarray in lexicographic order. -/
theorem compress_stream {s : Shape} (h : s.D ≤ s.E) {A : Type} (pad : A) (g : Addr s s.E → A) :
    compress pad (s.mask, stream g) = stream (g ∘ embed h) := by
  let f := g ∘ embed h
  change _ = stream f
  have hc : s.mask.count true = (stream f).length := by simp [stream,Shape.denseVolume]
  calc
    _ = compress pad (s.mask, stream (padded pad f)) := by
      apply compress_congr pad s.mask (mask_length s h).symm
      intro i hi
      let x := (rank s s.E).symm i
      have hx : occupied x := (mask_at s h x).mp (by
        rw [show rank s s.E x = i from (rank s s.E).apply_symm_apply i]
        exact hi)
      change g x = padded pad f x
      simp only [padded,hx,↓reduceDIte]
      rfl
    _ = _ := by rw [← expandWith_stream h pad f, expandWith_eq _ _ _ hc, compress_expand _ _ _ _ hc]

/-- A swap of the two physical `E`-ary coordinates sends the halo to itself. -/
theorem padded_swap {s : Shape} {A : Type} (pad : A) (f : Addr s s.D → A) :
    padded pad f ∘ swap = padded pad (f ∘ swap) := by
  funext x
  have hh : occupied (swap x) ↔ occupied x := and_comm
  by_cases hx : occupied x
  · change padded pad f (swap x) = padded pad (f ∘ swap) x
    simp only [padded, hx, hh.mpr hx, ↓reduceDIte]
    rfl
  · simp [padded,hx,mt hh.mp hx]

/-- Swapping the two padded coordinates and cropping gives exactly their dense swap. -/
theorem pad_swap_crop {s : Shape} (h : s.D ≤ s.E) {A : Type} (pad : A) (f : Addr s s.D → A) :
    compress pad (s.mask, stream (padded pad f ∘ swap)) = stream (f ∘ swap) := by
  rw [padded_swap, ←expandWith_stream h,expandWith_eq,compress_expand] <;>
    simp [stream, Shape.denseVolume]

open IntegerMultiplication.Strip

def series (s : Shape) (w : ℕ) : Series (Addr s w) :=
  (Series.natural s.P).cart ((Series.natural w).cart ((Series.natural s.G).cart
    ((Series.natural w).cart (Series.natural s.B))))

private def Lexical {A : Type} {n : ℕ} (S : Series A) (e : A ≃ Fin n) :=
  ∀ {B : Type} (f : A → B), S.tab f = List.ofFn (f ∘ e.symm)

private theorem lexicalNat (n : ℕ) : Lexical (Series.natural n) (Equiv.refl _) := by
  intro B f
  simp [Series.natural, Series.tab, Series.fixed,List.ofFn_eq_map]

private theorem lexicalCart {A : Type} {n : ℕ} (p : ℕ) {S : Series A} {e : A ≃ Fin n}
    (h : Lexical S e) : Lexical ((Series.natural p).cart S)
      (((Equiv.refl _).prodCongr e).trans finProdFinEquiv) := by
  intro B f
  rw [Series.grouped, lexicalNat p, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  change S.tab (fun a => f (i,a)) = _
  rw [h]
  apply congrArg List.ofFn
  funext j
  change f (i,e.symm j) = f (((Equiv.refl _).prodCongr e).symm (finProdFinEquiv.symm _))
  have hj : i.val*n+j.val < p*n := by
    simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using (finProdFinEquiv (i,j)).isLt
  have hi : (⟨i.val*n+j.val,hj⟩ : Fin (p*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    dsimp
    ac_rfl
  rw [hi, Equiv.symm_apply_apply]
  rfl

/-- The five natural tape-order enumerations serialize records by the mixed-radix address. -/
theorem series_tab {s : Shape} {w : ℕ} {A : Type} (f : Addr s w → A) :
    (series s w).tab f = stream f := by
  let hn : s.P*(w*(s.G*(w*s.B)))=s.P*w*s.G*w*s.B := by ac_rfl
  have h := lexicalCart s.P (lexicalCart w (lexicalCart s.G (lexicalCart w (lexicalNat s.B)))) f
  exact h.trans (List.ofFn_congr hn _)
end BinaryHalo

end NearSquareRoot
end Computability
end OAI
