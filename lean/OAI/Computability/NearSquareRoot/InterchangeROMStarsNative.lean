import OAI.Computability.NearSquareRoot.InterchangeROMStars

/-! # Full-volume reserve calls on the ordinary exposed request rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStars

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Port
  IntegerMultiplication.Loom InterchangeAddress InterchangeROMAddress InterchangeROMRecursion
  InterchangeSpectralFibre InterchangeROMExpose InterchangeBatch

abbrev frame {b : ℕ} (a m : ℕ) (q : Request b) (hb : 2≤b) (hn : 0<a+m+a)
    (hw : a+m+a < q.width) (ok : q.Admissible) : Input := ⟨b,a+m+a,q,hb,hn,hw,ok⟩

/-- The natural, unbanked center payload after the main spectral swap. -/
noncomputable abbrev afterMain {b : ℕ} (a m : ℕ) (q : Request b) (hb : 2≤b) (hn : 0<a+m+a)
    (hw : a+m+a < q.width) (ok : q.Admissible) :=
  let i := frame a m q hb hn hw ok
  stripe (centerRows i) (centerValues i ∘ swapMain (OuterReserves.main a m))

private theorem park_le {b a : ℕ} (hb : 2≤b) (q : Request b) (qs : List (Request b))
    (len : qs.length=2*a) (valid : ∀ x∈qs, x.Admissible ∧ x.rows.count=q.rows.count) :
    (headers Request.header qs).count ≤ ((2*a)*(2*b+9)+1)*(Nat.log 2 q.recordVolume+1) := by
  let L := Nat.log 2 q.recordVolume+1
  have logs : Nat.log 2 q.rows.count +1 ≤ L := Nat.succ_le_succ (Nat.log_mono_right q.rows_le_recordVolume)
  have h := Request.headers_count_log qs q.rows.count hb valid
  rw [len] at h
  have inner : (2*b+8)*(Nat.log 2 q.rows.count+1)+1 ≤ (2*b+9)*L := calc
    _ ≤ (2*b+8)*L + L := Nat.add_le_add (Nat.mul_le_mul_left _ logs) (by dsimp [L]; omega)
    _ = _ := by ring
  calc
    _ ≤ (2*a)*((2*b+9)*L)+1 := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ inner) _)
    _ ≤ (2*a)*((2*b+9)*L)+L := Nat.add_le_add_left (by dsimp [L]; omega) _
    _ = _ := by ring

/-- Every child preserves the exact number and width of records. Payload
validity transports directly from the original request. The only full-row
recursive space charge is its logarithmic forest of child headers. -/
theorem run_native : ∃ K d : ℕ, ∀ {b a m : ℕ} (q : Request b) (hb : 2≤b) (hn : 0<a+m+a)
    (hw : a+m+a < q.width) (ok : q.Admissible)
    (good : Tree → Prop) (_ : ∀ k, good (q.contents k)),
    let i := frame a m q hb hn hw ok
    let src := afterMain a m q hb hn hw ok
    let h := centerHeader i
    ∃ qs : List (Request b), qs.length=2*a ∧
      (∀ x∈qs, x.Admissible ∧ x.width = Request.lanes (a+m+a) q.width ∧
        x.recordWidth=q.recordWidth ∧ x.rows.count=q.rows.count ∧ ∀ k, good (x.contents k)) ∧
      (headers Request.header qs).count ≤ ((2*a)*(2*b+9)+1)*(Nat.log 2 q.recordVolume+1) ∧
      ∀ parent, At parent (command b a m) (Request.job b) [] qs (.fork (send h) src)
        ((Request.job b).reply q) (q.payload.count + admin b a m h K d)
        (headers Request.header qs).count 1 := by
  obtain ⟨K,d,code⟩ := run
  refine ⟨K,d,?_⟩
  intro b a m q hb hn hw ok good hg
  let : NeZero b := ⟨by omega⟩
  let i := frame a m q hb hn hw ok
  let rows := centerRows i
  let v := centerValues i
  let val := v ∘ swapMain (OuterReserves.main a m)
  let P := InterchangeFrame.pre b 1 q.before
  let G := InterchangeFrame.gap b 1 (rem i) q.between
  let B := InterchangeFrame.post b (rem i) q.after_
  have good' (x) : good (val x) := hg _
  obtain ⟨qs,len,shape,physical⟩ := code (a:=a) (m:=m) (f:=f i) P G B q.recordWidth val good good'
  have rowEq : rows.count=q.rows.count := (row_counts i).2.2
  have valid (x) (hx : x∈qs) : x.Admissible ∧ x.width = Request.lanes (a+m+a) q.width ∧
      x.recordWidth=q.recordWidth ∧ x.rows.count=q.rows.count ∧ ∀ k, good (x.contents k) := by
    obtain ⟨⟨width,N,l⟩,cells,inh⟩ := shape x hx
    exact ⟨Request.admissible_inherited hb (Request.admissible_center 1 (rem i) hb ok) inh,width,l,N.trans rowEq,cells⟩
  refine ⟨qs,len,valid,park_le hb q qs len (fun x hx => ⟨(valid _ hx).1,(valid _ hx).2.2.2.1⟩),?_⟩
  intro parent
  have dst : stripe rows (val ∘ OuterReserves.swapOuter) = (Request.job b).reply q := by
    apply Eq.trans _ (center_reply i)
    apply congrArg (stripe rows)
    exact funext fun x => congrArg v (OuterReserves.complete x).1
  have src : (stripe rows val).count = q.payload.count := by
    let σ := swapMain (OuterReserves.main a m) (P:=P) (G:=G) (B:=B) (b:=b) (f:=f i)
    have inv : Function.Involutive σ := by
      intro x
      rcases x with ⟨p,u,g,w,s⟩
      simp only [σ,swapMain,Prod.mk.injEq,true_and,and_true]
      constructor <;> funext j <;> by_cases h : j∈Set.range (OuterReserves.main a m) <;> simp [h]
    let e : Equiv.Perm _ := ⟨σ,σ,inv,inv⟩
    exact (Controlled.stripe_count_perm rows e v).trans (data_counts i).2.2.2.2.1
  have p := physical parent
  change At _ _ _ _ _ _ (stripe rows (val ∘ OuterReserves.swapOuter))
    ((stripe rows val).count+_) _ _ at p
  rw [dst,src] at p
  exact p

end InterchangeROMStars

end NearSquareRoot
end Computability
end OAI
