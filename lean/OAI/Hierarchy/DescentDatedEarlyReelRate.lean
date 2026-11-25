import OAI.Hierarchy.DescentEarlyRotationReel
import OAI.Hierarchy.DescentDatedPublicFloor

namespace OAI
/-! # The relocated exterior rows precede the terminal cohort's first write -/
namespace Hierarchy.DescentExteriorMatrixUpdate.Calendar
open DescentCompiler DescentDatedAddressBook DescentExteriorShelf Filter
noncomputable section
variable {ι : ℕ→Type*} {S : ∀h,ι h→AtomSchedule}
  {k tail start j r t E : ∀h,ι h→ℕ}

theorem early_room_rate
    (prior : Bounded start) (dates : Bounded (fun h i=>(S h i).length)) (exterior : Bounded E)
    (live : Bounded (fun h i=>rows (j h i) (r h i) (E h i)))
    (codes : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let d:=(S h i).groupWidth (k h i) (tail h i) 0+k h i;d*d≤K*h)
    (tables : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,tableBits (j h i) (r h i) (t h i)≤K*h) :
    Bounded (fun h i=>earlyEnd (S h i) (k h i) (tail h i) (start h i) (j h i) (r h i) (t h i) (E h i)) :=by
  let c (n : ℕ):=Bounded.const (ι:=ι) n
  obtain ⟨C,hc⟩:=codes
  obtain ⟨K,hk⟩:=tables
  have one:=Bounded.pow_of_linear (K:=C) hc
  have page:=Bounded.pow_of_linear (K:=K) hk
  have strideBound:=one.add (one.mul one)
  have shelf : Bounded (fun h i=>span (j h i) (r h i) (t h i) (E h i)) :=by
    apply (live.padded.max' page).of_le
    intro h i
    unfold span exponent
    rcases le_total (Nat.clog 2 (rows (j h i) (r h i) (E h i))) (tableBits (j h i) (r h i) (t h i)) with l|r'
    · rw [max_eq_right l]
      exact le_max_right ..
    · rw [max_eq_left r']
      exact le_max_left ..
  have first:=((prior.add (dates.mul strideBound)).add dates).add (c 1)
  exact first.add (((c 17).mul shelf).max' (shelf.add exterior))

theorem early_translate (S : AtomSchedule) (k tail start j r t E : ℕ) :
    earlyEnd S k tail start j r t E=start+earlyEnd S k tail 0 j r t E :=by
  simp only [earlyEnd,earlyAt,stop,tableAt,Nat.zero_add,Nat.add_assoc]

/-- The same stride works for all choices at a date and leaves the common cumulative
rotation and exterior spectrum in addressable memory for the terminal preflight. -/
theorem public_reel_room {choice : ℕ→Type*} (schedule : ℕ→AtomSchedule)
    (origin k tail j r t e : ℕ→ℕ)
    (endAt : ∀h,choice h→Fin (schedule h).length→ℕ→ℕ)
    (words : ∀h,choice h × Fin (schedule h).length→ℕ)
    (fit : ∀h c a b,endAt h c a b≤b+words h (c,a))
    (count : Bounded words)
    (header : ∃B:ℕ,∀ᶠ h:ℕ in atTop,origin h≤2^(B*h))
    (length : Bounded (ι:=fun _=>Unit) (fun h _=>(schedule h).length))
    (exterior : Bounded (ι:=fun _=>Unit) (fun h _=>e h))
    (live : Bounded (ι:=fun _=>Unit) (fun h _=>rows (j h) (r h) (e h)))
    (codes : ∃C:ℕ,∀ᶠ h:ℕ in atTop,let d:=(schedule h).groupWidth (k h) (tail h) 0+k h;d*d≤C*h)
    (tables : ∃T:ℕ,∀ᶠ h:ℕ in atTop,tableBits (j h) (r h) (t h)≤T*h) :
    ∃K W:ℕ,∀ᶠ h:ℕ in atTop,
      earlyEnd (schedule h) (k h) (tail h) (canonicalFloor (origin h) h K (schedule h).length)
        (j h) (r h) (t h) (e h)<2^(W*h) ∧
      ∀c (a:Fin (schedule h).length),endAt h c a (canonicalFloor (origin h) h K a.val)≤
        canonicalFloor (origin h) h K (a.val+1) :=by
  obtain ⟨A,ha⟩:=length
  obtain ⟨K,W,dated⟩:=calendar_public_slots endAt words fit count header ⟨A,ha.mono fun h hi=>hi ()⟩
  have old : Bounded (ι:=fun _=>Unit)
      (fun h _=>canonicalFloor (origin h) h K (schedule h).length):=
    ⟨W,dated.mono fun _ hh _=>hh.1.le⟩
  obtain ⟨C,hc⟩:=codes
  obtain ⟨T,ht⟩:=tables
  obtain ⟨V,last⟩:=early_room_rate (S:=fun h (_:Unit)=>schedule h) old
    ⟨A,ha⟩ exterior live ⟨C,hc.mono fun _ yes _=>yes⟩ ⟨T,ht.mono fun _ yes _=>yes⟩
  refine ⟨K,V+1,?_⟩
  filter_upwards [last,dated,eventually_ge_atTop 1] with h done_ steps positive
  refine ⟨(done_ ()).trans_lt (Nat.pow_lt_pow_right (by decide : 1<2) ?_),steps.2⟩
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentExteriorMatrixUpdate.Calendar

end OAI
