import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Native packed output words for both measured old-graph histograms -/

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {a b M H J w : ℕ}

theorem masked_data (f : Cell a→Cell b) (x : Fin H→Fin J→Cell a) (p : Row H J M) :
    masked f x p=(data (fun v g=>f (x v g)) p).val := by
  let word : Cell (b*M) := ⟨masked f x p,(Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b (Nat.min_le_left M _)))⟩
  have digits : (encode b M).symm word=(encode b M).symm (data (fun v g=>f (x v g)) p) := by
    funext i
    apply Fin.ext
    have hd := digit_encode ((encode b M).symm word) i
    rw [Equiv.apply_symm_apply] at hd
    rw [←hd]
    change digit b i.val (masked f x p)=_
    simp only [data,Equiv.symm_apply_apply]
    by_cases hi : p.2.val*M+i.val<J
    · simpa [hi] using active_read f x p i hi
    · have pad : used J M p.2.val ≤ i.val := (Nat.min_le_right M _).trans (by omega)
      simpa [hi] using padding_zero f x p i pad
  exact congrArg Fin.val ((encode b M).symm.injective digits)

private theorem before (out n : ℕ) (e : Expr) (m : Memory w) {a : ℕ} (ha : a<out) :
    image out n e m a=m a := by simp [image,fillSegment,Nat.not_le.mpr ha]

private theorem keep_frame (g : Banks) (f : Cell a→Cell b) (x : Fin H→Fin J→Cell a)
    (out msize : ℕ) (em : Expr) (mem : Memory w) (fit : Fits g a b M H J w out)
    (old : PinFrame (M:=M) g f x mem) : PinFrame (M:=M) g f x (image out msize em mem) := by
  constructor
  · intro j s
    rw [before]
    · exact old.1 j s
    · cases j with
      | inl key =>
        have hk : key.val<g.dictionary.size := by simp [Bank.size,fit.dictBits]
        exact (Nat.add_lt_add_left hk _).trans_le fit.dictionary.2.2
      | inr key => exact (Nat.add_lt_add_left (key.isLt.trans_le fit.maskSize) _).trans_le fit.mask.2.2
  · intro p
    rw [before]
    · exact old.2 p
    · exact (Nat.add_lt_add_left ((row H J M p).isLt.trans_le fit.srcSize) _).trans_le fit.source.2.2

theorem col_read (g : Banks) (out : ℕ) (fit : Fits g a b M H J w out) (f : Cell a→Cell b)
    (x : Fin H→Fin J→Cell a) (m : Memory w) (raw : PinFrame (M:=M) g f x m) (p : Row H J M) :
    image out (H*chunks J M) (DescentSIMDLookup.lookup g) m (out+(row H J M p).val)=
      ((data (fun v j=>f (x v j)) p).val:Word w) := by
  have here:=(row H J M p).isLt
  have read:=lookup_read g out fit f x m raw p
  rw [masked_data] at read
  simpa [image,fillSegment,show out≤out+(row H J M p).val ∧
    out+(row H J M p).val<out+H*chunks J M by omega,Nat.cast_add] using read

def histograms (first second : Banks) (lo hi H J M w : ℕ) :=
  (program first lo H J M w).seq (program second hi H J M w)

def clocks (first second : Banks) (H J M : ℕ) :=
  (4+H*chunks J M*(2*(DescentSIMDLookup.lookup first).work+4))+
  (4+H*chunks J M*(2*(DescentSIMDLookup.lookup second).work+4))

/-- Both tables receive the same old physical source rows. The output sectors
contain clean whole words, including every final partial chunk. -/
theorem histograms_frames (first second : Banks) (lo hi : ℕ)
    (fit1 : Fits first a b M H J w lo) (fit2 : Fits second a b M H J w lo)
    (fit3 : Fits second a b M H J w hi) (apart : lo+H*chunks J M≤hi)
    (f g : Cell a→Cell b) (x : Fin H→Fin J→Cell a) (mem : Memory w)
    (h1 : PinFrame (M:=M) first f x mem) (h2 : PinFrame (M:=M) second g x mem) :
    ∃ last,(histograms first second lo hi H J M w).Exec mem last (clocks first second H J M) ∧
    (∀p : Row H J M,last (lo+(row H J M p).val)=((data (fun v j=>f (x v j)) p).val:Word w)) ∧
    (∀p : Row H J M,last (hi+(row H J M p).val)=((data (fun v j=>g (x v j)) p).val:Word w)) ∧
    (∀t<lo,last t=mem t) ∧ ∀t,hi+H*chunks J M≤t→last t=mem t := by
  let n:=H*chunks J M
  let e₁:=DescentSIMDLookup.lookup first
  let e₂:=DescentSIMDLookup.lookup second
  let mid:=image lo n e₁ mem
  let last:=image hi n e₂ mid
  have f₁ : e₁.Fits w lo := by simp [e₁,DescentSIMDLookup.lookup,Expr.Fits,fit1.source,fit1.mask,fit1.dictionary]
  have f₂ : e₂.Fits w hi := by simp [e₂,DescentSIMDLookup.lookup,Expr.Fits,fit3.source,fit3.mask,fit3.dictionary]
  have one : (program first lo H J M w).Exec mem mid (4+n*(2*e₁.work+4)) :=
    scan_exec lo n e₁ mem f₁ fit1.output
  have two : (program second hi H J M w).Exec mid last (4+n*(2*e₂.work+4)) :=
    scan_exec hi n e₂ mid f₂ fit3.output
  refine ⟨last,?_,?_,col_read second hi fit3 g x mid (keep_frame second g x lo n e₁ mem fit2 h2),?_,?_⟩
  · intro P R U machine pc reg pub ep prog vals cfg raw entry eqn
    exact Procedure.Exec.then one two machine pc reg pub ep prog vals cfg raw entry eqn
  · intro p
    have placed : lo+(row H J M p).val<hi := (Nat.add_lt_add_left (row H J M p).isLt _).trans_le apart
    exact (before hi n e₂ mid placed).trans (col_read first lo fit1 f x mem h1 p)
  · intro t ht
    exact (before hi n e₂ mid (by omega)).trans (before lo n e₁ mem ht)
  · intro t ht
    have hhi : ¬t<hi+n:=by omega
    have hlo : ¬t<lo+n:=by dsimp [n];omega
    simp [last,mid,image,fillSegment,hhi,hlo]

theorem histograms_exec (first second : Banks) (lo hi : ℕ)
    (fit1 : Fits first a b M H J w lo) (fit2 : Fits second a b M H J w lo)
    (fit3 : Fits second a b M H J w hi) (apart : lo+H*chunks J M≤hi)
    (f g : Cell a→Cell b) (x : Fin H→Fin J→Cell a) (mem : Memory w)
    (h1 : PinFrame (M:=M) first f x mem) (h2 : PinFrame (M:=M) second g x mem) :
    ∃ last,(histograms first second lo hi H J M w).Exec mem last (clocks first second H J M) ∧
    (∀p : Row H J M,last (lo+(row H J M p).val)=((data (fun v j=>f (x v j)) p).val:Word w)) ∧
    (∀p : Row H J M,last (hi+(row H J M p).val)=((data (fun v j=>g (x v j)) p).val:Word w)) ∧
    ∀t<lo,last t=mem t := by
  obtain ⟨last,run,firstRead,secondRead,low,_⟩:=histograms_frames first second lo hi fit1 fit2 fit3 apart f g x mem h1 h2
  exact ⟨last,run,firstRead,secondRead,low⟩

theorem clock_invoice (first second : Banks) (H J a b w : ℕ) (positive : 0 < max a b)
    (wide : 2*max a b≤w) :
    clocks first second H J (lanes w (max a b))*w≤
      8*w+88*(H*w+4*H*J*(max a b)) := by
  have l := (DescentSIMDLookup.invoice first H J a b w positive wide).1
  have r := (DescentSIMDLookup.invoice second H J a b w positive wide).1
  unfold clocks
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
