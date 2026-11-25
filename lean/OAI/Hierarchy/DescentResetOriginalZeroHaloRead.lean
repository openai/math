import OAI.Hierarchy.DescentResetOriginalZeroHalo

namespace OAI
/-! # The original numbered reset operands on the emitted native tape -/
namespace Hierarchy.DescentResetOriginalZeroHalo
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open private DescentResetHaloBroadcast.point_read from OAI.Hierarchy.DescentResetHaloBroadcast
noncomputable section

variable {w : ℕ} (base H G M b z short haloBits D : ℕ)

private theorem literal_id (p : Row H G M) :
    literal H G M b z short haloBits D (row H G M p).val=p.1.val := by
  simp only [literal,dite_eq_left (show (row H G M p).val < rows H G M from (row H G M p).isLt)]
  exact congrArg (fun q : Row H G M => q.1.val) ((row H G M).symm_apply_apply p)

private theorem literal_mask (p : Row H G M) :
    literal H G M b z short haloBits D (rows H G M+(row H G M p).val)=used G M p.2.val*2^b := by
  have small : (row H G M p).val < rows H G M := (row H G M p).isLt
  have late : ¬rows H G M+(row H G M p).val<rows H G M := by omega
  simp [literal,small,late]

private theorem literal_zero (p : Row H G M) :
    literal H G M b z short haloBits D (2*rows H G M+(row H G M p).val)=
    (data (fun (_ : Fin H) (g : Fin G)=>((decide (g.val=0)).toNat:Cell z)) p).val := by
  let n:=rows H G M
  let i:=(row H G M p).val
  have small : i<n := (row H G M p).isLt
  have first : ¬2*n+i<n := by omega
  have second : ¬2*n+i-n<n := by omega
  simp only [literal,Nat.add_sub_cancel_left]
  split
  next hit => exact (first hit).elim
  next =>
    exact congrArg (fun q : Row H G M => (data
      (fun (_ : Fin H) (g : Fin G) => ((decide (g.val=0)).toNat : Cell z)) q).val)
      ((row H G M).symm_apply_apply p)

private theorem literal_field (k : Fin 3) (q digit : ℕ) (usedFit : q ≤ M) (small : digit < 2^b) :
    literal H G M b z short haloBits D (3*rows H G M+k.val*pageSize M b+(q*2^b+digit))=
      DescentResetHaloBroadcast.point (outputBits short haloBits k.val) M q (decoded D k.val digit) := by
  let n:=rows H G M
  let U:=pageSize M b
  let j:=q*2^b+digit
  let i:=3*n+k.val*U+j
  have inside : j<U := (Nat.add_lt_add_left small _).trans_le
    (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_succ usedFit))
  have first : ¬i<n := by dsimp only [i];omega
  have second : ¬i-n<n := by dsimp only [i];omega
  have third : ¬i-2*n<n := by dsimp only [i];omega
  have drop : i-3*n=k.val*U+j := by dsimp only [i];omega
  have positive : 0<U := Nat.zero_lt_of_lt inside
  have part : (k.val*U+j)/U=k.val := by
    rw [Nat.mul_comm k.val U,Nat.mul_add_div positive,Nat.div_eq_of_lt inside,Nat.add_zero]
  have inner : (k.val*U+j)%U=j := by
    rw [Nat.mul_comm k.val U,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt inside]
  have upper : j/2^b=q := by
    dsimp only [j]
    rw [Nat.mul_comm q (2^b),Nat.mul_add_div (Nat.two_pow_pos b),Nat.div_eq_of_lt small,Nat.add_zero]
  have lower : j%2^b=digit := by
    dsimp only [j]
    rw [Nat.mul_comm q (2^b),Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt small]
  change literal H G M b z short haloBits D i=_
  simp only [literal]
  split
  next hit => exact (first hit).elim
  next =>
    change DescentResetHaloBroadcast.point (outputBits short haloBits ((i-3*n)/U)) M
      (((i-3*n)%U)/2^b) (decoded D ((i-3*n)/U) (((i-3*n)%U)%2^b))=_
    rw [drop,part,inner,upper,lower]

theorem zero_read (x : ℕ) (m : Memory w) (room : endAddress base H G M b < 2^w) :
    Source (zero base H G M b x)
      (fun (_ : Fin H) (g : Fin G)=>((decide (g.val=0 ∧ x=0)).toNat:Cell z)) M
      ((phase w base H G M b z short haloBits D).image m) := by
  intro p
  by_cases first : x=0
  · let i:=row H G M p
    have small : i.val<rows H G M:=i.isLt
    have fit:=bank_fit base H G M b (2*rows H G M) (by omega) room
    have nroom : count H G M b+1 ≤ 2^bits H G M b := Nat.le_pow_clog (by decide) _
    have written : 2*rows H G M+i.val < count H G M b := by unfold count;omega
    have atRow := DescentStaticWordColumn.read base (count H G M b) (literal H G M b z short haloBits D) m written
    simp only [zero,first,ite_true,Expr.eval,and_true]
    rw [bank_read _ _ (show i.val<(bank base H G M b (2*rows H G M)).size by
      change i.val<2^bits H G M b;omega) fit]
    change (phase w base H G M b z short haloBits D).image m (base+2*rows H G M+i.val)=_
    rw [Nat.add_assoc]
    exact atRow.trans (congrArg (fun t : ℕ => (t : Word w))
      (literal_zero H G M b z short haloBits D p))
  · have zeroVal : (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell z)) p).val=0 := by
      change (finFunctionFinEquiv (fun j : Fin M=>if _ : p.2.val*M+j.val<G then (0:Cell z) else 0)).val=0
      simp
    simp [zero,first,Expr.eval,zeroVal]

theorem field_read (k : Fin 3) (src : Bank) (digit : Fin H→Cell b) (m : Memory w)
    (fit : src.Fits w base) (size : H ≤ src.size)
    (stored : ∀h,m (src.base+h.val)=((digit h).val:Word w))
    (room : endAddress base H G M b < 2^w) :
    Source (field base H G M b k src)
      (fun h (_ : Fin G)=>(decoded D k.val (digit h).val : Cell (outputBits short haloBits k.val))) M
      ((phase w base H G M b z short haloBits D).image m) := by
  let n:=rows H G M
  let U:=pageSize M b
  let dst:=(phase w base H G M b z short haloBits D).image m
  let ids:=bank base H G M b 0
  let masks:=bank base H G M b n
  let sheet:=bank base H G M b (3*n+k.val*U)
  let c:=count H G M b
  let v:=2^(bits H G M b)
  have cap : c+1≤v:=Nat.le_pow_clog (by decide) _
  have count_eq : c=3*n+3*U:=rfl
  have last := Nat.mul_le_mul_right U (show k.val ≤ 2 by omega)
  have idsFit := bank_fit base H G M b 0 (by omega) room
  have masksFit := bank_fit base H G M b n (by dsimp only [n];omega) room
  have sheetFit := bank_fit base H G M b (3*n+k.val*U) (by dsimp only [n,U] at *;omega) room
  have lower (a : ℕ) (below : a<base) : dst a=m a :=
    (any base H G M b z short haloBits D m room).2 _ (.inl below)
  have raw (a : ℕ) (inside : a<c) : dst (base+a)=(literal H G M b z short haloBits D a:Word w) :=
    DescentStaticWordColumn.read _ _ _ _ inside
  intro p
  let i:=row H G M p
  let q:=used G M p.2.val
  let d:=(digit p.1).val
  let j:=q*2^b+d
  have iSmall : i.val<n:=i.isLt
  have ir : i.val<v:=by omega
  have dSmall : d<2^b:=(digit p.1).isLt
  have qSmall : q ≤ M:=Nat.min_le_left ..
  have jSmall : j<U := by
    calc
      _<q*2^b+2^b:=Nat.add_lt_add_left dSmall _
      _=(q+1)*2^b:=(Nat.succ_mul ..).symm
      _≤U:=Nat.mul_le_mul_right _ (Nat.succ_le_succ qSmall)
  have head : dst (ids.base+i.val)=(p.1.val:Word w) := by
    change dst (base+i.val)=_
    exact (raw i.val (by omega)).trans
      (congrArg (fun t : ℕ => (t : Word w)) (literal_id H G M b z short haloBits D p))
  have mask : dst (masks.base+i.val)=(q*2^b:ℕ) := by
    change dst (base+n+i.val)=_
    rw [Nat.add_assoc,raw _ (by omega),literal_mask]
  have source : dst (src.base+p.1.val)=(d:Word w) := by
    have inside := p.1.isLt.trans_le size
    rw [lower _ (by have bound:=fit.2.2; omega),stored]
  have look : dst (sheet.base+j)=(DescentResetHaloBroadcast.point (outputBits short haloBits k.val)
      M q (decoded D k.val d):Word w) := by
    change dst (base+(3*n+k.val*U)+j)=_
    rw [Nat.add_assoc,raw _ (by omega)]
    exact congrArg (fun t : ℕ=>(t:Word w)) (literal_field H G M b z short haloBits D k q d qSmall dSmall)
  change sheet.read dst (masks.read dst (i.val:Word w)+src.read dst (ids.read dst (i.val:Word w)))=_
  rw [bank_read masks dst ir masksFit,mask,bank_read ids dst ir idsFit,head,
    bank_read src dst (p.1.isLt.trans_le size) fit,source,←Nat.cast_add,bank_read sheet dst
      (show j<v by omega) sheetFit,look]
  exact congrArg (fun t : ℕ=>(t:Word w)) (by
    simpa only [DescentResetHaloBroadcast.point,Fin.cast_val_eq_self,id_eq,d,q] using
      DescentResetHaloBroadcast.point_read (b:=outputBits short haloBits k.val)
        (fun h : Fin H=>(decoded D k.val (digit h).val:Cell (outputBits short haloBits k.val)))
        (id : Fin H→Fin H) p)

/-- The zero flag is shared by the public and private original-word formats.
The two self digits use their respective widths on the same measured receiver. -/
structure Sources (A₀ A₁ : Bank) (oldMark joint : Fin H→Cell b) (m : Memory w) : Prop where
  zero : ∀x,Source (DescentResetOriginalZeroHalo.zero base H G M b x)
    (fun (_ : Fin H) (g : Fin G)=>((decide (g.val=0 ∧ x=0)).toNat:Cell z)) M m
  self : Source (DescentResetOriginalZeroHalo.self base H G M b A₀)
    (fun h (_ : Fin G)=>(((oldMark h).val-1 : ℕ):Cell short)) M m
  shape : Source (DescentResetOriginalZeroHalo.shape base H G M b A₁)
    (fun h (_ : Fin G)=>(((joint h).val / (2^Nat.clog 2 (D+2)) : ℕ):Cell short)) M m
  halo : Source (DescentResetOriginalZeroHalo.halo base H G M b A₀)
    (fun h (_ : Fin G)=>(((oldMark h).val-1 : ℕ):Cell haloBits)) M m

theorem Sources.transfer {A₀ A₁ : Bank} {oldMark joint : Fin H→Cell b} {m after : Memory w}
    (sources : Sources base H G M b z short haloBits D A₀ A₁ oldMark joint m)
    (oldFit : A₀.Fits w base) (jointFit : A₁.Fits w base)
    (roof : endAddress base H G M b < 2^w)
    (keep : ∀j,j<endAddress base H G M b → after j=m j) :
    Sources base H G M b z short haloBits D A₀ A₁ oldMark joint after := by
  have save {a : ℕ} (e : Expr) (f : Fin H→Fin G→Cell a)
      (fit : e.Fits w (endAddress base H G M b)) (r : Source e f M m) : Source e f M after :=
    fun i=>(eval_below e _ m after fit keep).trans (r i)
  exact ⟨fun x=>save _ _ (zero_fits base H G M b x roof) (sources.zero x),
    save _ _ (field_fits base H G M b 0 A₀ oldFit roof) sources.self,
    save _ _ (field_fits base H G M b 1 A₁ jointFit roof) sources.shape,
    save _ _ (field_fits base H G M b 2 A₀ oldFit roof) sources.halo⟩

theorem run (A₀ A₁ : Bank) (oldMark joint : Fin H→Cell b) (m : Memory w)
    (oldFit : A₀.Fits w base) (jointFit : A₁.Fits w base)
    (oldSize : H ≤ A₀.size) (jointSize : H ≤ A₁.size)
    (oldWord : ∀h,m (A₀.base+h.val)=((oldMark h).val:Word w))
    (jointWord : ∀h,m (A₁.base+h.val)=((joint h).val:Word w))
    (room : endAddress base H G M b < 2^w) :
    let pgm:=phase w base H G M b z short haloBits D
    pgm.Runs m ∧ Sources base H G M b z short haloBits D A₀ A₁ oldMark joint (pgm.image m) ∧
    ∀a,a<base ∨ endAddress base H G M b ≤ a → pgm.image m a=m a := by
  intro pgm
  have run:=any base H G M b z short haloBits D m room
  refine ⟨run.1,⟨fun x=>zero_read base H G M b z short haloBits D x m room,?_,?_,?_⟩,run.2⟩
  · exact field_read base H G M b z short haloBits D 0 A₀ oldMark m oldFit oldSize oldWord room
  · exact field_read base H G M b z short haloBits D 1 A₁ joint m jointFit jointSize jointWord room
  · exact field_read base H G M b z short haloBits D 2 A₀ oldMark m oldFit oldSize oldWord room

end
end Hierarchy.DescentResetOriginalZeroHalo

end OAI
