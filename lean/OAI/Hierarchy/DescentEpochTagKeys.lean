import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.SplitLengths
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Finite keys for successive gadget births and physical cable subdivisions

A new gadget or rotor configuration occupies a fresh sum band. An old tag
keeps its prior ordinal. A physical split appends a bounded list of piece
lengths, with its own length digit so that separate splits can be decoded.
-/
namespace Hierarchy.DescentEpochTagKeys

/-- A total numeric table key and its readback for the actual admissible tags. -/
structure Codec (T : Type*) (size : ℕ) where
  store : T → Fin size
  read : Fin size → T
  fits : T → Prop
  read_store : ∀ t, fits t → read (store t)=t

def Codec.ofEquiv {T : Type*} {n : ℕ} (e : T ≃ Fin n) : Codec T n :=
  ⟨e,e.symm,fun _ => True,fun t _ => e.symm_apply_apply t⟩

def Codec.birth {T U : Type*} {n m : ℕ} (old : Codec T n) (fresh : Codec U m) :
    Codec (T ⊕ U) (n+m) where
  store t := finSumFinEquiv (t.map old.store fresh.store)
  read i := (finSumFinEquiv.symm i).map old.read fresh.read
  fits := Sum.elim old.fits fresh.fits
  read_store t h := by
    cases t with
    | inl t => simp [old.read_store t h]
    | inr t => simp [fresh.read_store t h]

def Codec.prod {T U : Type*} {n m : ℕ} (left : Codec T n) (right : Codec U m) :
    Codec (T × U) (n*m) where
  store z := finProdFinEquiv (left.store z.1,right.store z.2)
  read k := let z := finProdFinEquiv.symm k
            (left.read z.1,right.read z.2)
  fits z := left.fits z.1 ∧ right.fits z.2
  read_store z hz := by simp [left.read_store z.1 hz.1,right.read_store z.2 hz.2]

/-- A physical finite chart may have unused codes. Read an unused subtype
code as a fixed valid inhabitant; every genuine entry keeps its ordinal. -/
def Codec.subtype {T : Type*} {n : ℕ} (old : Codec T n) (p : T→Prop) [DecidablePred p]
    (fallback : Subtype p) : Codec (Subtype p) n where
  store z := old.store z.val
  read i := if h : p (old.read i) then ⟨old.read i,h⟩ else fallback
  fits z := old.fits z.val
  read_store z good := by
    have back := old.read_store z.val good
    have inside : p (old.read (old.store z.val)) := back.symm ▸ z.property
    rw [dite_eq_left inside]
    exact Subtype.ext back

def span (A M : ℕ) := (A+1)*(M+1)^A

def ListFits (A M : ℕ) (xs : List ℕ) := xs.length≤A ∧ ∀ x∈xs, x≤M

private def padded (A M : ℕ) (xs : List ℕ) (i : Fin A) : Fin (M+1) :=
  ⟨min M (if h : i.val<xs.length then xs[i.val] else 0),Nat.lt_succ_of_le (min_le_left ..)⟩

private def takeKey {A M : ℕ} (s : Fin (A+1) × (Fin A → Fin (M+1))) : List ℕ :=
  List.ofFn (fun i : Fin s.1.val => (s.2 ⟨i.val,i.isLt.trans_le (Nat.le_of_lt_succ s.1.isLt)⟩).val)

private def keyEquiv (A M : ℕ) : (Fin (A+1) × (Fin A → Fin (M+1))) ≃ Fin (span A M) :=
  (Equiv.prodCongr (Equiv.refl _) finFunctionFinEquiv).trans finProdFinEquiv

/-- Finite padded radix digits plus their genuine length form an invertible
description on every actual bounded sequence. -/
def listCodec (A M : ℕ) : Codec (List ℕ) (span A M) where
  fits := ListFits A M
  store xs := keyEquiv A M (⟨min A xs.length,Nat.lt_succ_of_le (min_le_left ..)⟩,padded A M xs)
  read k := takeKey ((keyEquiv A M).symm k)
  read_store xs valid := by
    rw [Equiv.symm_apply_apply]
    apply List.ext_getElem
    · simp [takeKey,min_eq_right valid.1]
    · intro i hi hx
      have atDigit := valid.2 xs[i] (List.getElem_mem hx)
      simp [takeKey,padded,hx,min_eq_right atDigit]

def Codec.pieces {T : Type*} {n : ℕ} (old : Codec T n) (A M : ℕ) :
    Codec (T × List ℕ) (n*span A M) := old.prod (listCodec A M)

theorem regroup {α : Type*} (groups : List (List α)) :
    (groups.map List.length).splitLengths groups.flatten = groups := by
  induction groups with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- A reset tag records the width of each original scalar operand, followed by
all source-bit offsets in their original operand order. Empty operands and
repeated references both have exact readback. -/
def Codec.gather {T : Type*} {n : ℕ} (old : Codec T n) (arity width total maxOffset : ℕ) :
    Codec (T × List (List ℕ)) ((n*span arity width)*span total maxOffset) :=
  let flat := (old.pieces arity width).pieces total maxOffset
  {store := fun t => flat.store ((t.1,t.2.map List.length),t.2.flatten)
   read := fun i => let z := flat.read i
                    (z.1.1,z.1.2.splitLengths z.2)
   fits := fun t => old.fits t.1 ∧ ListFits arity width (t.2.map List.length) ∧
     ListFits total maxOffset t.2.flatten
   read_store := by
     rintro ⟨t,groups⟩ ⟨oldFit,lengths,offsets⟩
     have valid : flat.fits ((t,groups.map List.length),groups.flatten) := ⟨⟨oldFit,lengths⟩,offsets⟩
     change ((flat.read (flat.store ((t,groups.map List.length),groups.flatten))).1.1,
       (flat.read (flat.store ((t,groups.map List.length),groups.flatten))).1.2.splitLengths
         (flat.read (flat.store ((t,groups.map List.length),groups.flatten))).2)=(t,groups)
     rw [flat.read_store _ valid,regroup]}

def gatherBits (trunk : ℕ→Bool) (refs : List (List ℕ)) : List (List Bool) :=
  refs.map (fun operand=>operand.map trunk)

/-- Evaluating the registered key reads each bit at its declared physical
offset and reproduces every original operand group. -/
theorem gather_value {T F : Type*} {n : ℕ} (old : Codec T n)
    (arity width total maxOffset : ℕ) (t : T × List (List ℕ))
    (valid : (old.gather arity width total maxOffset).fits t)
    (trunk : ℕ→Bool) (value : T→List (List Bool)→F) :
    let book := old.gather arity width total maxOffset
    let row := book.read (book.store t)
    value row.1 (gatherBits trunk row.2)=value t.1 (gatherBits trunk t.2) := by
  dsimp only
  rw [(old.gather arity width total maxOffset).read_store t valid]

inductive Layer where
  | birth (n : ℕ)
  | lengths (entries maximum : ℕ)
deriving DecidableEq

/-- The most recent operation is at the head. A keep/coalesce stage leaves
this list unchanged. -/
def Raw (base : ℕ) : List Layer → Type
  | [] => Fin base
  | .birth n :: earlier => Raw base earlier ⊕ Fin n
  | .lengths _A _M :: earlier => Raw base earlier × List ℕ

def capacity (base : ℕ) : List Layer → ℕ
  | [] => base
  | .birth n :: earlier => capacity base earlier+n
  | .lengths A M :: earlier => capacity base earlier*span A M

def codec (base : ℕ) : (layers : List Layer) → Codec (Raw base layers) (capacity base layers)
  | [] => Codec.ofEquiv (Equiv.refl _)
  | .birth n :: earlier => (codec base earlier).birth (Codec.ofEquiv (Equiv.refl (Fin n)))
  | .lengths A M :: earlier => (codec base earlier).pieces A M

theorem read_store (base : ℕ) (L : List Layer) (t : Raw base L) (valid : (codec base L).fits t) :
    (codec base L).read ((codec base L).store t)=t := (codec base L).read_store t valid

/-- The actual trivalent seed census has four arities. For arity m its table
has one coefficient index for each of the 2^m Boolean input settings. -/
def censusEquiv (s : ℕ) :
    (Σ m : Fin 4,(Fin m.val → Bool) → Fin (s+1)) ≃ Fin (∑ m : Fin 4, (s+1)^(2^m.val)) := by
  let bits (m : Fin 4) : (Fin m.val → Bool) ≃ Fin (2^m.val) :=
    (Equiv.piCongrRight (fun _ => finTwoEquiv.symm)).trans finFunctionFinEquiv
  let table (m : Fin 4) : ((Fin m.val → Bool) → Fin (s+1)) ≃ Fin ((s+1)^(2^m.val)) :=
    ((bits m).arrowCongr (Equiv.refl _)).trans finFunctionFinEquiv
  exact (Equiv.sigmaCongrRight table).trans finSigmaFinEquiv

def census (s : ℕ) :
    Codec ((Σ m : Fin 4,(Fin m.val → Bool) → Fin (s+1)) ⊕ Unit)
      ((∑ m : Fin 4, (s+1)^(2^m.val))+1) :=
  (Codec.ofEquiv (censusEquiv s)).birth (Codec.ofEquiv (Equiv.ofUnique Unit (Fin 1)))

/-- The birth alphabet of a six-party gadget has a term index, its actual
eight-channel profile, and a role. The range check on a profile is decidable. -/
def gadget (Z C : ℕ) :
    Codec (Fin (Z+1) × {p : Fin 8 → Fin (C+2) // (∑ e,(p e).val)≤C+8} × Fin 6)
      ((Z+1)*((C+2)^8*6)) :=
  let table : Codec (Fin 8 → Fin (C+2)) ((C+2)^8) := Codec.ofEquiv finFunctionFinEquiv
  let profile := table.subtype (fun p=>(∑ e,(p e).val)≤C+8) ⟨fun _=>0,by simp⟩
  (Codec.ofEquiv (Equiv.refl (Fin (Z+1)))).prod (profile.prod (Codec.ofEquiv (Equiv.refl (Fin 6))))

theorem census_fits (s : ℕ) (tag) : (census s).fits tag := by
  cases tag <;> trivial

theorem gadget_fits (Z C : ℕ) (tag) : (gadget Z C).fits tag :=
  ⟨trivial,trivial,trivial⟩

def Layer.Bounded (birthBits A M : ℕ) : Layer → Prop
  | .birth n => n ≤ 2^birthBits
  | .lengths a m => a ≤ A ∧ m ≤ M

private theorem span_mono {a m A M : ℕ} (ha : a≤A) (hm : m≤M) : span a m≤ span A M :=
  Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left (by omega : m+1≤M+1) a).trans
    (Nat.pow_le_pow_right (Nat.succ_pos M) ha))

/-- A new gadget is charged additively; in particular its original alphabet
size is never multiplied once per epoch. -/
theorem capacity_bound (base birthBits A M : ℕ) (baseFit : base≤2^birthBits) (L : List Layer)
    (bounds : ∀ l∈L, l.Bounded birthBits A M) :
    capacity base L ≤ ((L.length+1)*2^birthBits)*(span A M)^L.length := by
  let C := span A M
  have positive : 0<C := by dsimp [C,span]; positivity
  induction L with
  | nil => simpa [capacity] using baseFit
  | cons layer rest ih =>
    have old := ih (fun l hl => bounds l (List.mem_cons_of_mem _ hl))
    have app := bounds layer (List.mem_cons_self ..)
    cases layer with
    | birth n =>
      change n≤2^birthBits at app
      have addRoom := Nat.le_mul_of_pos_right (2^birthBits) (show 0<C^rest.length from Nat.pow_pos positive)
      have grow := Nat.pow_le_pow_right positive (Nat.le_succ rest.length)
      change capacity base rest+n ≤ ((rest.length+1+1)*2^birthBits)*C^(rest.length+1)
      calc
        _ ≤ ((rest.length+1)*2^birthBits)*C^rest.length+2^birthBits*C^rest.length :=
          Nat.add_le_add old (app.trans addRoom)
        _ = ((rest.length+1+1)*2^birthBits)*C^rest.length := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ grow
    | lengths a m =>
      change a≤A ∧ m≤M at app
      have enlarged := Nat.mul_le_mul (Nat.mul_le_mul_right (2^birthBits) (Nat.le_succ (rest.length+1)))
        (le_refl (C^(rest.length+1)))
      change capacity base rest*span a m ≤ ((rest.length+1+1)*2^birthBits)*C^(rest.length+1)
      calc
        _ ≤ (((rest.length+1)*2^birthBits)*C^rest.length)*C :=
          Nat.mul_le_mul old (span_mono app.1 app.2)
        _ = ((rest.length+1)*2^birthBits)*C^(rest.length+1) := by rw [pow_succ,Nat.mul_assoc]
        _ ≤ _ := enlarged

def width (birthBits A M stages : ℕ) :=
  birthBits+Nat.clog 2 (stages+1)+stages*(2*A*Nat.clog 2 (M+2))

theorem capacity_le_pow (base birthBits A M : ℕ) (baseFit : base≤2^birthBits) (L : List Layer)
    (bounds : ∀ l∈L,l.Bounded birthBits A M) :
    capacity base L≤2^(width birthBits A M L.length) := by
  let digit := Nat.clog 2 (M+2)
  have two : 1<2 := by decide
  have radix : M+2≤2^digit := Nat.le_pow_clog two _
  have letters : M+1≤2^digit := by omega
  have header : A+1≤(2^digit)^A := (Nat.lt_two_pow_self (n:=A)).trans_le
    (Nat.pow_le_pow_left (by omega : 2≤2^digit) A)
  have line : span A M≤2^(2*A*digit) := by
    have both := Nat.mul_le_mul header (Nat.pow_le_pow_left letters A)
    calc
      _ ≤ (2^digit)^A*(2^digit)^A := both
      _ = 2^(2*A*digit) := by rw [←pow_mul,←pow_add];congr 1;ring
  calc
    capacity base L ≤ ((L.length+1)*2^birthBits)*(span A M)^L.length :=
      capacity_bound base birthBits A M baseFit L bounds
    _ ≤ ((2^(Nat.clog 2 (L.length+1)))*2^birthBits)*(2^(2*A*digit))^L.length :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_pow_clog two _)) (Nat.pow_le_pow_left line _)
    _ = 2^(width birthBits A M L.length) := by
      rw [←pow_mul,←pow_add,←pow_add]
      congr 1
      unfold width
      dsimp only [digit]
      ring

theorem code_width (base birthBits A M : ℕ) (baseFit : base≤2^birthBits) (L : List Layer)
    (bounds : ∀ l∈L,l.Bounded birthBits A M) :
    Nat.clog 2 (capacity base L)≤width birthBits A M L.length :=
  (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 (capacity_le_pow base birthBits A M baseFit L bounds)

end Hierarchy.DescentEpochTagKeys

end OAI
