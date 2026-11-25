import OAI.Computability.IntegerMultiplication.Atoll.Dye
import OAI.Computability.IntegerMultiplication.Thin.Rift

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Cap Strip Halo Param Scale Loom Earth Adic Packed Thin
variable (f k r:ℕ)
-- New coordinate reps (z last field, (M=(short,b from f-gapped),a first)).
abbrev View := Fin (2^k) × Mid f k r × Fin (2^k)
abbrev laid : Series (View f k r) :=
  (Series.natural (2^k)).cart ((braid f k r).cart (Series.natural (2^k)))
abbrev bent_ : Series (View f k r) :=
  (Series.natural (2^k)).cart ((winds f k r).cart (Series.natural (2^k)))
variable {d:ℕ}
abbrev addTail (m:ℕ):
    ((UX d m) × Fin (2^m))≃UX (d+1) m := (Equiv.prodComm ..).trans join
noncomputable def lastRoll (m:ℕ): Adopt
    ((Retreat d (2^m)).cart (Series.natural (2^m))) (Retreat (d+1) (2^m)):=
  by
  let q:= (Retreat d (2^m)).cart (Series.natural (2^m))
  let p:=q.via (addTail m)
  have h: Runs p (Fall (r:=Uni _ _)) :=
    transfer q _ (prodRuns _ _ _ (Digit _) retreat_runs (clock _)) (by
      rintro ⟨x,v⟩ ⟨y,u⟩ (h|⟨t,e⟩)
      · obtain ⟨i,b,p⟩:=h
        refine ⟨i.succ,?_,?_⟩
        · change Digit _ (join (v,x) i.succ) (join (u,y) i.succ)
          rw [tail_j,tail_j]; exact b
        intro j
        refine Fin.cases (fun e=>False.elim (Nat.not_lt_zero _ e)) (fun k w=> ?_) j
        change join (v,x) k.succ=join (u,y) k.succ; rw [tail_j,tail_j]
        exact p _ (Fin.succ_lt_succ_iff.mp w)
      refine ⟨0,e,?_⟩
      intro j
      refine Fin.cases (fun w=>False.elim (lt_irrefl _ w)) (fun k _=> ?_) j
      change join (v,x) k.succ=join (u,y) k.succ; rw [tail_j,tail_j]
      exact congrFun t _)
  let g := sameness _ h (retreat_runs (d:=d+1) (s:=2^m))
  refine ⟨addTail m,fun {O} x=>?_⟩
  rw [← g]; exact Strip.Series.tab_via q _ _

-- casting
def cutX {m f k:ℕ} (H:f=k) : UX f m≃UX k m where
  toFun x i:=x (Fin.cast H.symm i)
  invFun x i:=x (Fin.cast H i)
  left_inv _:=rfl; right_inv _:=rfl
def cutH {m f k:ℕ}(H:f=k): Adopt (House f (2^m)) (House k (2^m)):=
  ⟨cutX H,fun {_}=>by subst k; intro; rfl⟩
def cutR {m f k:ℕ}(H:f=k): Adopt (Retreat f (2^m)) (Retreat k (2^m)):=
  ⟨cutX H,fun {_}=>by subst k; intro;rfl⟩

variable {n:ℕ}(h:Season n)
abbrev rest (n:ℕ):=scouts n-1
include h
theorem coverP : rest n+1= scouts n := by unfold rest; have q:=h.dim; unfold scouts; omega
abbrev Vw := View (rest n) (ell n) (reach n)
omit h
-- align z, Mrev,a.
noncomputable def topline (h:Season n):
    Adopt (laid (rest n) (ell n) (reach n)) (Rim h) :=
  let P := (Adopt.same (Csys n)).split ((lastRoll (ell n)).thenDo (cutR (coverP h)))
  let Q:= (Adopt.rotate (Csys n) (Retreat (rest n) (wall n)) (Peace n)).thenDo P
  (((Adopt.same (Peace n)).split Q).thenDo (Adopt.turn _ (gold h)))
abbrev glean (h:Season n)(x:Vw (n:=n)) : Tri n :=
  gluer h (cutX (m:=ell n) (coverP h) (addTail (ell n) (x.2.1.2,x.2.2)),
    x.2.1.1,x.1)
theorem cast0 (h:Season n)(x:Vw (n:=n)):(topline h).cast x=glean h x:= rfl
-- align a,Mnew,z. winds representation Mid as (short,b).
noncomputable def midline (h:Season n):
    Adopt (bent_ (rest n) (ell n) (reach n)) (Halo.walk h) :=
  let E:= Peace n
  let H:= House (rest n) (wall n)
  let V:= Csys n
  let S : Adopt (E.cart H) (Track E (rest n+1)) := Adopt.turn _ join
  let Q:= S.thenDo (cutH (coverP h))
  let M:= ((Adopt.turn _ (Equiv.prodComm ..)).back : Adopt (winds (rest n) (ell n) (reach n)) (H.cart V))
  let G:= (((M.split (Adopt.same E)).thenDo (Adopt.rotate H V E)))
  let D:=((((Adopt.same E).split G).thenDo (Adopt.rotate E H (V.cart E)).back).thenDo (Q.split (Adopt.same _)))
  -- layout Psys cart Csys cart E association. rotate -> (P×short)× E
  (D.thenDo (Adopt.rotate (Psys n) V E).back).thenDo (Adopt.turn _ ((Equiv.prodAssoc ..).trans (prism h).symm))
variable {f k r}
abbrev flipV (x:View f k r): View f k r:=(x.2.2,x.2.1,x.1)
@[simp] theorem flip_twice (x:View f k r):flipV (flipV x)=x:=rfl
theorem cast1 (h:Season n)(x:Vw (n:=n)):(midline h).cast x=glean h (flipV x):=rfl

-- align Thin switch
noncomputable def splash (f k r): Adopt (laid f k r) (Thin.lands 0 k (Mbit f k r) 0) :=
  let Z:=noir k
  -- want (a,(m,b)) -> (_,(a,(m,(b,_)))).
  let G:Adopt ((braid f k r).cart (Series.natural (2^k))) ((line 2 (Mbit f k r)).cart ((line 2 k).cart Series.one)) :=
    (Aseal f k r).split (Z.back.thenDo (Adopt.skip _).back)
  (Z.back.split G).thenDo (Adopt.omitL _).back
theorem others (x:View f k r):
    (splash f k r).cast (flipV x)=switch_ ((splash f k r).cast x):= rfl
-- align curtain. prefix [k], block M, no suffix; grouped by last. old & new share types.
abbrev Veil := Fin (2^k) × Mid f k r
abbrev dark_ (f k r:ℕ):Series (Veil (f:=f) (k:=k) (r:=r)):=
  (Series.natural _).cart (braid ..)
abbrev light_ (f k r:ℕ):Series (Veil (f:=f) (k:=k) (r:=r)):=
  (Series.natural _).cart (winds ..)
abbrev Acover (f k r):Adopt ((dark_ f k r).cart (Series.natural (2^k))) (laid f k r):=
  Adopt.rotate _ _ _
abbrev Bcover (f k r):Adopt ((light_ f k r).cart (Series.natural (2^k))) (bent_ f k r):=
  Adopt.rotate _ _ _
noncomputable def CvA (f k r): Adopt (dark_ f k r) (Earth.comfort (Adic.field 2 k) [] (Mbit f k r)):=
  (noir k).back.split ((Aseal f k r).thenDo (Adopt.skip _).back)
noncomputable def CvB (f k r): Adopt (light_ f k r) (Earth.comfort (Adic.field 2 k) [] (Mbit f k r)):=
  (noir k).back.split ((Bseal f k r).thenDo (Adopt.skip _).back)
open Dusk
theorem curtainV (x):
    Curtain.induce (orderMW f k r) ((CvB f k r).cast x)=((CvA f k r).cast x):=
  Prod.ext rfl (Prod.ext (moved x.2) rfl)
theorem curtainW (x):
    Curtain.induce (orderMW f k r).symm ((CvA f k r).cast x)=(CvB f k r).cast x:=
  Prod.ext rfl (Prod.ext (moved' x.2) rfl)

end Atoll

end IntegerMultiplication
end Computability
end OAI
