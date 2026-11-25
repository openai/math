import OAI.Computability.IntegerMultiplication.Adic.Drive

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Code IntegerMultiplication.Port Strip
variable {p : ℕ} [NeZero p] (hp : 2 ≤ p)
variable {I : Type} {r : Regime I} (j : I→ℕ) {C : I → Type} (s : (i:I) → Series (C i))
variable (h : Regime.Has r (tally ∘ j)) (hs : Station r s)
variable {l : I→ℕ}
abbrev stations := fun i => (line p (j i)).cart (s i)
abbrev luggage := fun i => p^j i * (s i).count

-- group suffix data then ungroup. arbitrary D→D permutation implemented on axis (with controllers from header)
include hp h hs in
omit [NeZero p] in
theorem orchestrate (e : ∀ i,(Block p (j i))→(Block p (j i)))
    (v : (i:I)→Block p (j i) × C i→Tree)
    (known : Alive r (luggage (p:=p) j s) l (stackRun (stations j s) v))
    (port : ∀ (v : (i:I)→Block p (j i)→Tree),
      Alive r (luggage (p:=p) j s) l (stackRun (fun i => line p (j i)) v) →
      Drive r (luggage (p:=p) j s) l (stackRun (fun i => line p (j i)) v)
        (stackRun (fun i => line p (j i)) fun i x => v i (e i x))) :
    Drive r (luggage (p:=p) j s) l (stackRun (stations j s) v)
        (stackRun (stations j s) fun i x => v i (e i x.1,x.2)) := by
  let t i := line p (j i)
  let n i := (t i).count*(s i).count
  have q := terminal hp j h
  have u i : (t i).count*(s i).count = luggage (p:=p) j s i := by simp only [t,lineSize,luggage]
  have ns i : (t i).count ≤ luggage (p:=p) j s i := (u i) ▸ Nat.le_mul_of_pos_right _ (hs.1 i)
  have nt i : (s i).count ≤ luggage (p:=p) j s i := (u i) ▸ Nat.le_mul_of_pos_left _ (q.1 i)
  have pn i := (q.1 i).trans (ns i)
  let input := stackRun (stations j s) v
  have f := Drive.fetch pn known
  have hz := Rip.carve t s v
    (f.chain ((Station.supply q ns).twice (Station.supply hs nt)))
    (Drive.self pn known) q.1 hs.1 (fun i => (u i).le)
  exact Rip.flatten t s (fun i x => v i (e i x.1,x.2)) (Drive.pipe hz (port _ hz.idle))

noncomputable section
include hp h hs in
theorem sail (a : Span p) (v : (i:I)→Block p (j i) × C i→Tree)
    (known : Alive r (luggage (p:=p) j s) l (stackRun (stations j s) v)) :
    Drive r (luggage (p:=p) j s) l (stackRun (stations j s) v)
        (stackRun (stations j s) fun i x => v i ((sweep a (j i)).symm x.1,x.2)) :=
  orchestrate hp j s h hs _ v known
    (dilation hp j h (fun i => Nat.le_mul_of_pos_right _ (hs.1 i)) a)

theorem easy_apply (b : Pinpoint p) :
    Easy (fun (x : Raw p) => b.elim (no x) (fun a => applyScale a x)) := by
  cases b
  · exact easy_no easy_id
  exact easy_scale _ easy_id

variable {j' : ℕ}
def glide (o : Tower p j') := (swift Nug.one Nug.one o)
@[simp] theorem move_nat (o : Tower p j') (x : Block p j') :
    index p j' (glide o x) = index p j' x + o := by
  rw [glide,arrive]
  simp [slide]

/- Gathering from a control (earlier field's digits communicated in LSD
order) to this contiguous axis; prefix applied later. -/
include hp h hs in
theorem takeOff (b : Pinpoint p)
    (signal : I→Raw p) (y : (i:I)→Tower p (j i)) (_sig : ∀ i,Holds (j i) (signal i) (y i)) (_hg : r.Has signal)
    (v : (i:I)→Block p (j i) × C i→Tree)
    (_known : Alive r (luggage (p:=p) j s) l (stackRun (stations j s) v)) :
    Drive r (luggage (p:=p) j s) l (stackRun (stations j s) v)
        (stackRun (stations j s) fun i x => v i ((glide (b.stamp (j i)*y i)).symm x.1,x.2)) := by
  let w := fun i => b.elim (no (signal i)) (fun a => applyScale a (signal i))
  have z i : Holds (j i) (w i) (b.stamp (j i)*y i) := by
    cases b with
    | none =>
      simp only [Pinpoint.none,zero_mul]
      simpa [w,no] using sum 0 0 0 (by decide) (_sig i) (_sig i)
    | some c => exact scaled c (_sig i)
  exact orchestrate hp j s h hs _ v _known (fun v =>
    motion hp j h (fun i => Nat.le_mul_of_pos_right _ (hs.1 i))
      Nug.one Nug.one w _ (_hg.ez (easy_apply _)) z v)
end
end Adic

end IntegerMultiplication
end Computability
end OAI
