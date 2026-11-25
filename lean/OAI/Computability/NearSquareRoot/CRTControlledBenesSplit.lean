import OAI.Computability.NearSquareRoot.CRTControlledBenesRaw
import Mathlib.Data.List.OfFn

/-! # Correctness of recursive splitting on raw Beneš tables

Filtering the physical table can change the enumeration order of the child addresses.
The table invariant accepts every complete duplicate-free order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes

def RawRepresents {d : ℕ} (p : Equiv.Perm (Word d)) (t : RawTable) : Prop :=
  ∃ ks : List (Word d), ks.Nodup ∧ (∀ x, x ∈ ks) ∧
    t = ks.map (fun x => (List.ofFn x, List.ofFn (p x)))

/-- The switch setting read from a padded table at one logical tail. -/
def rawControl {d : ℕ} (t : RawTable) (side : Bool) (x : Word d) : Bool :=
  (label (rawLabels t) (side,List.ofFn x)).2

private abbrev consPort {d : ℕ} : Bool × Word d ≃ Word (d+1) :=
  Fin.consEquiv (fun _ : Fin (d+1) => Bool)

private def portGraph {d : ℕ} (p : Equiv.Perm (Bool × Word d)) (x : Bool × Word d) :
    List Bool × List Bool :=
  (x.1 :: List.ofFn x.2, (p x).1 :: List.ofFn (p x).2)

/-- Put the logical table enumeration into switch-bit/tail coordinates. -/
private theorem in_ports {d : ℕ} (p : Equiv.Perm (Word (d+1))) (t : RawTable)
    (h : RawRepresents p t) :
    let P := (consPort.trans p).trans consPort.symm
    ∃ zs : List (Bool × Word d), zs.Nodup ∧ (∀ z, z ∈ zs) ∧ t = zs.map (portGraph P) := by
  obtain ⟨ks,hk,ha,rfl⟩ := h
  refine ⟨ks.map consPort.symm, hk.map consPort.symm.injective, ?_, ?_⟩
  · intro z
    exact List.mem_map.mpr ⟨consPort z,ha _,consPort.symm_apply_apply z⟩
  · rw [List.map_map]
    apply List.map_congr_left
    intro v _
    change (List.ofFn v,List.ofFn (p v)) =
      ((consPort.symm v).1 :: List.ofFn (consPort.symm v).2,
        (consPort.symm (p (consPort (consPort.symm v)))).1 ::
          List.ofFn (consPort.symm (p (consPort (consPort.symm v)))).2)
    rw [Equiv.apply_symm_apply]
    exact Prod.ext List.ofFn_succ List.ofFn_succ

private theorem bool_lanes {A : Type} [Finite A] (p : Equiv.Perm (Bool × A))
    (l r : A → Bool) (h : ∀ x, (x.1 ^^ l x.2) = ((p x).1 ^^ r (p x).2)) :
    ∃ q : Bool → Equiv.Perm A, ∀ x,
      p x = port r (x.1 ^^ l x.2, q (x.1 ^^ l x.2) x.2) := by
  let q (b : Bool) (x : A) := (p (b ^^ l x,x)).2
  have first (b : Bool) (x : A) : (p (b ^^ l x,x)).1 = (b ^^ r (q b x)) := by
    have hc := h (b ^^ l x,x)
    change ((b ^^ l x) ^^ l x) = ((p (b ^^ l x,x)).1 ^^ r (q b x)) at hc
    have hf := congrArg (· ^^ r (q b x)) hc
    simpa using hf.symm
  have qi (b : Bool) : Function.Injective (q b) := by
    intro x y hxy
    have he : p (b ^^ l x,x) = p (b ^^ l y,y) := by
      apply Prod.ext _ hxy
      rw [first, first, hxy]
    exact congrArg Prod.snd (p.injective he)
  refine ⟨fun b => Equiv.ofBijective (q b) ⟨qi b,Finite.surjective_of_injective (qi b)⟩,?_⟩
  rintro ⟨b,x⟩
  apply Prod.ext
  · simpa [port,q] using first (b ^^ l x) x
  · simp [port,q,Equiv.ofBijective_apply]

private theorem selected_keys {A : Type*} (zs : List (Bool × A)) (hd : zs.Nodup)
    (ha : ∀ z, z ∈ zs) (c : A → Bool) (b : Bool) :
    let l := zs.filter fun z => decide ((z.1 ^^ c z.2) = b)
    (l.map Prod.snd).Nodup ∧ ∀ a, a ∈ l.map Prod.snd := by
  constructor
  · apply List.Nodup.map_on _ (hd.filter _)
    intro x hx y hy he
    have hx' := of_decide_eq_true (List.mem_filter.mp hx).2
    have hy' := of_decide_eq_true (List.mem_filter.mp hy).2
    rw [he] at hx'
    exact Prod.ext (by simpa using congrArg (· ^^ c y.2) (hx'.trans hy'.symm)) he
  · intro a
    refine List.mem_map.mpr ⟨(b ^^ c a,a),List.mem_filter.mpr ⟨ha _,?_⟩,rfl⟩
    simp

/-- The filter/project procedure implements the two recursive permutations.
Its factorization reads the outer switches from the very same raw table. -/
theorem raw_split_correct {d : ℕ} (p : Equiv.Perm (Word (d+1))) (t : RawTable)
    (ht : RawRepresents p t) :
    ∃ q : Bool → Equiv.Perm (Word d),
      (∀ b, RawRepresents (q b) (childTable t b)) ∧
      ∀ (b : Bool) (x : Word d),
        let lane := b ^^ rawControl t false x
        let y := q lane x
        p (Fin.cons b x) = Fin.cons (lane ^^ rawControl t true y) y := by
  let P := (consPort.trans p).trans consPort.symm
  obtain ⟨zs,hd,ha,hz⟩ := in_ports p t ht
  change t = zs.map (portGraph P) at hz
  let left := rawControl (d:=d) t false
  let right := rawControl (d:=d) t true
  have hentries : t.map unconsRow = zs.map (fun z =>
      (indexedPort List.ofFn z, indexedPort List.ofFn (P z))) := by
    rw [hz, List.map_map]
    rfl
  have hcolor (z : Bool × Word d) : (z.1 ^^ left z.2) = ((P z).1 ^^ right (P z).2) := by
    have H := tapeColors_correct List.ofFn List.ofFn_injective P zs ha z
    unfold left right rawControl rawLabels
    rw [hentries]
    exact H
  obtain ⟨q,hq⟩ := bool_lanes P left right hcolor
  refine ⟨q,?_,?_⟩
  · intro b
    let pick (z : Bool × Word d) := decide ((z.1 ^^ left z.2) = b)
    let sel := zs.filter pick
    have H := selected_keys zs hd ha left b
    refine ⟨sel.map Prod.snd, H.1,H.2, ?_⟩
    let test (row : List Bool × List Bool) :=
      decide ((row.1.headD false ^^ (label (rawLabels t) (false,row.1.tail)).2) = b)
    change (t.filter test).map _ = _
    rw [hz]
    simp only [List.filter_map, List.map_map]
    change (zs.filter pick).map _ = (zs.filter pick).map _
    apply List.map_congr_left
    intro z h
    have hz' := of_decide_eq_true (List.mem_filter.mp h).2
    change (z.1 ^^ left z.2) = b at hz'
    have ho := congrArg Prod.snd (hq z)
    change (P z).2 = q (z.1 ^^ left z.2) z.2 at ho
    rw [hz'] at ho
    change (List.ofFn z.2, List.ofFn (P z).2) = (List.ofFn z.2, List.ofFn (q b z.2))
    rw [ho]
  · intro b x
    have he := congrArg consPort (hq (b,x))
    change consPort (consPort.symm (p (consPort (b,x)))) = _ at he
    rw [Equiv.apply_symm_apply] at he
    exact he

end Benes

end NearSquareRoot
end Computability
end OAI
