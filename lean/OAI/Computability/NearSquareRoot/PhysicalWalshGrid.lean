import OAI.Computability.NearSquareRoot.PhysicalWalshChecked
import OAI.Computability.NearSquareRoot.KernelPassMixPhysical
import OAI.Computability.NearSquareRoot.KernelScaleBank

/-! # Rounded grid primitives on a shared row-bank header

The packet carries the address-count and record-width rulers for mixing and the
three shape rulers for producing the scale table. A fixed rearrangement places
the required header at the head of the work stack and restores the full header
with the result. Every primitive works on arbitrary admissible intermediate rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication Code Space PhysicalWalsh KernelPass

theorem easyWithin {X A B : Type} [Codec A] [Codec B] (b : X → ℕ) {f : A → B}
    (hf : Easy f) (x : X → A) (C : ℕ) (h : ∀ t, size (x t) ≤ C*(b t+1)) :
    BoundedTask b b (fun t => send (x t)) (fun t => send (f (x t))) := by
  apply (BoundedTask.of_time (hf.on x)).bound (C+1) (C+C+1) <;> intro t
  · rw [Nat.succ_mul]; have := h t; omega
  · change size (x t)+size (x t)+1 ≤ _
    rw [Nat.succ_mul, Nat.add_mul]; have := h t; omega

/-- Call a header-preserving primitive with a projection of a larger header. -/
theorem retain {X H K A B : Type} [Codec H] [Codec K] [Codec A] [Codec B] (budget : X → ℕ)
    (key : H → K) (select : Easy key) (header : X → H) (x : X → A) (y : X → B)
    (C D : ℕ) (hin : ∀ t, size (header t,x t) ≤ C*(budget t+1))
    (hout : ∀ t, size (header t,y t) ≤ D*(budget t+1))
    (inner : BoundedTask budget budget (fun t => send (key (header t),x t))
      (fun t => send (key (header t),y t))) :
    BoundedTask budget budget (fun t => send (header t,x t)) (fun t => send (header t,y t)) := by
  let frame {V : Type} (p : H × V) := ((key p.1, p.2),p.1)
  have fr {V : Type} [Codec V] : Easy (frame (V := V)) :=
    ((Easy.fst.compose select).pair Easy.snd).pair Easy.fst
  let restore (p : (K × B) × H) := (p.2,p.1.2)
  have er : Easy restore := Easy.snd.pair (Easy.fst.compose Easy.snd)
  have start := easyWithin budget (fr (V := A)) (fun t => (header t,x t)) C hin
  have saved := inner.left (fun t => send (header t))
  have middle : BoundedTask budget budget (fun t => send (frame (header t,x t)))
      (fun t => send (frame (header t,y t))) := by
    apply saved.bound 1 (C+2)
    · intro t; simp
    · intro t
      have hh := hin t
      simp only [size_prod] at hh
      change budget t + size (header t) + 1 ≤ (C+2)*(budget t+1)
      rw [Nat.add_mul]; omega
  obtain ⟨E,hE⟩ := (fr (V := B)).length
  have finish := easyWithin budget er (fun t => frame (header t,y t)) (E*D) (fun t =>
    (hE _).trans ((Nat.mul_le_mul_left E (hout t)).trans_eq (Nat.mul_assoc ..).symm))
  exact ((start.compose middle).compose finish).bound 3 1 (fun _ => by omega) (fun _ => by simp)

abbrev Header := (Tally × Tally) × (Tally × Tally) × Tally

variable {a q i o : ℕ} {U X F : Type} (L : KernelScaleBank.Layout a U F) (w : U → ℕ)

def header (u : U) : Header :=
  ((tally (L.rows u).length, tally (w u + 1)), KernelScaleBank.header L u)

def layout : Layout U Header (List Dusk.Pair) where
  Row u := F → Dusk.Grain (w u)
  header := header L w
  store u r := (L.rows u).map fun z => Dusk.mark (r z)

/-- Charge one pass over the address field and the complete fixed-width record. -/
def budget (u : U) := ((L.rows u).length+1)*(KernelScaleBank.width L u+w u+1)

/-- When the local address width fits one record, the scan allowance is
linear in the physical row volume, including short and singleton rows. -/
theorem budget_le_rowVolume (u : U) (hw : KernelScaleBank.width L u ≤ w u+1) :
    budget L w u ≤ 2 * (((L.rows u).length+1)*(w u+1)) := by
  rw [Nat.mul_left_comm 2]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem count_bounds (u : U) : L.prefixCount u ≤ (L.rows u).length ∧
    L.suffixCount u ≤ (L.rows u).length := by
  rw [KernelScaleBank.count_eq]
  have h := L.prefix_pos u
  have s := L.suffix_pos u
  have powpos : 0 < 2 ^ KernelScaleBank.width L u := pow_pos (by decide) _
  exact ⟨Nat.le_mul_of_pos_right _ (Nat.mul_pos powpos s),
    (Nat.le_mul_of_pos_left _ powpos).trans (Nat.le_mul_of_pos_left _ h)⟩

theorem fitsLayout {m : Meter U} (hm : ∀ u, 20*(budget L w u+1) ≤ m.arena u) :
    FitsLayout m (layout L w) := by
  constructor
  · intro u
    apply le_trans _ (hm u)
    have hN : (L.rows u).length+1 ≤ budget L w u := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hw : KernelScaleBank.width L u+w u+1 ≤ budget L w u := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hp := (count_bounds L u).1
    have hs := (count_bounds L u).2
    simp only [layout, header, KernelScaleBank.header, size_prod, size_tally,tally_length]
    omega
  · intro u x
    apply le_trans _ (hm u)
    have bound (l : List F) : size (l.map fun z => Dusk.mark (x z)) ≤ l.length*(4*(w u+1)+4)+1 := by
      induction l with
      | nil => simp
      | cons z l ih =>
        simp only [List.map_cons, List.length_cons, size_cons, Dusk.volume]
        rw [Nat.succ_mul l.length]; omega
    have V : (L.rows u).length*(w u+1) ≤ budget L w u := by
      apply Nat.mul_le_mul (Nat.le_succ _) (by omega)
    have N : (L.rows u).length+1 ≤ budget L w u := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    change size ((L.rows u).map _) ≤ _
    have h := bound (L.rows u)
    rw [Nat.mul_add, Nat.mul_left_comm _ 4] at h
    omega

private def unitMeter : Meter U where
  scan u := 20*(budget L w u+1)
  arena u := 20*(budget L w u+1)
  arena_le _ := le_rfl
  permit _ _ _ _ := True

theorem packet_bound {n : ℕ} (u : U) (x : Rows (layout L w) u n) :
    size (packet (layout L w) u x) ≤ ((n+3)*21)*(budget L w u+1) := by
  have fit : FitsLayout (unitMeter L w) (layout L w) := fitsLayout L w (fun _ => le_rfl)
  apply (fit.packet u x).trans
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  change 20*(budget L w u+1)+1 ≤ 21*(budget L w u+1)
  omega

/-- A nonempty input bank supplies its own address-count and record-width rulers.
Only the active-field shape header is required on entry. -/
def readHeader (p : ((Tally × Tally) × Tally) × List (List Dusk.Pair)) : Header × List (List Dusk.Pair) :=
  let r := p.2.headD []
  (((ruler r, ruler (r.headD ([],[])).1),p.1),p.2)

private theorem readHeader_easy : Easy readHeader := by
  let row := (fun p : ((Tally × Tally) × Tally) × List (List Dusk.Pair) => p.2.headD [])
  have first : Easy row := Easy.snd.compose (Iter.leader _)
  have record := first.compose (Iter.leader (([],[]) : Dusk.Pair))
  exact (((Easy.ruler first).pair (Easy.ruler (record.compose Easy.fst))).pair Easy.fst).pair Easy.snd

private theorem readHeader_eq {n : ℕ} (u : U) (x : Rows (layout L w) u (n+1)) :
    readHeader (KernelScaleBank.header L u,(packet (layout L w) u x).2) = packet (layout L w) u x := by
  have hn : 0 < (L.rows u).length := by
    rw [KernelScaleBank.count_eq]; exact Nat.mul_pos (L.prefix_pos _) (Nat.mul_pos (by positivity) (L.suffix_pos _))
  cases he : L.rows u with
  | nil => simp [he] at hn
  | cons z zs =>
    have rlen : ∀ (xs : List Dusk.Pair), ruler xs = tally xs.length := fun xs => by
      simpa only [ruler_length] using (recover_tally (ruler xs)).symm
    simp [readHeader,packet,layout,header,List.ofFn_succ,he,rlen,Dusk.mark]
    simp [ruler,tally,Dusk.trip_length,List.replicate_succ]

theorem readHeader_bounded {n : ℕ} (u : X → U) (x : ∀ t, Rows (layout L w) (u t) (n+1)) :
    BoundedTask (budget L w ∘ u) (budget L w ∘ u)
      (fun t => send (KernelScaleBank.header L (u t),(packet (layout L w) (u t) (x t)).2))
      (fun t => send (packet (layout L w) (u t) (x t))) := by
  let d t := (KernelScaleBank.header L (u t),(packet (layout L w) (u t) (x t)).2)
  have size_d (t : X) : size (d t) ≤ ((n+1+3)*21)*(budget L w (u t)+1) := by
    apply le_trans _ (packet_bound L w (u t) (x t))
    simp only [d,packet,layout,header,size_prod]; omega
  have easy := easyWithin (budget L w ∘ u) readHeader_easy d _ size_d
  exact easy.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun t => congrArg send (readHeader_eq L w _ (x t)))

def mix (c : Fin o → Fin i → Coefficient) (u : U) (x : Rows (layout L w) u i) : Rows (layout L w) u o :=
  fun b z => KernelPassMix.rounded (c b) (fun j => x j z)

def mixFits (c : Fin o → Fin i → Coefficient) (u : U) (x : Rows (layout L w) u i) : Prop :=
  ∀ z ∈ L.rows u, ∀ b, Grid.focus (w u) (Grid.divA (KernelPassMix.denom (c b))
    (KernelPassMix.accum (c b) (Grid.aspect ∘ (fun j => x j z))))

theorem mix_bounded (c : Fin o → Fin i → Coefficient) (u : X → U)
    (x : ∀ t, Rows (layout L w) (u t) i) (room : ∀ t, mixFits L w c (u t) (x t)) :
    BoundedTask (budget L w ∘ u) (budget L w ∘ u)
      (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (mix L w c (u t) (x t)))) := by
  have core := KernelPassMix.mixHeaderBoundedTask c (fun t => L.rows (u t)) (w ∘ u)
    (fun t z j => x t j z) room
  let out := fun t => mix L w c (u t) (x t)
  let p := fun t => packet (layout L w) (u t) (x t)
  let r := fun t => packet (layout L w) (u t) (out t)
  apply retain (budget L w ∘ u) Prod.fst Easy.fst (fun t => header L w (u t))
    (fun t => (p t).2) (fun t => (r t).2) _ _ (fun t => packet_bound L w _ _) (fun t => packet_bound L w _ _)
  apply core.mono <;> intro t <;> exact Nat.mul_le_mul_left _ (by simp [Function.comp_apply])

def scale (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : U) (x : (layout L w).Row u) : (layout L w).Row u := fun z =>
  KernelScaleRecord.rounded (table (KernelScaleBank.signature L test u z)) (x z)

def scaleFits (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : U) (x : (layout L w).Row u) : Prop :=
  ∀ z ∈ L.rows u, KernelScaleRecord.fits (table (KernelScaleBank.signature L test u z)) (x z)

def reindex (u : X → U) : KernelScaleBank.Layout a X F where
  h := L.h ∘ u
  prefixCount := L.prefixCount ∘ u
  suffixCount := L.suffixCount ∘ u
  prefix_pos t := L.prefix_pos (u t)
  suffix_pos t := L.suffix_pos (u t)
  rows := L.rows ∘ u
  coord t := L.coord (u t)
  address_order t := L.address_order (u t)

theorem scale_bounded (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : X → U) (x : ∀ t, Rows (layout L w) (u t) 1)
    (room : ∀ t, scaleFits L w test table (u t) (x t 0)) :
    BoundedTask (budget L w ∘ u) (budget L w ∘ u)
      (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => scale L w test table (u t) (x t 0)))) := by
  let out := fun t (_ : Fin 1) => scale L w test table (u t) (x t 0)
  let p := fun t => packet (layout L w) (u t) (x t)
  let r := fun t => packet (layout L w) (u t) (out t)
  apply retain (budget L w ∘ u) Prod.snd Easy.snd (fun t => header L w (u t))
    (fun t => (p t).2) (fun t => (r t).2) _ _ (fun t => packet_bound L w _ _) (fun t => packet_bound L w _ _)
  have core := KernelScaleBank.scaleBank_bounded (reindex L u) test table (w ∘ u) (fun t => x t 0) room
  apply (core.mono (time' := budget L w ∘ u) (space' := budget L w ∘ u)
    (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ _)) (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ _))).conform
    (fun _ => rfl) (fun _ => rfl) <;> intro t <;>
      simp [p,r,layout,packet,KernelScaleBank.bank,KernelScaleBank.output,reindex,header,KernelScaleBank.header,
        KernelScaleBank.width,Function.comp_def,List.ofFn_succ,out,scale,KernelScaleBank.signature]
  rfl

section
variable {m : Meter U} (hb : ∀ u, budget L w u ≤ m.arena u)
include hb

theorem mix_open (c : Fin o → Fin i → Coefficient) (u : X → U) (x : ∀ t, Rows (layout L w) (u t) i)
    (room : ∀ t, mixFits L w c (u t) (x t)) :
    OpenRun m 0 u (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (mix L w c (u t) (x t)))) :=
  OpenRun.closed ((mix_bounded L w c u x room).mono (fun t => (hb (u t)).trans (m.arena_le _)) (fun t => hb (u t)))

theorem scale_open (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : X → U) (x : ∀ t, Rows (layout L w) (u t) 1)
    (room : ∀ t, scaleFits L w test table (u t) (x t 0)) :
    OpenRun m 0 u (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => scale L w test table (u t) (x t 0)))) :=
  OpenRun.closed ((scale_bounded L w test table u x room).mono (fun t => (hb (u t)).trans (m.arena_le _)) (fun t => hb (u t)))

end
end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
