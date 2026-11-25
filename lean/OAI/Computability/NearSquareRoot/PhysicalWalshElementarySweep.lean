import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryOrdinal
import OAI.Computability.NearSquareRoot.PhysicalWalshElementarySchedule
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO
import OAI.Computability.NearSquareRoot.PhysicalWalshSequence
import OAI.Computability.NearSquareRoot.PhysicalWalshFrameScan

/-! # Walking the bit-pair schedule on a single physical row

Only one cut pair is expanded at a time. The compact remaining agenda and
the current record row share the same arena throughout all passes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementarySweep

open IntegerMultiplication Code Space PhysicalWalsh Strip Staff Carry
open ElementarySchedule (slotWidth agenda compact pref gap suff)
open ElementaryGate (natAction Bits2)

private theorem relabel {I H K X : Type} [Codec H] [Codec K] [Codec X] (v : I → ℕ)
    (h : I → H) (k : I → K) (x y : I → X)
    (prep : BoundedTask v v (send ∘ h) (send ∘ k))
    (stage : BoundedTask v v (fun i => send (k i,x i)) (fun i => send (k i,y i))) :
    BoundedTask v v (fun i => send (h i,x i)) (fun i => send (h i,y i)) := by
  have body := framePrepare h k k x y prep prep stage
  obtain ⟨C,hC⟩ := body.endpointSize
  let endPacket (z : (K × H) × X) := (z.1.2,z.2)
  have e : Easy endPacket := (Easy.fst.compose Easy.snd).pair Easy.snd
  have close := PhysicalWalshGrid.easyWithin v e (fun i => ((k i,h i),y i)) C
    (fun i => (Nat.le_max_right ..).trans (hC i))
  exact (body.compose close).bound 2 1 (fun _ => by omega) (fun _ => by simp)

variable {a W : ℕ} (src dst : Fin (a+1))

private def N (s : Shape) := groups W s * inner (a+1) s

private def records (s : Shape) := (N (a:=a) (W:=W) s+1)*(4*(s.w+1)+4)+1

private theorem row_size (s : Shape) (x : Data s) : size (laneFlat (a+1) W s x) ≤ records (a:=a) (W:=W) s := by
  rw [laneFlat,← List.map_map,PhysicalWalsh.Padding.marks_size,List.length_map,List.length_range]
  unfold records N
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_succ _)) _

private theorem count_le (s : Shape) : N (a:=a) (W:=W) s ≤ count (a+1) s :=
  Nat.mul_le_mul_right _ (max_le s.pref_pos (Nat.div_le_self ..))

private theorem records_le (s : Shape) : records (a:=a) (W:=W) s ≤ 9*((count (a+1) s+1)*(s.w+1)) := by
  unfold records
  have h := count_le (a:=a) (W:=W) s
  calc
    _ ≤ (count (a+1) s+1)*(4*(s.w+1)+4)+1 := by gcongr
    _ ≤ _ := by ring_nf; omega

private theorem gate_area {P G B : ℕ} (hp : 0<P) (hg : 0<G) (hb : 0<B) :
    (P+1)*(G+1)*(B+1) ≤ 2*(P*2*G*2*B) := by
  calc
    _ ≤ (2*P)*(2*G)*(2*B) := by gcongr <;> omega
    _ = _ := by ring

private def prefixAgenda (W : ℕ) (steps : Shape → ℕ) (s : Shape) := (agenda W src dst s).take (steps s)

private theorem prefix_length (W : ℕ) (steps : Shape → ℕ) (cap : ∀ s, steps s ≤ slotWidth (a+1) s) (s : Shape) :
    (prefixAgenda src dst W steps s).length = steps s := by simp [prefixAgenda,min_eq_left (cap s)]

private theorem prefix_get (W : ℕ) (steps : Shape → ℕ) (s : Shape) (j : Fin (prefixAgenda src dst W steps s).length) :
    (prefixAgenda src dst W steps s).get j = compact W src dst s j := by
  change ((agenda W src dst s).take (steps s))[j.val] = _
  rw [List.getElem_take]
  simp only [agenda,List.getElem_ofFn]

private theorem prefix_bounded (W : ℕ) (steps : Shape → ℕ) (known : Realizes (Header.regime (a+1)) steps) :
    ∃ e D : ℕ, let b s := D*(Header.scale (a+1) s+1)^e
    BoundedTask b b (send ∘ Header.wire (a+1)) (send ∘ prefixAgenda src dst W steps) ∧
    ∀ s, size (prefixAgenda src dst W steps s) ≤ b s := by
  let r := Header.regime (a+1)
  have made := (known.pair (ElementarySchedule.agenda_has W src dst)).ez
    ((easy_cut (Easy.identity (X:=Tally × List ElementarySchedule.Words))).compose Easy.fst)
  have pack : r.Has (prefixAgenda src dst W steps) := by
    change (Header.regime (a+1)).Has fun s => (agenda W src dst s).take (steps s)
    simpa only [cutLists,id_eq,tally_length,Function.comp_apply,Staff.box] using made
  have sz := Strip.Regime.Small.extent pack
  obtain ⟨t,dt,prog⟩ := pack
  obtain ⟨e,D,dom⟩ := (r.gauge.add dt).add sz
  refine ⟨e,D,(BoundedTask.of_time prog).mono ?_ ?_,?_⟩ <;> intro s <;>
    have h := dom s <;> change (r.header s).count+t s+size (prefixAgenda src dst W steps s) ≤ D*(r.scale s+1)^e at h <;>
    change _ ≤ D*(r.scale s+1)^e <;> dsimp only at * <;> omega

/-- The local workspace polynomial is added to the stream rather than to
each record. The time for all passes sums their individual scan allowances. -/
theorem sweepPrefix (W : ℕ) (ne : src ≠ dst) (σ : Bits2 → Bits2)
    (steps : Shape → ℕ) (known : Realizes (Header.regime (a+1)) steps) (cap : ∀ s, steps s ≤ slotWidth (a+1) s)
    (state : (t : XorInput W) → ℕ → Data t.shape)
    (step : ∀ (t : XorInput W) (j : Fin (steps t.shape)) n,
      state t (j.val+1) n =
        state t j (natAction (gap src dst t.shape j) (suff src dst t.shape j) σ n)) :
    ∃ d C : ℕ,
      let space s := C*(Header.scale (a+1) s+1)^d + (count (a+1) s+1)*(s.w+1)
      BoundedTask (fun t : XorInput W => (steps t.shape+1)*(space t.shape+1))
        (fun t => space t.shape)
        (fun t => send (Header.wire (a+1) t.shape,laneFlat (a+1) W t.shape (state t 0)))
        (fun t => send (laneFlat (a+1) W t.shape (state t (steps t.shape)))) := by
  obtain ⟨e,D,make,agendaSize⟩ := prefix_bounded src dst W steps known
  obtain ⟨f,F,ticket⟩ := ElementarySchedule.cuts_bounded W ne
  let d := max e f
  let C := D+F+1
  let setup (s : Shape) := C*(Header.scale (a+1) s+1)^d
  let space (s : Shape) := setup s + (count (a+1) s+1)*(s.w+1)
  have setupDom (s : Shape) (g H : ℕ) (hg : g ≤ d) (hH : H ≤ C) :
      H*(Header.scale (a+1) s+1)^g ≤ setup s :=
    Nat.mul_le_mul hH (Nat.pow_le_pow_right (Nat.succ_pos _) hg)
  have largeE s := setupDom s e D (le_max_left ..) (by dsimp [C]; omega)
  have largeF s := setupDom s f F (le_max_right ..) (by dsimp [C]; omega)
  have hrows (s : Shape) (x : Data s) : size (laneFlat (a+1) W s x) ≤ 9*space s := by
    exact (row_size s x).trans ((records_le s).trans (Nat.mul_le_mul_left 9 (Nat.le_add_left ..)))
  let s (t : XorInput W) := t.shape
  let planList (t : XorInput W) := prefixAgenda src dst W steps (s t)
  let rows (t : XorInput W) (j : ℕ) := laneFlat (a+1) W (s t) (state t j)
  let X := (t : XorInput W) × Fin (planList t).length
  have dur (t : XorInput W) : (planList t).length = steps (s t) := prefix_length src dst W steps cap (s t)
  let k (z : X) : Fin (steps (s z.1)) := ⟨z.2, (dur z.1) ▸ z.2.isLt⟩
  let j (z : X) : Fin (slotWidth (a+1) (s z.1)) := (k z).castLE (cap _)
  let v (z : X) := space (s z.1)
  let sub (z : X) := (⟨⟨s z.1,z.1.positive⟩,j z⟩ :
    (q : {s : Shape // 0<s.level}) × Fin (slotWidth (a+1) q.val))
  let P (z : X) := pref W src dst (s z.1) (j z)
  let G (z : X) := gap src dst (s z.1) (j z)
  let B (z : X) := suff src dst (s z.1) (j z)
  let inrow (z : X) := rows z.1 z.2
  let outrow (z : X) := rows z.1 (z.2.val+1)
  let top (z : X) := (planList z.1).get z.2
  let ruler (z : X) := ElementaryGate.header (P z) (G z) (B z)
  have head_eq (z : X) : top z = compact W src dst (s z.1) (j z) :=
    prefix_get src dst W steps (s z.1) z.2
  have dims (z : X) : P z*2*G z*2*B z = N (a:=a) (W:=W) (s z.1) :=
    ElementarySchedule.gate_count W ne _ z.1.positive (j z)
  have area (z : X) : (P z+1)*(G z+1)*(B z+1) ≤ 2*space (s z.1) := by
    have hp : 0<P z := Nat.mul_pos (Nat.zero_lt_one.trans_le (Nat.le_max_left ..)) (Nat.two_pow_pos _)
    have hg : 0<G z := Nat.two_pow_pos _
    have hb : 0<B z := Nat.mul_pos (Nat.two_pow_pos _) (s z.1).suff_pos
    have fit := gate_area hp hg hb
    rw [dims] at fit
    have cn := count_le (a:=a) (W:=W) (s z.1)
    have room : count (a+1) (s z.1) + 1 ≤ (count (a+1) (s z.1)+1)*((s z.1).w+1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    dsimp only [space]; omega
  have cuts : BoundedTask v v (send ∘ top) (send ∘ ruler) := by
    have pass := ticket.on sub
    have sizeCuts (z : X) : F*(Header.scale (a+1) (s z.1)+1)^f + N (a:=a) (W:=W) (s z.1) ≤ v z := by
      apply Nat.add_le_add (largeF _)
      exact (count_le _).trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    exact (pass.mono sizeCuts sizeCuts).conform (fun _ => rfl) (fun _ => rfl) (fun z => congrArg send (head_eq z).symm) (fun _ => rfl)
  let read (z : X) := Dusk.mark ∘ state z.1 z.2
  have gate := ElementaryGate.boundedOrdinal σ P G B read
  have inp (z : X) : (List.range (P z*2*G z*2*B z)).map (read z) = inrow z := by rw [dims]; rfl
  have out (z : X) : (List.range (P z*2*G z*2*B z)).map (read z ∘ natAction (G z) (B z) σ) = outrow z := by
    rw [dims]; apply List.map_congr_left
    intro n _
    exact congrArg Dusk.mark (step z.1 (k z) n).symm
  have charged (z : X) : ElementaryGate.budget (P z) (G z) (B z)
      (size ((List.range (P z*2*G z*2*B z)).map (read z))) + 1 ≤ 12*(v z+1) := by
    rw [inp]; have room := hrows (s z.1) (state z.1 z.2)
    change size (inrow z) ≤ 9 * v z at room
    have fit := area z
    change _ ≤ 2*v z at fit
    unfold ElementaryGate.budget; omega
  have prog : BoundedTask v v (fun z => send (ruler z,inrow z)) (fun z => send (ruler z,outrow z)) :=
    (gate.bound 12 12 charged charged).conform (fun _ => rfl) (fun _ => rfl)
      (fun z => congrArg (fun q => send (ruler z,q)) (inp z)) (fun z => congrArg (fun q => send (ruler z,q)) (out z))
  have piece := relabel v top ruler inrow outrow cuts prog
  let arena (t : XorInput W) := 9*space (s t)
  have walk := Sequence.walk planList rows (fun t _ => space (s t)) arena
    (fun t j _ => hrows (s t) (state t j)) (piece.mono (fun _ => le_rfl)
      (fun z => Nat.le_mul_of_pos_left (v z) (by decide : 0<9)))
  have build := (make.on s).left (fun t => send (rows t 0))
  have run := build.compose walk
  refine ⟨d,C,?_⟩
  let clock (t : XorInput W) := (steps (s t)+1)*(space (s t)+1)
  have head (t : XorInput W) : size (planList t) ≤ space (s t) := (agendaSize _).trans ((largeE _).trans (Nat.le_add_right ..))
  have init (t : XorInput W) : D*(Header.scale (a+1) (s t)+1)^e ≤ space (s t) := (largeE _).trans (Nat.le_add_right ..)
  apply (run.bound (time' := clock) (space' := space ∘ s) 15 11 ?_ ?_).conform
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun t => congrArg (fun n => send (rows t n)) (dur t))
  · intro t
    dsimp only [arena,Function.comp_apply]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, dur]
    have hAgenda := head t
    have b := init t
    have wall (x y z l : ℕ) (hx : x ≤ z) (hy : y ≤ z) :
        x + (y+9*z+1 + l*(z+(y+9*z)+1))+1 ≤ 15*((l+1)*(z+1)+1) := by
      have h := Nat.mul_le_mul_left l hy
      ring_nf at h ⊢; omega
    exact wall _ _ _ _ b hAgenda
  · intro t
    have hAgenda := head t
    have b := init t
    have c := hrows (s t) (state t 0)
    change size (rows t 0) ≤ 9*space (s t) at c
    change max (_+size (rows t 0)) (size (planList t)+9*space (s t))+1 ≤ 11*(space (s t)+1)
    omega

/-- Complete the aligned slot by applying the entire compact agenda. -/
theorem sweep (W : ℕ) (ne : src ≠ dst) (σ : Bits2 → Bits2)
    (state : (t : XorInput W) → ℕ → Data t.shape)
    (step : ∀ (t : XorInput W) (j : Fin (slotWidth (a+1) t.shape)) n,
      state t (j.val+1) n =
        state t j (natAction (gap src dst t.shape j) (suff src dst t.shape j) σ n)) :
    ∃ d C : ℕ,
      let space s := C*(Header.scale (a+1) s+1)^d + (count (a+1) s+1)*(s.w+1)
      BoundedTask (fun t : XorInput W => (slotWidth (a+1) t.shape+1)*(space t.shape+1))
        (fun t => space t.shape)
        (fun t => send (Header.wire (a+1) t.shape,laneFlat (a+1) W t.shape (state t 0)))
        (fun t => send (laneFlat (a+1) W t.shape (state t (slotWidth (a+1) t.shape)))) :=
  sweepPrefix src dst W ne σ (slotWidth (a+1)) (Header.childBits (a+1) (Nat.succ_pos _)) (fun _ => le_rfl) state step

end PhysicalWalshNode.ElementarySweep

end NearSquareRoot
end Computability
end OAI
