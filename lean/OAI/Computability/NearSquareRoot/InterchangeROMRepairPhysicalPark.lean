import OAI.Computability.NearSquareRoot.InterchangeROMRoute
import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveCell

/-! # Parking ground repair rows on the P192 deck

One fixed command peels a row off the bank under its common header. A
compiled sequence saves a prefix on register one, runs the active operation
on the suffix and reinstates the prefix in its original order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM.Parking

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters

private def below (c : Cmd) : Cmd := splitRoot 0 (fun _ => .pass)
  ((move 0 2 3).join (c.join ((move 2 0 3).join (pack 0))))

private def save : Cmd := below (splitRoot 0 (fun _ => .pass) (move 0 1 3))
private def restore : Cmd := below ((move 1 0 3).join (pack 0))

def parkPrefix : ℕ → Cmd → Cmd
  | 0, c => c
  | n+1, c => save.join ((parkPrefix n c).join restore)

private theorem below_within {R : ℕ} (hR : 4 ≤ R) {c : Cmd} (hc : Within R c) : Within R (below c) :=
  split_within (by omega) (fun _ => trivial) ⟨move_within (by omega) (by omega) (by omega),
    hc, move_within (by omega) (by omega) (by omega), (by omega : 0 < R)⟩

theorem parkPrefix_within {R : ℕ} (hR : 4 ≤ R) {c : Cmd} (hc : Within R c) (k : ℕ) :
    Within R (parkPrefix k c) := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    exact ⟨below_within hR (split_within (by omega) (fun _ => trivial)
      (move_within (by omega) (by omega) (by omega))), ih,
      below_within hR ⟨move_within (by omega) (by omega) (by omega), (by omega : 0 < R)⟩⟩

private theorem below_fits (h u v : Tree) (c : Cmd) (t : ℕ) (env : Env) (r s : Deck)
    (run : Fits env c (pile 0 u (pile 2 h r)) (pile 0 v (pile 2 h s)) t) :
    Fits env (below c) (pile 0 (.fork h u) r) (pile 0 (.fork h v) s) (84*h.count+t+11) := by
  have a := fits_move (i:=0) (u:=3) (j:=2) (by decide) (by decide) h env (pile 0 u r)
  have b := fits_move (i:=2) (u:=3) (j:=0) (by decide) (by decide) h env (pile 0 v s)
  rw [pile_comm 2 _ _ 0 _ (by decide)] at a b
  exact (fits_pair (a.join (run.join (b.join (fits_pack _ _ _ _ _))))).mono (by omega)

private theorem save_fits (h y : Tree) (xs : List Tree) (env : Env) (r : Deck) :
    Fits env save (pile 0 (packet h (y::xs)) r) (pile 0 (packet h xs) (pile 1 y r))
      (84*h.count + (42*y.count+4) + 11) := by
  apply below_fits
  have a := fits_move (i:=0) (j:=1) (u:=3) (by decide) (by decide) y env
    (pile 0 (Task.forest id xs) (pile 2 h r))
  rw [pile_comm 1 _ _ 0 _ (by decide),pile_comm 1 _ _ 2 _ (by decide)] at a
  exact fits_pair a

private theorem restore_fits (h y : Tree) (xs : List Tree) (env : Env) (r : Deck) :
    Fits env restore (pile 0 (packet h xs) (pile 1 y r)) (pile 0 (packet h (y::xs)) r)
      (84*h.count + (42*y.count+3) + 11) := by
  apply below_fits
  have a := fits_move (i:=1) (j:=0) (u:=3) (by decide) (by decide) y env
    (pile 0 (Task.forest id xs) (pile 2 h r))
  rw [pile_comm 1 _ _ 0 _ (by decide),pile_comm 1 _ _ 2 _ (by decide)] at a
  exact a.join (fits_pack _ _ _ _ _)

set_option maxRecDepth 8192 in
private theorem prefix_bounded (ys xs zs : List Tree) (h : Tree) (c : Cmd) (env : Env) (t S D V : ℕ)
    (run : ∀ r base, DeckCap base r → BoundedFits env c (pile 0 (packet h xs) r)
      (pile 0 (packet h zs) r) t (base+S) D)
    (hi : (packet h (ys++xs)).count ≤ V) (ho : (packet h (ys++zs)).count ≤ V)
    (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let cost := ys.length * (256*(V+1))
    BoundedFits env (parkPrefix ys.length c) (pile 0 (packet h (ys++xs)) r)
      (pile 0 (packet h (ys++zs)) r) (t+cost) (base+S+256*(V+1)) (D+256*(V+1)) := by
  induction ys generalizing V r base with
  | nil =>
    simpa [parkPrefix] using (run r base hr).mono le_rfl
      (show _ ≤ base+S+256*(V+1) by omega) (show _ ≤ D+256*(V+1) by omega)
  | cons y ys ih =>
    let K := 256*(V+1)
    let n := ys.length*K
    let cap := base+S+K
    let ret := D+K
    change BoundedFits env (save.join ((parkPrefix ys.length c).join restore))
      (pile 0 (packet h (y::(ys++xs))) r) (pile 0 (packet h (y::(ys++zs))) r)
      (t+((ys.length+1)*K)) cap ret
    rw [Nat.add_mul,Nat.one_mul]
    let V₀ := V-(y.count+1)
    have ci : (packet h (ys++xs)).count ≤ V₀ := by
      dsimp only [V₀]
      simp only [List.cons_append,packet,Tree.count,Task.forest_cons,id_eq] at hi ⊢
      omega
    have co : (packet h (ys++zs)).count ≤ V₀ := by
      dsimp only [V₀]
      simp only [List.cons_append,packet,Tree.count,Task.forest_cons,id_eq] at ho ⊢
      omega
    have hy : h.count + y.count ≤ V := by
      simp only [List.cons_append,packet,Tree.count,Task.forest_cons,id_eq] at hi
      omega
    change (packet h (y::(ys++xs))).count ≤ V at hi
    have a := save_fits h y (ys++xs) env r
    have b := restore_fits h y (ys++zs) env r
    have h₁ := BoundedFits.of_fits a (cap:=cap) (depth:=ret-1)
      (fun i => by have := hr.pile 0 (packet h (y::(ys++xs))) i
                   dsimp only [cap,K]; omega) (by dsimp only [ret,K]; omega)
    have h₃ := BoundedFits.of_fits b (cap:=cap) (depth:=ret)
      (fun i => by have := ((hr.pile 1 y).pile 0 (packet h (ys++zs))) i
                   dsimp only [cap,K]; omega) (by dsimp only [ret,K]; omega)
    have h₂ := ih V₀ ci co (pile 1 y r) (base+y.count) (hr.pile 1 y)
    let K₀ := 256*(V₀+1)
    change BoundedFits env _ _ _ (t+ys.length*K₀) (base+y.count+S+K₀) (D+K₀) at h₂
    have hroom : V = V₀ + (y.count+1) := by
      have := h.count_pos
      dsimp only [V₀]
      omega
    have spread : K = K₀ + 256*(y.count+1) := by
      change 256*(V+1) = 256*(V₀+1)+256*(y.count+1)
      nth_rw 1 [hroom]
      ring
    have leK : K₀ ≤ K := by omega
    have ltK : K₀+1 ≤ K := by omega
    have times : ys.length*K₀ ≤ n := Nat.mul_le_mul_left ys.length leK
    have middle := h₂.mono le_rfl (show _ ≤ cap by change base+y.count+S+K₀ ≤ base+S+K; omega) le_rfl
    have u := h₁.join (middle.join h₃ (by change D+K₀+1 ≤ D+K; omega)) (by dsimp only [ret,K]; omega)
    exact u.mono (by change _ ≤ t+(n+K); dsimp only [K]; omega) le_rfl le_rfl

/-- The register and return-stack overhead is linear in the packet volume
with a constant independent of the number of parked rows. -/
theorem parkPrefix_linear (ys xs zs : List Tree) (h : Tree) (c : Cmd) (env : Env) (t S D : ℕ)
    (run : ∀ r base, DeckCap base r → BoundedFits env c (pile 0 (packet h xs) r)
      (pile 0 (packet h zs) r) t (base+S) D) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let v := max (packet h (ys++xs)).count (packet h (ys++zs)).count
    let cost := 256*(v+1)
    BoundedFits env (parkPrefix ys.length c) (pile 0 (packet h (ys++xs)) r)
      (pile 0 (packet h (ys++zs)) r) (t+ys.length*cost) (base+S+cost) (D+cost) :=
  prefix_bounded ys xs zs h c env t S D _ run (le_max_left _ _) (le_max_right _ _) r base hr

/-- The saved prefix is available again after any change in the active arity.
The inner time and absolute resource allowances are each charged once. -/
theorem parkPrefix_bounded (ys xs zs : List Tree) (h : Tree) (c : Cmd) (env : Env) (t S D : ℕ)
    (run : ∀ r base, DeckCap base r → BoundedFits env c (pile 0 (packet h xs) r)
      (pile 0 (packet h zs) r) t (base+S) D) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let v := max (packet h (ys++xs)).count (packet h (ys++zs)).count
    let cost := ys.length*(256*(v+1))
    BoundedFits env (parkPrefix ys.length c) (pile 0 (packet h (ys++xs)) r)
      (pile 0 (packet h (ys++zs)) r) (t+cost) (base+S+cost) (D+cost) := by
  cases ys with
  | nil => simpa [parkPrefix] using run r base hr
  | cons a as =>
    have u := parkPrefix_linear (a::as) xs zs h c env t S D run r base hr
    apply u.mono le_rfl <;> simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

open GeneratorSyntax

/-- The same uniform syntax generator handles a varying number of parked
rows and a computably supplied active command. -/
theorem effective_parkPrefix {X : Type} [Primcodable X] {n : X → ℕ} {c : X → Cmd}
    (hn : Computable n) (hc : Effective ltr c) : Effective ltr fun x => parkPrefix (n x) (c x) := by
  let step (_ : X) (v : ℕ × File) := joinFile (file ltr save) (joinFile v.2 (file ltr restore))
  have hs : Computable₂ step := (primrec_joinFile.to_comp.comp (Computable.const _)
    (primrec_joinFile.to_comp.comp (Computable.snd.comp .snd) (Computable.const _))).to₂
  refine (Computable.nat_rec hn hc hs).of_eq fun x => ?_
  change Nat.rec (file ltr (c x)) _ (n x) = file ltr (parkPrefix (n x) (c x))
  generalize n x = k
  induction k with
  | zero => rfl
  | succ k ih => simp [parkPrefix,step,ih,joinFile_file]

end InterchangeROM.Parking

end NearSquareRoot
end Computability
end OAI
