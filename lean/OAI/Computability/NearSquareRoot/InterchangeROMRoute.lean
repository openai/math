import OAI.Computability.NearSquareRoot.InterchangeBQuestCore
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSeries

/-! # Compiling the numbered source rows of an interchange route -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters

variable {M : Type}

/-- Work on a bank beneath its common shape header. -/
def underHeader (op : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join (op.join ((move 1 0 2).join (pack 0))))

theorem underHeader_within {R : ℕ} (hR : 3 ≤ R) {op : Cmd} (h : Within R op) :
    Within R (underHeader op) :=
  split_within (by omega) (fun _ => trivial)
    ⟨move_within (by omega) (by omega) (by omega),h,
     move_within (by omega) (by omega) (by omega),(by omega : 0 < R)⟩

theorem underHeader_fits (header input output : Tree) (c : Cmd) (t : ℕ) (env : Env)
    (run : ∀ deck, Fits env c (pile 0 input deck) (pile 0 output deck) t) (deck : Deck) :
    Fits env (underHeader c) (pile 0 (.fork header input) deck)
      (pile 0 (.fork header output) deck) (84 * header.count + t + 11) := by
  have start := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide)
    header env (pile 0 input deck)
  have finish := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide)
    header env (pile 0 output deck)
  rw [pile_comm 1 _ deck 0 _ (by decide)] at start finish
  exact (fits_pair (start.join ((run _).join (finish.join (fits_pack _ _ _ _ _))))).mono (by omega)

/-- The output contains the common header followed by the newly routed rows. -/
def packet (header : Tree) (xs : List Tree) := Tree.fork header (Task.forest id xs)

def routePart (moveRow : M → Cmd) : Option (ℕ × M) → Cmd
  | none => cellCommand 0
  | some (n, m) => (underHeader (cellCommand n)).join (moveRow m)

/-- One compiled field of the output is emitted for each literal source and move.
The persistent copy of the bank is shared by all field selections. -/
def routeCommand (moveRow : M → Cmd) (steps : List (ℕ × M)) : Cmd :=
  seriesCommand (routePart moveRow) (none :: steps.map some)

private theorem within_mono {A : Type} {c : Prog A} {R D : ℕ} (h : Within R c) (hr : R ≤ D) :
    Within D c := by
  induction c with
  | pass | again => trivial
  | push | pop => exact lt_of_lt_of_le h hr
  | look i branches ih => exact ⟨lt_of_lt_of_le h.1 hr,fun v => ih v (h.2 v)⟩
  | join a b aih bih => exact ⟨aih h.1,bih h.2⟩
  | tie a ih => exact ih h

theorem route_within {R : ℕ} (hR : 3 ≤ R) (moveRow : M → Cmd) (hm : ∀ m, Within R (moveRow m))
    (steps : List (ℕ × M)) : Within R (routeCommand moveRow steps) := by
  apply series_within hR
  rintro (_ | ⟨j,m⟩)
  · exact within_mono (cell_within 0) hR
  · exact ⟨underHeader_within hR (within_mono (cell_within j) hR),hm m⟩

open private build from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSeries

private theorem build_map {A B : Type} (c : B → Cmd) (f : A → B) (xs : List A) :
    build c (xs.map f) = build (c ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,build,Function.comp_apply,ih]

theorem series_map {A B : Type} (c : B → Cmd) (f : A → B) (xs : List A) :
    seriesCommand c (xs.map f) = seriesCommand (c ∘ f) xs := by
  simp only [seriesCommand,← List.map_reverse,build_map]

private theorem forest_map {A B : Type} (out : B → Tree) (f : A → B) (xs : List A) :
    Task.forest out (xs.map f) = Task.forest (out ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,Task.forest_cons,Function.comp_apply,ih]

def source (xs : List Tree) (j : ℕ) : Tree := xs[j]?.getD (.atom false)

private theorem field {S D t : ℕ} (header : Tree) (xs : List Tree) (j : ℕ) (m : M)
    (y : Tree) (hj : j < xs.length) (moveRow : M → Cmd) (env : Env)
    (hc : ∀ r base, DeckCap base r →
      BoundedFits env (moveRow m) (pile 0 (.fork header (source xs j)) r) (pile 0 y r)
        t (base + S) D)
    (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    BoundedFits env (routePart moveRow (some (j,m))) (pile 0 (packet header xs) r) (pile 0 y r)
      (100 * ((packet header xs).count + 1) + t)
      (base + 101 * ((packet header xs).count + 1) + S) (101 * ((packet header xs).count + 1) + D) := by
  have hx : xs[j]? = some (source xs j) := by simp [source,hj]
  let v := packet header xs
  have select := underHeader_fits header (Task.forest id xs) (source xs j) _ _ env
    (cell_fits id xs j _ hx env) r
  have htime : 84 * header.count + 90 * (Task.forest id xs).count + 11 ≤ 99*(v.count+1) := by
    simp [v,packet,Tree.count]
    omega
  have hs := BoundedFits.of_fits (select.mono htime)
    (cap:=base+101*(v.count+1)+S) (depth:=99*(v.count+1))
    (fun i => by have := hr.pile 0 v i; change (letters (pile 0 v r) i).length + _ ≤ _; omega) le_rfl
  have arrive := (hc r base hr).mono le_rfl (by omega : base+S ≤ base+101*(v.count+1)+S)
    (show D ≤ 101*(v.count+1)+D from by omega)
  have := Tree.count_pos v
  exact (hs.join arrive (by omega)).mono (by change _ ≤ 100*(v.count+1)+t; omega) le_rfl le_rfl

private theorem route_sum {K : Type} (u : ℕ) (t : K → ℕ) (l : List K) :
    costSum (fun a => u + t a) l = u * l.length + costSum t l := by
  induction l with
  | nil => simp [costSum]
  | cons a l ih => simp only [costSum_cons,List.length_cons,Nat.mul_succ,ih]; omega

/-- Each supplied child clock occurs exactly once in the compiled bank clock.
The peak data volume uses the input, output, and the largest child allowance. -/
theorem route_bounded {K : Type} (header : Tree) (xs : List Tree) (steps : List K)
    (sel : K → ℕ × M) (moveRow : M → Cmd) (out : K → Tree)
    (t : K → ℕ) (S D : ℕ) (env : Env)
    (index : ∀ k, (sel k).1 < xs.length)
    (child : ∀ k r base, DeckCap base r →
      BoundedFits env (moveRow (sel k).2) (pile 0 (.fork header (source xs (sel k).1)) r)
        (pile 0 (out k) r) (t k) (base+S) D)
    (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let v := packet header xs
    let w := Tree.fork header (Task.forest out steps)
    BoundedFits env (routeCommand moveRow (steps.map sel)) (pile 0 v r) (pile 0 w r)
      ((steps.length + 2) * (160 * (v.count + 1)) + costSum t steps)
      (base + 170 * (v.count+1) + w.count + S) (170 * (v.count+1) + D) := by
  let v := packet header xs
  let w := Tree.fork header (Task.forest out steps)
  let l := none :: steps.map some
  let part := routePart moveRow ∘ Option.map sel
  let q : Option K → Tree := Option.elim' header out
  let time : Option K → ℕ := fun a => 100*(v.count+1) + a.elim 0 t
  have run : ∀ a dr b, DeckCap b dr → BoundedFits env (part a) (pile 0 v dr)
      (pile 0 (q a) dr) (time a) (b+(101*(v.count+1)+S)) (101*(v.count+1)+D) := by
    rintro (_ | a) dr b hb
    · have h := cell_fits id (header::xs) 0 header rfl env dr
      change Fits env _ (pile 0 v _) (pile 0 header _) (90*v.count) at h
      apply (BoundedFits.of_fits h (cap:=b+(101*(v.count+1)+S)) (depth:=101*(v.count+1)+D)
        (fun i => by have := hb.pile 0 v i; omega) (by omega)).mono _ le_rfl le_rfl
      change 90*v.count ≤ 100*(v.count+1)+0
      omega
    · simpa only [part,q,time,Function.comp_apply,Option.map_some,Option.elim_some,
        Option.elim'_some,Nat.add_assoc] using
        field header xs (sel a).1 (sel a).2 (out a) (index a) moveRow env (child a) dr b hb
  have compiled := series_bounded_at part v q time _ _ env run l r base hr
  have hl : (none :: (steps.map sel).map some) = l.map (Option.map sel) := by
    simp [l,List.map_map,Function.comp_def]
  have main : routeCommand moveRow (steps.map sel) = seriesCommand part l := by
    rw [routeCommand,hl,series_map]
  have outcome : Task.forest q l = w := by
    simp only [l,Task.forest_cons,forest_map]
    rfl
  have clock : seriesClock v.count time l =
      (45*v.count+100*(v.count+1)+7)*(steps.length+1) + costSum t steps + 60*v.count+10 := by
    change (45*v.count+(100*(v.count+1)+0)+7) + costSum _ (steps.map some) + _ + _ = _
    simp only [costSum,List.map_map,time,Function.comp_def,Option.elim_some]
    have eq := route_sum (45*v.count+100*(v.count+1)+7) t steps
    simp only [costSum] at eq
    simp_rw [show ∀ a : K, 45*v.count+(100*(v.count+1)+t a)+7 =
      (45*v.count+100*(v.count+1)+7)+t a by intro; omega]
    rw [eq]
    ring
  rw [outcome,clock,← main] at compiled
  apply compiled.mono _ (by change _ ≤ base+170*(v.count+1)+w.count+S; omega)
    (by change _ ≤ 170*(v.count+1)+D; omega)
  change _ ≤ (steps.length+2)*(160*(v.count+1))+costSum t steps
  have mult := Nat.mul_le_mul_right (steps.length+1)
    (show 45*v.count+100*(v.count+1)+7 ≤ 160*(v.count+1) by omega)
  rw [show (steps.length+2)*(160*(v.count+1)) =
    (160*(v.count+1))*(steps.length+1)+160*(v.count+1) by ring]
  omega

end InterchangeROM

end NearSquareRoot
end Computability
end OAI
