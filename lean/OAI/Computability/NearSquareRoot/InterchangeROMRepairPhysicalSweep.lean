import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveSeries
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded

/-! # A fixed-register datapath for one selected-field spectral pass

The single recursive field mover receives one copy of the data row. A second
copy supplies the ordinary coefficients, and a third supplies payload lengths
for broadcasting the separately generated comparison marks. Each component
runs on the same shape header and leaves the background deck intact.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters InterchangeROM GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)

abbrev Run (env : Env) (c : Cmd) (x y : Tree) (a : Allowance) : Prop :=
  ∀ r base, DeckCap base r → BoundedFits env c (pile 0 x r) (pile 0 y r)
    a.time (base+a.cap) a.depth

def joinCost (a b : Allowance) : Allowance :=
  ⟨a.time+b.time+2,max a.cap b.cap,max (a.depth+1) b.depth⟩

theorem run_join {env : Env} {c d : Cmd} {x y z : Tree} {a b : Allowance}
    (hc : Run env c x y a) (hd : Run env d y z b) : Run env (c.join d) x z (joinCost a b) := by
  intro r base hr
  have left := (hc r base hr).mono le_rfl (Nat.add_le_add_left (le_max_left a.cap b.cap) base) le_rfl
  have right := (hd r base hr).mono le_rfl (Nat.add_le_add_left (le_max_right a.cap b.cap) base)
    (le_max_right (a.depth+1) b.depth)
  exact left.join right (le_max_left ..)

def scanCost (x : Tree) (t : ℕ) : Allowance := ⟨t,x.count+t,t⟩

private theorem of_fits {x y : Tree} {env : Env} {c : Cmd} {t : ℕ}
    (f : ∀ r, Fits env c (pile 0 x r) (pile 0 y r) t) : Run env c x y (scanCost x t) := by
  intro r base hr
  exact BoundedFits.of_fits (f r) (fun i => by
    have := hr.pile 0 x i
    change (letters (pile 0 x r) i).length + t ≤ base+(x.count+t)
    omega) le_rfl

def tail : Cmd := splitRoot 0 (fun _ => .pass) (discard 0)

theorem tail_within {R : ℕ} (hR : 0 < R) : Within R tail :=
  split_within hR (fun _ => trivial) (discard_within hR)

theorem head_within {R : ℕ} (hR : 3 ≤ R) : Within R (cellCommand 0) :=
  split_within (by omega : 0 < R) (fun _ => trivial)
    ⟨move_within (by omega) (by omega) (by omega),discard_within (by omega),
     move_within (by omega) (by omega) (by omega)⟩

def projectCost (x : Tree) : Allowance := scanCost x (90*x.count)

theorem run_head (h u : Tree) (env : Env) : Run env (cellCommand 0) (.fork h u) h (projectCost (.fork h u)) := by
  apply of_fits
  intro r
  have a := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) h env (pile 0 u r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at a
  have b := fits_discard 0 u env (pile 1 h r)
  have c := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) h env r
  apply (fits_pair (a.join (b.join c))).mono
  simp only [Tree.count]; omega

theorem run_tail (h u : Tree) (env : Env) : Run env tail (.fork h u) u (projectCost (.fork h u)) := by
  apply of_fits
  intro r
  apply (fits_pair (fits_discard 0 h env (pile 0 u r))).mono
  simp only [Tree.count]; omega

def two {A : Type} (a b : A) (i : Bool) := if i then b else a
def three {A : Type} (a b c : A) : Option Bool → A := Option.elim' c (two a b)

def collect2 (a b : Cmd) := seriesCommand (two a b) [false,true]
def collect3 (a b c : Cmd) := seriesCommand (three a b c) [some false,some true,none]

def cost2 (x y z : Tree) (a b : Allowance) : Allowance :=
  let out := Task.forest id [y,z]
  ⟨seriesClock x.count (two a.time b.time) [false,true],
    60*x.count+out.count+max a.cap b.cap+10,60*x.count+max a.depth b.depth+10⟩

def cost3 (x y z w : Tree) (a b c : Allowance) : Allowance :=
  let out := Task.forest id [y,z,w]
  ⟨seriesClock x.count (three a.time b.time c.time) [some false,some true,none],
    60*x.count+out.count+max a.cap (max b.cap c.cap)+10,
    60*x.count+max a.depth (max b.depth c.depth)+10⟩

theorem collect2_within {R : ℕ} (hR : 3 ≤ R) {a b : Cmd} (ha : Within R a) (hb : Within R b) :
    Within R (collect2 a b) :=
  series_within hR _ _ (fun i => by cases i <;> assumption)

theorem collect3_within {R : ℕ} (hR : 3 ≤ R) {a b c : Cmd}
    (ha : Within R a) (hb : Within R b) (hc : Within R c) : Within R (collect3 a b c) :=
  series_within hR _ _ (by rintro (_|(_|_)) <;> assumption)

theorem run_collect2 {env : Env} {c d : Cmd} {x y z : Tree} {a b : Allowance}
    (hc : Run env c x y a) (hd : Run env d x z b) :
    Run env (collect2 c d) x (Task.forest id [y,z]) (cost2 x y z a b) := by
  intro r base hr
  have h := series_bounded_at (two c d) x (two y z) (two a.time b.time)
    (max a.cap b.cap) (max a.depth b.depth) env (by
      rintro (_|_) q n hn
      · exact (hc q n hn).mono le_rfl (Nat.add_le_add_left (le_max_left ..) _) (le_max_left ..)
      · exact (hd q n hn).mono le_rfl (Nat.add_le_add_left (le_max_right ..) _) (le_max_right ..))
    [false,true] r base hr
  rw [show Task.forest (two y z) [false,true] = Task.forest id [y,z] by rfl] at h
  simpa only [collect2,cost2,Nat.add_assoc] using h

theorem run_collect3 {env : Env} {c d e : Cmd} {x y z w : Tree} {a b s : Allowance}
    (hc : Run env c x y a) (hd : Run env d x z b) (he : Run env e x w s) :
    Run env (collect3 c d e) x (Task.forest id [y,z,w]) (cost3 x y z w a b s) := by
  intro r base hr
  have h := series_bounded_at (three c d e) x (three y z w) (three a.time b.time s.time)
    (max a.cap (max b.cap s.cap)) (max a.depth (max b.depth s.depth)) env (by
      rintro (_|(_|_)) q n hn
      · exact (he q n hn).mono le_rfl (Nat.add_le_add_left ((le_max_right ..).trans (le_max_right ..)) _)
          ((le_max_right ..).trans (le_max_right ..))
      · exact (hc q n hn).mono le_rfl (Nat.add_le_add_left (le_max_left ..) _) (le_max_left ..)
      · exact (hd q n hn).mono le_rfl (Nat.add_le_add_left ((le_max_left ..).trans (le_max_right ..)) _)
          ((le_max_left ..).trans (le_max_right ..)))
    [some false,some true,none] r base hr
  rw [show Task.forest (three y z w) [some false,some true,none] = Task.forest id [y,z,w] by rfl] at h
  simpa only [collect3,cost3,Nat.add_assoc] using h

/-- The pointwise update consumes ordinary and swapped data on the last two
input lanes. The only occurrence of the recursive pivot is in the third lane. -/
def one (mask broadcast pivot lookup : Cmd) : Cmd :=
  let tags := (collect2 ((cellCommand 0).join mask) tail).join broadcast
  (collect3 tags tail pivot).join (lookup.join (cellCommand 0))

theorem one_within {R : ℕ} (hR : 3 ≤ R) {mask broadcast pivot lookup : Cmd}
    (hm : Within R mask) (hb : Within R broadcast) (hp : Within R pivot) (hl : Within R lookup) :
    Within R (one mask broadcast pivot lookup) :=
  ⟨collect3_within hR ⟨collect2_within hR ⟨head_within hR,hm⟩ (tail_within (by omega)),hb⟩
    (tail_within (by omega)) hp,hl,head_within hR⟩

def oneCost (h u v mark tags out : Tree) (am ab ap al : Allowance) : Allowance :=
  let x := Tree.fork h u
  let tagCost := joinCost (cost2 x mark u (joinCost (projectCost x) am) (projectCost x)) ab
  joinCost (cost3 x tags u v tagCost (projectCost x) ap)
    (joinCost al (projectCost (Task.forest id [out])))

theorem run_one {env : Env} {mask broadcast pivot lookup : Cmd} {h u v mark tags out : Tree}
    {am ab ap al : Allowance} (hm : Run env mask h mark am)
    (hb : Run env broadcast (Task.forest id [mark,u]) tags ab)
    (hp : Run env pivot (.fork h u) v ap)
    (hl : Run env lookup (Task.forest id [tags,u,v]) (Task.forest id [out]) al) :
    Run env (one mask broadcast pivot lookup) (.fork h u) out (oneCost h u v mark tags out am ab ap al) :=
  run_join (run_collect3 (run_join (run_collect2 (run_join (run_head h u env) hm)
    (run_tail h u env)) hb) (run_tail h u env) hp)
    (run_join hl (run_head out (.atom false) env))

open private build from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSeries

variable {X : Type} [Primcodable X]
private theorem effective_field {a b : X → Cmd} (ha : Effective ltr a) (hb : Effective ltr b) :
    Effective ltr (fun x => ((clone 1 0 2).join ((a x).join (pack 0))).join (b x)) :=
  ((effective_const ltr (clone 1 0 2)).join (ha.join (effective_const ltr (pack 0)))).join hb

private theorem effective_build {a : X → Cmd} (ha : Effective ltr a) :
    Effective ltr (fun x => (move 0 1 2).join ((give 0 false).join ((a x).join (discard 1)))) :=
  (effective_const ltr (move 0 1 2)).join ((effective_const ltr (give 0 false)).join
    (ha.join (effective_const ltr (discard 1))))

theorem effective_collect2 {a b : X → Cmd} (ha : Effective ltr a) (hb : Effective ltr b) :
    Effective ltr (fun x => collect2 (a x) (b x)) :=
  effective_build (effective_field hb (effective_field ha (effective_const ltr .pass)))

theorem effective_collect3 {a b c : X → Cmd}
    (ha : Effective ltr a) (hb : Effective ltr b) (hc : Effective ltr c) :
    Effective ltr (fun x => collect3 (a x) (b x) (c x)) :=
  effective_build (effective_field hc (effective_field hb (effective_field ha (effective_const ltr .pass))))

theorem effective_one {mask broadcast pivot lookup : X → Cmd}
    (hm : Effective ltr mask) (hb : Effective ltr broadcast) (hp : Effective ltr pivot) (hl : Effective ltr lookup) :
    Effective ltr (fun x => one (mask x) (broadcast x) (pivot x) (lookup x)) :=
  (effective_collect3 ((effective_collect2 ((effective_const ltr (cellCommand 0)).join hm)
    (effective_const ltr tail)).join hb) (effective_const ltr tail) hp).join
    (hl.join (effective_const ltr (cellCommand 0)))

end InterchangeROMRepair.Sweep

end NearSquareRoot
end Computability
end OAI
