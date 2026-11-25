import OAI.Computability.IntegerMultiplication.Prog.Compile
import OAI.Computability.IntegerMultiplication.Code.Tree
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List

/-! # Numeric syntax and compiler sites for structured P192 programs

A look instruction stores its complete finite branch table. A site stores the
codes for the enclosing ties as well as the code for the current instruction.
The constructor rules below build these data directly from a program family.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax
open IntegerMultiplication

variable {A : Type} [Fintype A] (letter : A ↪ ℕ)

/-- A numeric instruction begins with its opcode followed by its operands.
The branches of a look use the same order as the P192 compiler. -/
noncomputable def key : Prog A → ℕ
  | .pass => Encodable.encode ([0] : List ℕ)
  | .push i a => Encodable.encode [1, i, letter a]
  | .pop i => Encodable.encode [2, i]
  | .look i f => Encodable.encode (3 :: i :: Prog.options.map (fun a => key (f a)))
  | .join p q => Encodable.encode [4, key p, key q]
  | .tie p => Encodable.encode [5, key p]
  | .again i => Encodable.encode [6, i]

theorem key_injective : Function.Injective (key letter) := by
  intro p
  induction p with
  | look i f ih =>
    intro q h
    cases q <;> simp only [key, Encodable.encode_inj, List.cons.injEq] at h
    all_goals try omega
    obtain ⟨_, rfl, h⟩ := h
    congr 1
    funext a
    exact ih a ((List.map_inj_left.mp h) a (Prog.mem_options a))
  | join p q ih jh =>
    intro r h
    cases r <;> simp [key] at h
    exact congrArg₂ Prog.join (ih h.1) (jh h.2)
  | tie p ih =>
    intro r h
    cases r <;> simp [key] at h
    exact congrArg Prog.tie (ih h)
  | _ =>
    intro q h
    cases q <;> simp_all [key, letter.injective.eq_iff]

abbrev Site := List ℕ × ℕ
abbrev File := ℕ × List Site

noncomputable def site (p : Prog.Loc A) : Site := (p.1.map (key letter), key letter p.2)

theorem site_injective : Function.Injective (site letter) := by
  rintro ⟨g,p⟩ ⟨h,q⟩ e
  obtain ⟨e,f⟩ := Prod.mk.inj e
  exact Prod.ext (List.map_injective_iff.mpr (key_injective letter) e) (key_injective letter f)

/-- The exact compiler traversal, with its pointer keys represented by numbers. -/
noncomputable def file (p : Prog A) : File := (key letter p, (Prog.sites [] p).map (site letter))

private theorem sites_append (p : Prog A) (Γ Δ : Scope A) :
    Prog.sites (Γ ++ Δ) p = (Prog.sites Γ p).map (fun s => (s.1 ++ Δ, s.2)) := by
  induction p generalizing Γ with
  | look i f ih =>
    rw [Prog.sites.eq_def, Prog.sites.eq_def (Γ := Γ)]
    simp only [List.map_cons, List.map_flatMap]
    congr 1
    apply List.flatMap_congr
    intro a _
    exact ih a Γ
  | join p q ih jh =>
    rw [Prog.sites.eq_def, Prog.sites.eq_def (Γ := Γ)]
    simp only [List.map_cons, List.map_append, ih Γ, jh Γ]
  | tie p ih =>
    rw [Prog.sites.eq_def, Prog.sites.eq_def (Γ := Γ)]
    exact congrArg (List.cons _) (ih (p :: Γ))
  | _ => rw [Prog.sites.eq_def, Prog.sites.eq_def (Γ := Γ)]; rfl

/-- Attach an enclosing tie to all sites in the body. -/
def enclose (p : ℕ) (s : Site) : Site := (s.1 ++ [p], s.2)

/-- Store a root and its already enumerated descendants. -/
def root (fields : List ℕ) (children : List Site) : File :=
  let n := Encodable.encode fields
  (n, ([],n) :: children)

theorem file_pass : file letter (.pass : Prog A) = root [0] [] := by
  rw [file, Prog.sites.eq_def]; rfl

theorem file_push (i : ℕ) (a : A) : file letter (.push i a) = root [1,i,letter a] [] := by
  rw [file, Prog.sites.eq_def]; rfl

theorem file_pop (i : ℕ) : file letter (.pop i) = root [2,i] [] := by
  rw [file, Prog.sites.eq_def]; rfl

theorem file_again (i : ℕ) : file letter (.again i) = root [6,i] [] := by
  rw [file, Prog.sites.eq_def]; rfl

theorem file_join (p q : Prog A) : file letter (.join p q) =
    root [4, (file letter p).1, (file letter q).1] ((file letter p).2 ++ (file letter q).2) := by
  rw [file,Prog.sites.eq_def]
  simp only [List.map_cons, List.map_append]
  rfl

theorem file_tie (p : Prog A) : file letter (.tie p) =
    root [5,(file letter p).1] ((file letter p).2.map (enclose (file letter p).1)) := by
  rw [file, Prog.sites.eq_def]
  change (_, (([],p.tie) :: Prog.sites [p] p).map (site letter)) = _
  rw [show [p] = ([] : Scope A) ++ [p] from rfl, sites_append]
  simp only [List.map_cons, List.map_map, root, key, file, site, enclose, List.map_append,
    List.map_nil, List.map_cons, Function.comp_def]

theorem file_look (i : ℕ) (f : Option A → Prog A) :
    file letter (.look i f) = root
      (3 :: i :: Prog.options.map (fun a => (file letter (f a)).1))
      (Prog.options.flatMap fun a => (file letter (f a)).2) := by
  rw [file, Prog.sites.eq_def]
  simp only [List.map_cons, List.map_flatMap]
  rfl

/-- The fixed four-letter alphabet used by tree-stack programs. -/
def ltr : Code.Ltr ↪ ℕ where
  toFun
    | .bit false => 0
    | .bit true => 1
    | .node => 2
    | .sep => 3
  inj' := by
    rintro (⟨_ | _⟩ | _ | _) (⟨_ | _⟩ | _ | _) <;> simp

def joinFile (p q : File) : File := root [4,p.1,q.1] (p.2 ++ q.2)
def tieFile (p : File) : File := root [5,p.1] (p.2.map (enclose p.1))
def lookFile (i : ℕ) (branches : List File) : File :=
  root (3 :: i :: branches.map Prod.fst) (branches.flatMap Prod.snd)

theorem joinFile_file (p q : Prog A) :
    joinFile (file letter p) (file letter q) = file letter (.join p q) :=
  (file_join ..).symm

theorem tieFile_file (p : Prog A) : tieFile (file letter p) = file letter (.tie p) :=
  (file_tie ..).symm

theorem lookFile_file (i : ℕ) (f : Option A → Prog A) :
    lookFile i (Prog.options.map (fun a => file letter (f a))) = file letter (.look i f) := by
  rw [file_look]
  simp [lookFile, List.flatMap_map, Function.comp_def]

theorem primrec_root : Primrec₂ root := by
  have hk : Primrec fun v : List ℕ × List Site => Encodable.encode v.1 :=
    Primrec.encode.comp Primrec.fst
  exact hk.pair (Primrec.list_cons.comp ((Primrec.const []).pair hk) Primrec.snd)

theorem primrec_joinFile : Primrec₂ joinFile := by
  apply primrec_root.comp _ (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_cons.comp (Primrec.const 4)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])))

theorem primrec_tieFile : Primrec tieFile := by
  have en : Primrec₂ enclose :=
    (Primrec.list_concat.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).pair
      (Primrec.snd.comp Primrec.snd)
  apply primrec_root.comp _ (Primrec.list_map Primrec.snd
    (en.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  exact Primrec.list_cons.comp (Primrec.const 5) (Primrec.list_cons.comp Primrec.fst
    (Primrec.const []))

theorem primrec_lookFile : Primrec₂ lookFile := by
  apply primrec_root.comp _ (Primrec.list_flatMap Primrec.snd (Primrec.snd.comp Primrec.snd).to₂)
  exact Primrec.list_cons.comp (Primrec.const 3)
    (Primrec.list_cons.comp Primrec.fst (Primrec.list_map Primrec.snd
      (Primrec.fst.comp Primrec.snd).to₂))

variable {X : Type} [Primcodable X]

/-- Effective generation includes all sites of the ensuing compiler run. -/
def Effective (p : X → Prog A) : Prop := Computable (fun x => file letter (p x))

theorem effective_const (p : Prog A) : Effective letter (fun _ : X => p) := Computable.const _

theorem effective_push {i : X → ℕ} {a : X → A} (hi : Computable i)
    (ha : Computable fun x => letter (a x)) : Effective letter (fun x => .push (i x) (a x)) := by
  simp only [Effective, file_push]
  exact primrec_root.to_comp.comp (Computable.list_cons.comp (Computable.const 1)
    (Computable.list_cons.comp hi (Computable.list_cons.comp ha (Computable.const []))))
    (Computable.const [])

theorem effective_pop {i : X → ℕ} (hi : Computable i) :
    Effective letter (fun x => .pop (i x)) := by
  simp only [Effective, file_pop]
  exact primrec_root.to_comp.comp (Computable.list_cons.comp (Computable.const 2)
    (Computable.list_cons.comp hi (Computable.const []))) (Computable.const [])

theorem effective_again {i : X → ℕ} (hi : Computable i) :
    Effective letter (fun x => .again (i x)) := by
  simp only [Effective, file_again]
  exact primrec_root.to_comp.comp (Computable.list_cons.comp (Computable.const 6)
    (Computable.list_cons.comp hi (Computable.const []))) (Computable.const [])

theorem computable_options_map {I B : Type} [Primcodable B] (l : List I) (f : I → X → B)
    (hf : ∀ i ∈ l, Computable (f i)) : Computable fun x => l.map (fun i => f i x) := by
  induction l with
  | nil => exact Computable.const []
  | cons a l ih => exact Computable.list_cons.comp (hf a (by simp)) (ih fun i hi => hf i (by simp [hi]))

theorem effective_look {i : X → ℕ} {f : X → Option A → Prog A} (hi : Computable i)
    (hf : ∀ a, Effective letter (fun x => f x a)) : Effective letter (fun x => .look (i x) (f x)) := by
  have hb := computable_options_map Prog.options (fun a x => file letter (f x a)) (fun a _ => hf a)
  exact (primrec_lookFile.to_comp.comp hi hb).of_eq (fun x => lookFile_file ..)

namespace Effective

variable {letter} {p q : X → Prog A}

theorem join (hp : Effective letter p) (hq : Effective letter q) :
    Effective letter (fun x => .join (p x) (q x)) :=
  (primrec_joinFile.to_comp.comp hp hq).of_eq (fun _ => joinFile_file ..)

theorem tie (hp : Effective letter p) : Effective letter (fun x => .tie (p x)) :=
  (primrec_tieFile.to_comp.comp hp).of_eq (fun _ => tieFile_file ..)

theorem key (hp : Effective letter p) : Computable fun x => GeneratorSyntax.key letter (p x) :=
  Computable.fst.comp hp

end Effective

end GeneratorSyntax

end NearSquareRoot
end Computability
end OAI
