import OAI.Hierarchy.DescentDatedLocalScale

namespace OAI
/-! # Polynomial in the local sender fields and direct-contact slots -/
namespace Hierarchy.DescentContactFieldPolynomial
open DescentDatedAddressBook

/-- Finite work of all contact opcodes per original host, packed host row or dictionary word.
The two site counts and the group dimension appear only in the separate physical area. -/
structure Fields where
  board : ℕ
  lanes : ℕ
  returns : ℕ
  stemJobs : ℕ
  degree : ℕ
  term : ℕ
  oldArgs : ℕ
  views : ℕ
  shapes : ℕ
  sockets : ℕ
  donors : ℕ

def coefficient (a : Fields) (u : ℕ) :=
  let cells n:=(n*2+2)*3
  let clock n j w:=(4+10*cells n)+(4+j*(4+(2*w+4)+(4+44)))
  let text n j w:=15*(cells n+1)+(15+j*(102+4*w))
  let gather n w:=1+n*(w+11)
  let back:=gather a.returns (256+32*a.degree+2*u)
  let phase (cost : ℕ→ℕ→ℕ→ℕ) (index : ℕ) :=
    cost a.board 1 (gather a.board u)+index+cost 2 a.lanes (gather 2 7)+
      cost a.returns a.stemJobs back+cost a.returns a.stemJobs back
  let halo:=2*(2*(a.degree+1)+1)
  let route:=1+((a.degree+1)+(1+(1+1)))
  let previous:=phase clock (4+10*(a.lanes*3))+(4+10*4)+
    (4+10*halo+(4+(a.degree+1)*(2*a.term+4))+(4+10*2)+(4+10*route))
  let names:=phase text (15*(a.lanes*3+1))+15*(4+1)+
    (15*(halo+1)+(11+4*a.term)+15*(2+1)+15*(route+1))
  let step n s:=1+n*2+1+(2*s+1)
  let pages:=a.views*step 1 1+5*(2*a.shapes+1)+a.sockets*step 8 a.shapes
  let marker:=1+8*(max (8*7) 96+11)
  let incoming:=gather a.oldArgs u
  let jobs:=a.sockets*a.donors
  let probe:=clock a.oldArgs 1 incoming+(12+10*pages)+
    (4+jobs*(4+a.shapes*(2*marker+4)+(4+44*a.shapes)))
  let declarations:=text a.oldArgs 1 incoming+15*(pages+3)+(15+jobs*(102+4*marker))
  (previous+7*names)+(probe+7*declarations)

def diagonal (x : ℕ) := coefficient ⟨x,x,x,x,x,x,x,x,x,x,x⟩ x

theorem dominated (a : Fields) (u x : ℕ) (work : u≤x) (small : ∀f∈
    [a.board,a.lanes,a.returns,a.stemJobs,a.degree,a.term,a.oldArgs,a.views,a.shapes,a.sockets,a.donors],f≤x) :
    coefficient a u≤diagonal x := by
  have board := small a.board (by simp)
  have lanes := small a.lanes (by simp)
  have returns := small a.returns (by simp)
  have stemJobs := small a.stemJobs (by simp)
  have degree := small a.degree (by simp)
  have term := small a.term (by simp)
  have oldArgs := small a.oldArgs (by simp)
  have views := small a.views (by simp)
  have shapes := small a.shapes (by simp)
  have sockets := small a.sockets (by simp)
  have donors := small a.donors (by simp)
  simp only [diagonal,coefficient]
  gcongr

theorem diagonal_eq (x : ℕ) : diagonal x=3802*x^3+41030*x^2+11994*x+11116 := by
  unfold diagonal coefficient
  norm_num1; simp only [show max (56:ℕ) 96=96 by decide]; ring

theorem diagonal_bound (x : ℕ) : diagonal x≤100000*(x+1)^3 := by
  rw [diagonal_eq]
  ring_nf; omega

variable {ι : ℕ→Type*} {J : ℕ→ℕ}

structure Bounds (J : ℕ→ℕ) (a : ∀h,ι h→Fields) : Prop where
  board : SmallAt J (fun h i=>(a h i).board)
  lanes : SmallAt J (fun h i=>(a h i).lanes)
  returns : SmallAt J (fun h i=>(a h i).returns)
  stemJobs : SmallAt J (fun h i=>(a h i).stemJobs)
  degree : SmallAt J (fun h i=>(a h i).degree)
  term : SmallAt J (fun h i=>(a h i).term)
  oldArgs : SmallAt J (fun h i=>(a h i).oldArgs)
  views : SmallAt J (fun h i=>(a h i).views)
  shapes : SmallAt J (fun h i=>(a h i).shapes)
  sockets : SmallAt J (fun h i=>(a h i).sockets)
  donors : SmallAt J (fun h i=>(a h i).donors)

theorem paid {a : ∀h,ι h→Fields} {u : ∀h,ι h→ℕ} (small : Bounds J a) (work : SmallAt J u) :
    SmallAt J (fun h i=>coefficient (a h i) (u h i)) := by
  let upper h (i : ι h):=u h i+(a h i).board+(a h i).lanes+(a h i).returns+(a h i).stemJobs+(a h i).degree+(a h i).term+(a h i).oldArgs+(a h i).views+(a h i).shapes+(a h i).sockets+(a h i).donors
  have all : SmallAt J upper := (((((((((((work.add small.board).add small.lanes).add small.returns).add small.stemJobs).add small.degree).add small.term).add small.oldArgs).add small.views).add small.shapes).add small.sockets).add small.donors)
  have plus:=all.add (SmallAt.const J 1)
  have base:=(SmallAt.const J 100000).mul ((plus.mul plus).mul plus)
  apply base.of_le
  intro h i
  have bound:=dominated (a h i) (u h i) (upper h i) (by dsimp [upper];omega) (by
    intro f hf
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    dsimp [upper]
    omega)
  simpa only [pow_succ,pow_zero,one_mul] using bound.trans (diagonal_bound _)

end Hierarchy.DescentContactFieldPolynomial

end OAI
