from fractions import Fraction as F
import itertools, math, numpy as np
from scipy.optimize import linprog
from gen import analyse

def reduce_vertices(V,z,D,n):
    dot=lambda a,x: sum(F(p)*q for p,q in zip(a,x))
    bound=2/3-1/D
    def box_and_support(W):
        Dm=np.array([[float(vi-zi) for vi,zi in zip(v,z)] for v in W])
        box=[];sup=set()
        for j in range(n):
            lohi=[]
            for s in (1,-1):
                cc=np.zeros(n); cc[j]=-s
                r=linprog(cc,A_ub=Dm,b_ub=np.full(len(W),bound),bounds=[(None,None)]*n,method='highs')
                if r.status!=0: return None,None
                sup|={W[i] for i,mu in enumerate(r.ineqlin.marginals) if abs(mu)>1e-9}
                lohi.append(math.floor(-r.fun+1e-9))
            box.append((-lohi[1],lohi[0]))
        return box,sup
    _,sup=box_and_support(V)
    W=set(sup)
    while True:
        box,_=box_and_support(sorted(W))
        if box is None: W|=set(V); continue
        added=False
        for w in itertools.product(*[range(lo,hi+1) for lo,hi in box]):
            k=math.ceil(dot(w,z))
            if max(dot(w,v) for v in W)>=k: continue
            best=max(V,key=lambda v:dot(w,v)); W.add(best); added=True
        if not added: return sorted(W),box

def fmt_vec(v): return "![" + ", ".join(str(x) for x in v) + "]"
def fmt_mat(A): return "!![" + ";\n     ".join(", ".join(str(x) for x in r) for r in A) + "]"

def generate(modname, matname, A, b, c, l, u, z, doc, paper_ref):
    n=len(A[0]); m=len(A)
    V,D,box,sep,npts=analyse(A,b,c,l,u,z)
    W,box=reduce_vertices(V,z,D,n)
    y=[int(3*t) for t in z]
    VD=[[int(D*t) for t in v] for v in W]
    w0,r0=sep
    xs=[f"w{j}" for j in range(n)]
    lin=lambda coeffs: " + ".join(f"({a}) * {x}" for a,x in zip(coeffs,xs))
    hyps="\n    ".join(f"(h{i} : {lin(v)} ≤ {D} * k - 1)" for i,v in enumerate(VD))
    bnds="\n".join(f"  have b{j}l : {lo} ≤ w{j} := by omega\n  have b{j}u : w{j} ≤ {hi} := by omega" for j,(lo,hi) in enumerate(box))
    ivc=" <;> ".join(f"interval_cases w{j}" for j,(lo,hi) in enumerate(box) if hi>lo)
    finish = (ivc+" <;> omega") if ivc else "omega"
    wargs=" ".join(f"(w {j})" for j in range(n))
    vargs="\n    ".join(f"(by have := hc {i}; simp [V, Fin.sum_univ_succ] at this; linarith)" for i in range(len(VD)))
    # hull
    rows="\n".join(f"  have r{i} := hr {i}\n  simp [{matname}, bv, cv, Fin.sum_univ_succ] at r{i}" for i in range(m))
    cols="\n".join(f"  have q{j} := hb {j}\n  simp [lv, uv] at q{j}" for j in range(n))
    ns=matname+"Data"
    s=f'''import Lab.EdmondsJohnson.Basic

/-!
# {doc}

{paper_ref}

Data: `b = {b}`, `c = {c}`, `l = {l}`, `u = {u}`, and the point `z = y / 3` with
`y = {y}`. `z` lies in the Chvátal closure of `P = P({matname}; b, c, l, u)`
(`z_mem_chvatalClosure`), but every integral point of `P` satisfies `w₀·x ≤ {r0}` with
`w₀ = {list(w0)}`, while `w₀·z > {r0}` (`z_not_mem_integerHull`).

The closure step uses the duality-free criterion `mem_chvatalClosure_of_int` with
{len(VD)} vertices of `P` (listed as `{D}v` in `V`). The integer statement `key` is checked by
bounding a would-be counterexample `w` to a box of
{math.prod(h-lo+1 for lo,h in box)} points and running `omega` on each.
-/

namespace EdmondsJohnson

/-- The matrix `{matname}`. -/
def {matname} : Matrix (Fin {m}) (Fin {n}) ℤ :=
  {fmt_mat(A)}

namespace {ns}

def bv : Fin {m} → ℤ := {fmt_vec(b)}
def cv : Fin {m} → ℤ := {fmt_vec(c)}
def lv : Fin {n} → ℤ := {fmt_vec(l)}
def uv : Fin {n} → ℤ := {fmt_vec(u)}
/-- `3z`. -/
def y : Fin {n} → ℤ := {fmt_vec(y)}
/-- `{D}v` for {len(VD)} vertices `v` of `P`. -/
def V : Fin {len(VD)} → Fin {n} → ℤ :=
  ![{(","+chr(10)+"    ").join(fmt_vec(v) for v in VD)}]
/-- The separating inequality `w₀·x ≤ {r0}` of the integer hull. -/
def w₀ : Fin {n} → ℤ := {fmt_vec(w0)}

lemma y_mem : IntMem {matname} bv cv lv uv 3 y := by decide

lemma V_mem : ∀ i, IntMem {matname} bv cv lv uv {D} (V i) := by decide

set_option maxHeartbeats 4000000 in
/-- The integer core, on coordinates. -/
lemma key_coords ({" ".join(xs)} k : ℤ) (hz : 3 * k ≤ {lin(y)} + 2)
    {hyps} : False := by
{bnds}
  {finish}

lemma key (w : Fin {n} → ℤ) (k : ℤ) (hz : 3 * k ≤ ∑ j, w j * y j + 2) :
    ∃ i, {D} * k ≤ ∑ j, w j * V i j := by
  by_contra hc
  push Not at hc
  simp [y, Fin.sum_univ_succ] at hz
  exact key_coords {wargs} k (by linarith)
    {vargs}

/-- `z = y / 3` lies in the Chvátal closure of `P`. -/
theorem z_mem_chvatalClosure :
    (fun j => (y j : ℝ) / 3) ∈ chvatalClosure (poly {matname} bv cv lv uv) :=
  mem_chvatalClosure_of_int y V {D} (by norm_num) y_mem V_mem key

/-- Every integral point of `P` satisfies `w₀·x ≤ {r0}`. -/
lemma int_le (k : Fin {n} → ℤ) (hk : (fun j => (k j : ℝ)) ∈ poly {matname} bv cv lv uv) :
    ∑ j, w₀ j * k j ≤ {r0} := by
  obtain ⟨hr, hb⟩ := intMem_of_mem hk
{rows}
{cols}
  simp [w₀, Fin.sum_univ_succ]
  omega

/-- `z` is not in the integer hull of `P`. -/
theorem z_not_mem_integerHull :
    (fun j => (y j : ℝ) / 3) ∉ integerHull (poly {matname} bv cv lv uv) := by
  intro h
  have := integerHull_le w₀ {r0} int_le h
  simp [w₀, y, Fin.sum_univ_succ] at this
  norm_num at this

end {ns}

/-- **`{matname}` does not have the Edmonds–Johnson property.** -/
theorem not_hasEJProperty_{matname} : ¬ HasEJProperty {matname} := fun h =>
  {ns}.z_not_mem_integerHull (h {ns}.bv {ns}.cv {ns}.lv {ns}.uv ▸ {ns}.z_mem_chvatalClosure)

end EdmondsJohnson
'''
    open(f'../../Lab/EdmondsJohnson/{modname}.lean','w').write(s)
    print(modname, 'vertices',len(V),'used',len(VD),'box',box)

if __name__=='__main__':
    A6=[[0,0,1,-1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
    generate('A6','A6',A6,[0,2,1,1,0],[2,4,3,3,2],[-1,0,-1,0,-1,-1],[1,2,1,2,2,2],[F(2,3),F(1,3)]*3,
      "Del Pia's counterexample `A₆` does not have the Edmonds–Johnson property",
      "Del Pia, arXiv:2611.28580 (v1), Proposition 3.3, with the paper's data `(3)`.")
    A6p=[[0,0,1,1,0,0],[0,1,1,0,2,0],[0,1,0,1,0,2],[1,0,1,0,2,0],[1,0,0,1,0,2]]
    generate('A6plus','A6plus',A6p,[-2,-2,-1,-1,0],[0,0,1,1,2],[-1,-2,-1,0,-1,-1],[1,0,1,2,2,2],
      [F(-2,3),F(-1,3),F(-2,3),F(1,3),F(1,3),F(1,3)],
      "The matrix `A₆⁺` does not have the Edmonds–Johnson property",
      "Del Pia, arXiv:2611.28580 (v1), Section 6, states this without proof (\"We do not include these\nproofs here\"). The data below are ours, found by computer search.")
    A7=[[0,0,1,-1,2,-2,2],[0,1,1,0,2,0,0],[0,1,0,1,0,2,0],[1,0,1,0,2,0,0],[1,0,0,1,0,2,0]]
    generate('A7','A7',A7,[-1,-2,-2,-1,-1],[1,0,0,1,1],[-1,-2,-1,-1,-1,-1,-1],[1,0,1,1,2,2,2],
      [F(-2,3),F(-1,3),F(-2,3),F(-2,3),F(1,3),F(1,3),F(1,3)],
      "The matrix `A₇` does not have the Edmonds–Johnson property",
      "Del Pia, arXiv:2611.28580 (v1), Section 6, states this without proof (\"We do not include these\nproofs here\"). The data below are ours, found by computer search.")
