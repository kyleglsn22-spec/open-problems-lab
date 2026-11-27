# Generates Lab/ClawFree/ChromCount*.lean (run from open-problems-lab/). Prints the totals (128, 320, 768).
from collections import Counter
E=[(0,1),(1,2),(2,3),(3,0),(0,4),(0,5),(4,5),(2,6),(2,7),(6,7),(1,8),(3,9)]
A=[[a!=b and bool(set(E[a])&set(E[b])) for b in range(12)] for a in range(12)]
def ext(L):
    out=[]
    for l in L:
        j=len(l)
        for c in range(4):
            if all(not A[i][j] or l[i]!=c for i in range(j)): out.append(l+[c])
    return out
def gf(L,j):
    for _ in range(j): L=ext(L)
    return L
D=4
P=gf([[]],D)
def summ(L):
    cs=[tuple(l.count(i) for i in range(4)) for l in L]
    return (sum(c==(4,4,2,2) for c in cs),sum(c==(4,3,3,2) for c in cs),sum(c==(3,3,3,3) for c in cs))
lit=lambda l:'['+', '.join(map(str,l))+']'
out=['import Lab.ClawFree.Graph','','''/-!
# Counting the proper 4-colourings of `G` by class sizes

The kernel enumerates the proper colourings with the verified backtracking list. To keep memory
low, the enumeration is split by the colours of the first %d vertices: `gen4` lists the %d valid
prefixes, and each `pref_i` handles the colourings extending one prefix in its own declaration.
`summ_gen` adds the pieces up.
-/'''%(D,len(P)),'','namespace OpenProblemsLab.ClawFree.Counterexample','','open MvPolynomial Finset OpenProblemsLab.ClawFree','']
out.append('theorem gen%d : Enum.gen colR %d = [' % (D,D))
out.append(',\n'.join('    '+lit(p) for p in P)+'] := by')
out.append('  decide +kernel')
out.append('')
tot=[0,0,0]
for i,p in enumerate(P):
    s=summ(gf([p],12-D)); tot=[a+b for a,b in zip(tot,s)]
    out.append('theorem pref_%d : summ (Enum.genFrom colR [%s] %d) = (%d, %d, %d, true) := by\n  decide +kernel\n' % (i,lit(p),12-D,*s))
print(tot)
names=', '.join('pref_%d'%i for i in range(len(P)))
out.append('''theorem genFrom_cons2 (p q : List (Fin 4)) (L : List (List (Fin 4))) (j : ℕ) :
    Enum.genFrom colR (p :: q :: L) j = Enum.genFrom colR [p] j ++ Enum.genFrom colR (q :: L) j :=
  Enum.genFrom_cons colR p (q :: L) j

theorem summ_gen : summ (Enum.gen colR 12) = (128, 320, 768, true) := by
  rw [show (12 : ℕ) = %d + %d from rfl, Enum.gen_add, gen%d]
  simp only [genFrom_cons2, summ_append, %s]
  rfl
''' % (D,12-D,D,names))
for nm,w,v,k in [('4422','![4, 4, 2, 2]',128,'1'),('4332','![4, 3, 3, 2]',320,'2.1'),('3333','![3, 3, 3, 3]',768,'2.2.1')]:
    out.append('''theorem chrom_%s : coeff e%s (chromSym G 4) = %d := by
  have h := congrArg (·.%s) summ_gen
  simp only [summ] at h
  unfold contentIs at h
  rw [coeff_chromSym_eq_gen e%s %s (fun _ => rfl), h]
  rfl
''' % (nm,nm,v,k,nm,w))
out.append('end OpenProblemsLab.ClawFree.Counterexample')

txt='\n'.join(out)+'\n'
NCH=6
head_end=txt.index('theorem gen%d' % D)
pre=txt[:head_end]
g_end=txt.index('theorem pref_0 ')
gen_part=txt[head_end:g_end]
tail_start=txt.index('theorem genFrom_cons2')
prefs=txt[g_end:tail_start].split('\n\n')
prefs=[x for x in prefs if x.strip()]
per=(len(prefs)+NCH-1)//NCH
prev='Lab.ClawFree.Graph'
for c in range(NCH):
    body=(gen_part if c==0 else '')+'\n\n'.join(prefs[c*per:(c+1)*per])+'\n\n'
    t=pre.replace('import Lab.ClawFree.Graph','import '+prev)
    if c>0:
        t=t[:t.index('/-!')]+'/-! Colouring counts of `G`, part %d of %d (see `ChromCount0`). -/\n\n' % (c,NCH)+t[t.index('namespace'):]
    open('Lab/ClawFree/ChromCount%d.lean' % c,'w').write(t+body+'end OpenProblemsLab.ClawFree.Counterexample\n')
    prev='Lab.ClawFree.ChromCount%d' % c
t=pre.replace('import Lab.ClawFree.Graph','import '+prev)
t=t[:t.index('/-!')]+'/-! Colouring counts of `G`: assembling the pieces `ChromCount0` to `ChromCount%d`. -/\n\n' % (NCH-1)+t[t.index('namespace'):]
open('Lab/ClawFree/ChromCount.lean','w').write(t+txt[tail_start:])

