# This file contains code which takes a prime p and returns a potential weight 1 space.
# Elements of this potential weight 1 space are dictionaries with send primes to a list 
# of polynomials which are irreducible over Q(chi).  At ell, these polynomials represent the
# possible minimal polynomials (over Q(chi)) of the eigenvalue of T-ell.
#
# More precisely, let h be one of these dictionaries.  Attach to h, we define an ideal I_h in the Hecke algebra.
# Namely, for ell a prime, let pi_ell denote the product over all polynomials in h[ell].  Set I_h equal to 
# the ideal generated by pi_ell(T_ell) for all ell in h.keys().  The mathematiacl meaning of a potential space
# of weight 1 forms is that:
#
# S_1(N,chi) is contained within union over all h of S_1(N,chi)[I^\infty].
#
# We say this space is unique or uniquely determined, if h[ell] has length 1 for all ell.  In this case,
# we further know that S_1(N,chi)[I^\infty] is bounded in dimension by the multiplicity of h in our space
# times max(degree h[ell]) as ell primes over all of h.keys().
#
# Less formally, when the space is unique, the only q-expansions that can occur are the ones for which the 
# min poly of a_ell is the unique polynomial in h[ell].

def wt1_space_modp(p,chi,lower=0,verbose=False,sturm=None,log=None):
	"""
	Returns a weight one space which contains the potential q-expansions of any potential weight 1 form

	Let N be the modulus of chi, Nc the conductor of chi and Nt = N/Nc.
	If p \nmid N, then each eigensystem in weight 1 will appear in weight p with multiplicity 2.  
	If p | N but does not divide Nt, then each eigensystem in weight 1 will appear in weight p with multiplicity 1.  
	We do not allow for p to divide Nt.

	Let e = 2 if p \nmid N and e = 1 otherwise

	Looking then in weight p, we enumerate all Hecke-eigensystems that:
		(1) have multiplicity at least e
		(2) are of Artin-type
	 
	INPUT:
	- p = prime
	- chi = Dirichlet character (normalized to fit database)

	OUTPUT:
    
	A weight one space
	"""
	output(log,verbose,1,"------")
	output(log,verbose,1,"   Working with p = "+str(p)+":")
	N = chi.modulus()
	Nc = chi.conductor()
	Nt = N / Nc
	assert Nt % p != 0,"working at supercuspidal prime!"
	if N % p != 0:
		e = 2
	else:
		e = 1
	pchi = choose_prime_over_p(chi,p)
	FC.set_pchi(p,chi,pchi)
	kchi = pchi.residue_field()

	output(log,verbose,3,"     Forming modsym space")
	M = ModularSymbols(chi,p,1,kchi).cuspidal_subspace()

	if sturm == None:
		sturm = STURM
	if N % p != 0:
		exclude = [p]
	else:
		exclude = []
	D = decompose(M,chi,sturm,exclude,p,log,verbose)
	output(log,verbose,1,"    After decomposition into eigenspaces the upper bound is "+str(D.upper_bound()))
		
	if D.upper_bound() == lower:
		return weight_one_space([],chi)

	S = D.wt1_space(sturm=sturm)

	return S

def decompose(M,chi,sturm,exclude,p,log=None,verbose=false):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	if sturm == None:
		sturm = STURM
	output(log,verbose,2,"    Decomposing by Hecke away from p")
	doubled = N % p != 0
	D = EigenDecomp(decompose_helper([M],chi,sturm,exclude,p,log=log,verbose=verbose,doubled = doubled),chi,p=p)

	return D

def decompose_helper(Ms,chi,sturm,exclude,p,log=None,verbose=false,doubled=true):
	newMs = Ms

	# makes sure the first prime used is not supercuspidal (this is probably better)
	primes_to_use = [q for q in range(sturm) if is_prime(q)]
	for r in range(len(primes_to_use)):
		q = primes_to_use[r]
		if not supercuspidal(chi,q):
			break
	primes_to_use.remove(q)
	primes_to_use = [q] + primes_to_use

	d = sum([M.dimension() for M in Ms])
	for q in primes_to_use:
		if exclude.count(q)==0:
			output(log,verbose,3,"      decomposing with Hecke operator at "+str(q)+" -- dimensions: "+str([newMs[a].dimension() for a in range(len(newMs))]))
			newMs = decompose_helper_at_q(newMs,chi,q,p,total_dim=d,log=log,verbose=verbose,doubled=doubled)
			if len(newMs) == 0:
				print "      --all spaces gone"
				break
	if exclude.count(p) > 0 and len(newMs) > 0:
		output(log,verbose,3,"      passing to ordinary subspaces -- dimensions: "+str([newMs[a].dimension() for a in range(len(newMs))]))
		newMs = ordinary_helper(newMs,p)
		output(log,verbose,3,"      final dimensions: "+str([newMs[a].dimension() for a in range(len(newMs))]))
	return newMs

def decompose_helper_at_q(Ms,chi,q,p,total_dim=Infinity,log=None,verbose=false,doubled=true):
	if len(Ms)>0:
		M = Ms[0]
		N = M.level()
		newMs = []
		Tq = M.hecke_operator(q)
		fq = Tq.charpoly()
		fact = fq.factor()
		for D in fact:
			g = D[0]
			e = D[1]
			if N % p != 0:
				v = FC.possible_Artin_polys(g,chi,q,p,upper=floor(total_dim/2))
			else:
				v = FC.possible_Artin_polys(g,chi,q,p,upper=total_dim)
			if (len(v) > 0) and (e > 1 or not doubled):
				newMs += [((g**e).substitute(Tq)).kernel()]
			else:
				total_dim -= e * g.degree()
		return newMs + decompose_helper_at_q(Ms[1:len(Ms)+1],chi,q,p,total_dim=total_dim,log=log,verbose=verbose,doubled=doubled)
	else:
		return []

def ordinary_helper(Ms,p):
	newMs = []
	for M in Ms:
		Tp = M.hecke_operator(p)
		fp = Tp.charpoly()
		R = fp.parent()
		x = R.gen()
		newM = (Tp**(fp.valuation(x))).image()
		if newM.dimension() > 0:
			newMs += [newM]
	return newMs

def output(log,verbose,level,str):
	if log != None:
		file = open(log,'a')
		file.write(str+'\n')
		file.close()
	if verbose > level:
		print str


def choose_prime_over_p(chi,p):
	Qchi = chi(1).parent()
	if Qchi != QQ:
		return Qchi.prime_above(p)
	else:
		return ideal(p)

def ordinary_subspace(M,p,log=None,verbose=False):
	output(log,verbose,3,"    Passing to ordinary subspace")
	T = M.hecke_operator(p)
	fp = T.charpoly()
	R = fp.parent()
	x = R.gen()
	return (T**(fp.valuation(x))).image()





