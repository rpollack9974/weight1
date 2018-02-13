####-----------------


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
	
	M,done = maximal_eigendoubled_Artin(chi,p,lower=lower,sturm=sturm,log=log,verbose=verbose)
	output(log,verbose,1,"    Maximal Artin eigendoubled subspace mod "+str(p)+" has dimension "+str(M.dimension())+
		" which gives an upper bound of "+str(floor(M.dimension()/e)))
	if done:
		return weight_one_space([],chi)
	else:
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


def maximal_eigendoubled_Artin(chi,p,lower=0,sturm=None,log=None,verbose=False):
	pchi = choose_prime_over_p(chi,p)
	FC.set_pchi(p,chi,pchi)

	N = chi.modulus()
	Nc = chi.conductor()					

	if N % p != 0:
		e = 2
	else:
		e = 1
	if sturm == None:
		sturm = STURM

	kchi = pchi.residue_field()
	output(log,verbose,3,"     Forming modsym space")

	M = ModularSymbols(chi,p,1,kchi).cuspidal_subspace()
		# if N % p != 0 or p == 2:
		# 	M = ModularSymbols(chi,p,1,kk).cuspidal_subspace()
		# else:
		# 	omega = teich_char(N,pp)
		# 	M = ModularSymbols(chi*omega**(-1),2,1,kk).cuspidal_subspace()
	R = PolynomialRing(M.base_ring(),'x')

	if N % p != 0:
		exclude = [p]
	else:
		exclude = []
	primes_to_use = []
	sc = []
	for ell in primes(sturm):
		if exclude.count(ell) == 0:
			if not supercuspidal(chi,ell):
				primes_to_use += [ell]
			else:
				sc += [ell]
	primes_to_use += sc

	output(log,verbose,2,"    Passing to maximal Artin eigen-doubled subspace")
	r = 0 
	while (floor(M.dimension()/e) > lower) and (r < len(primes_to_use)):
		ell = primes_to_use[r]
		M = maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=verbose,log=log)
		r += 1
	M = ordinary_subspace(M,p,log=log,verbose=verbose)

	return M,floor(M.dimension()/e) <= lower


## returns the maximal subspace of M which at ell is of Artin type (wrt chi) and has doubled eigensocle.
def maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=False,log=None):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	# R = PolynomialRing(GF(p),'x')
	# x = R.gen()

	if N % p == 0:
		output(log,verbose,2,'At a prime dividing the level!')
	output(log,verbose,2,'      Using T_'+str(ell)+' on '+str(M.dimension())+'-dimensional space')

	T_ell = M.hecke_operator(ell)
	f_ell = T_ell.charpoly()
	facts = f_ell.factor()

	if N % p != 0:
		output(log,verbose,3,'       Collecting irreducible factors with doubled socle and Artin type')
	else:
		output(log,verbose,3,'       Collecting irreducible factors with Artin type')

	f_passed = 1
	passed = false
	for D in facts:
		g = D[0]
		e = D[1]
		if N % p !=0:
			if e > 1:  ## doubled
				output(log,verbose,3,'        Poly = '+str(g)+' is doubled.  Checking Artin and eigen-doubled')
				v = FC.possible_Artin_polys(g,chi,ell,p,upper=floor(M.dimension()/2))
			else:
				v = []
		else:
			output(log,verbose,3,'        Checking if '+str(g)+' is Artin')
			v = FC.possible_Artin_polys(g,chi,ell,p,upper=M.dimension())
		### upper bound above rejects artin polys whose degree is too big to be plausible in this space


		passed = len(v) > 0
		if N % p != 0:
			if passed:
				socle = g.substitute(T_ell).kernel()
				passed = socle.dimension() >= 2*g.degree()
				if passed:
					output(log,verbose,3,"         passed --- eigen-doubled and Artin")
				else:
					output(log,verbose,3,"         not eigen-doubled")
			elif e > 1:
					output(log,verbose,3,"         not Artin")

		else:
			if not passed:
				output(log,verbose,3,"         not Artin")
			else:
				output(log,verbose,3,"         passed --- Artin")


		if passed:
			f_passed *= g**e

	if f_passed != 1:
		output(log,verbose,3,"      Restricting to "+str(f_passed.factor()))
		M = (f_passed.substitute(T_ell)).kernel()
	else:
		M = M.zero_submodule()

	return M

def decompose(M,chi,sturm,exclude,p,log=None,verbose=false):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	if sturm == None:
		sturm = STURM
	output(log,verbose,2,"    Decomposing by Hecke away from p")
	doubled = N % p != 0
	D = EigenDecomp(decompose_helper([M],sturm,exclude,log=log,verbose=verbose,doubled = doubled),chi,p=p)
	if N % p != 0:
		output(log,verbose,3,"    Verifying that each Hecke-system is still eigen-doubled")
		bad_spaces = []
		for r in range(D.num_spaces()):
			if D.eigen_multiplicity(r,exclude,sturm=sturm) < 2:
				bad_spaces.append(D[r])
		for M in bad_spaces:
			D.remove(M)

	return D


def decompose_helper(Ms,sturm,exclude,log=None,verbose=false,doubled=true):
	newMs = Ms
	for q in primes(sturm+1):
		if exclude.count(q)==0:
			output(log,verbose,3,"      decomposing with Hecke operator at "+str(q))
			newMs = decompose_helper_at_q(newMs,q,log=log,verbose=verbose,doubled=doubled)
	return newMs

def decompose_helper_at_q(Ms,q,log=None,verbose=false,doubled=true):
	if len(Ms)>0:
		M = Ms[0]
		newMs = []
		Tq = M.hecke_operator(q)
		fq = Tq.charpoly()
		fact = fq.factor()
		for D in fact:
			g = D[0]
			e = D[1]
			if (doubled and e > 1):
				if g.substitute(Tq).kernel().dimension() >= 2 * g.degree():
					newMs += [((g**e).substitute(Tq)).kernel()]
			else:
				newMs += [((g**e).substitute(Tq)).kernel()]
		return newMs + decompose_helper_at_q(Ms[1:len(Ms)+1],q,log=log,verbose=verbose,doubled=doubled)
	else:
		return []


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
