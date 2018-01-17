### STURM is a global variable which gives the bound to which all initial Hecke decompositions are done
STURM = 30

def collect_wt1_data(Nmin,Nmax,sturm=None,verbose=false):
	t = cputime()
	log = "DATA/wt1."+str(Nmin)+"-"+str(Nmax)+".log"
	for N in range(Nmin,Nmax+1):
		G = DirichletGroup(N)
		Gc = G.galois_orbits()
		Gc = [psi[0] for psi in Gc if psi[0](-1)==-1 and no_steinberg(psi[0])]
		if verbose > 0:
			print "----------------------------------------------------"
			print "Working with level",N
			print " There are",len(Gc),"spaces to consider"
		file = open(log,'a')
		file.write("\n------------------------------------------------\n")
		file.write("Working with level "+str(N)+"\n")
		file.write(" There are "+str(len(Gc))+" spaces to consider\n")
		file.close()

		for chi in Gc:
			chi = convert_character_to_database(chi)
			chi = chi.minimize_base_ring()
			if verbose > 0:
				print "\nWorking with",chi
			file = open(log,'a')
			file.write("\nWorking with "+str(chi)+"\n")
			file.close()
			A = wt1(chi,log=log,verbose=verbose)
			if verbose > 0:
				print "time:",cputime(t)
			file = open(log,'a')
			file.write("time: "+str(cputime(t))+"\n")
			file.close()

def wt1(chi,sturm=None,log=None,verbose=false):
	"""Computes the space of weight 1 forms with character chi
	
	INPUT:
	chi -- Dirichlet character

	OUTPUT:
    A list of the q-expansions (up to Galois conjugacy) of the weight 1 forms with nebentype chi
	"""
	# if log != None:
	# 	file = open(log,'a')
	# 	file.write(str(chi.modulus())+": computing with "+str(chi)+'\n')
	# 	file.close()

	U = cut_down_to_unique(chi,sturm=sturm,log=log,verbose=verbose)
	if U.num_forms() == 0:
		return []
	else:
		N = chi.modulus()
		strong_sturm = ceil(Gamma0(N).index() / 3)
		if log != None:
			file = open(log,'a')
			file.write("Computing to higher precision"+'\n')
			file.close()

		if verbose > 2:
			print "Computing to higher precision"
		# WASTING LOTS OF TIME ABOVE RECMPUTING EVERYTHING
		U = cut_down_to_unique(chi,sturm=strong_sturm,log=log,verbose=verbose)
		ans = []
		for f in U:
			if verify(f,chi,log=log):
				ans += [f]
			else:
				if verbose > 2:
					print "Did NOT verify"
				if log != None:
					file = open(log,'a')
					file.write("Did NOT verify"+'\n')
					file.close()


	if log != None:
		file = open(log,'a')
		file.write('-----------------------------\n')
		file.close()
	if verbose > 2:
		print "-----------------------------"


	return ans


def add_on_another_prime(chi,spaces,p,sturm=None,log=None,verbose=false):
	if sturm == None:
		sturm = STURM
	N = chi.modulus()
	if verbose > 1:
		print "Working with p =",p
	if log != None:
		file = open(log,'a')
		file.write(" Working with p = "+str(p)+": \n")
		file.close()

	Dp = wt1_space_modp(p,chi,sturm=sturm,verbose=verbose,log=log)
	if Dp.num_spaces() > 0:
		if verbose > 1:
			print "  -Found something"
		if log != None:
			file = open(log,'a')
			file.write("found something"+'\n')
			file.close()
		Sp = Dp.wt1_space(sturm=sturm)
		for Sq in spaces:
			Sp = Sp.intersect(Sq)
		for i in range(len(spaces)):
			spaces[i] = spaces[i].intersect(Sp) ## once more?
		spaces += [Sp]
		return spaces
	else:
		return []

def trim_down_spaces(chi,spaces):
	new_spaces = []
	for Sp in spaces:
		ans = []
		for f in Sp.forms():
			if ans.count(f) == 0:  # form hasn't been added yet
				m = min([S.multiplicity(f) for S in spaces])
				if m * euler_phi(chi.order()) >= f.degree():
					ans += [f]
					### SHOULD THINK THRU THIS -- PROBABLY FINE
					#assert m * euler_phi(chi.order()) == f.degree(), "haven't thought about this"
		new_spaces += [weight_one_space(ans)]

	return new_spaces


def cut_down_to_unique(chi,sturm=None,log=None,verbose=false):
### get character to agree with Buzzard-Lauder (Huh?)
	if sturm == None:
		sturm = STURM
	N = chi.modulus()
	unique = false
	empty = false
	started = false

	p = ZZ(2)
	j = 0
	spaces = []

	while (not empty and not unique) or not started:
		if gcd(p,chi.modulus())==1:
			spaces = add_on_another_prime(chi,spaces,p,sturm=sturm,log=log,verbose=verbose)
			started = true
			if len(spaces) == 0:
				empty = true
			for Sq in spaces:
				empty = empty or not Sq.is_nontrivial()
		if empty and started:
			if verbose > 1:
				print "  -nothing there after intersections"
			if log != None:
				file = open(log,'a')
				file.write('  -nothing there after intersection\n')
				file.close()

			spaces = []
		elif started:
			unique = true
			for Sq in spaces:
				unique = unique and Sq.unique()
		p = next_prime(p)
		p = ZZ(p)

	if empty:
		if verbose > 1:
			print "Weight 1 space has no exotic forms"
		if log != None:
			file = open(log,'a')
			file.write("Weight 1 space has no exotic forms"+'\n')
			file.close()
		return weight_one_space([])
	else:		
		### gets rid of multiplicity (counted carefully by Galois)
		spaces = trim_down_spaces(chi,spaces)

		ans = []
		for i in range(spaces[0].num_forms()): #all spaces should now be identical in hecke polys
			f = spaces[0][i]
			## looking for an unramified prime to compute this form
			poly = 1
			for q in f.primes():
				poly *= f[q][0]
			Lf = poly.splitting_field('a')
			p_found = false
			r = 0
			while (not p_found) and (r < len(spaces)):
				p = spaces[r][i].space().p
				if Lf.disc() % p != 0:
					g = spaces[r][i]
					assert f==g,"should have been same form.  whawt is going on?"
					p_found = true
					ans += [g]
				else:
					r += 1
			if not p_found: # "no unramified prime!  need to compute more p's"
				if verbose > 1:
					print "No unramified prime: need more primes!"
				if log != None:
					file = open(log,'a')
					file.write('No unramified prime: need more primes!\n')
					file.close()
				while Lf.disc() % p == 0:
					p = next_prime(p)
				spaces_aug = add_on_another_prime(chi,spaces,p,sturm=sturm,log=log,verbose=verbose)
				if len(spaces_aug) > 0:
					spaces_aug = trim_down_spaces(chi,spaces)
					g = spaces_aug[len(spaces_aug)-1][i]
					ans += [g]
				else:
					if verbose > 1:
						print "  -nothing there after intersection"
					if log != None:
						file = open(log,'a')
						file.write('  -nothing there after intersection\n')
						file.close()

		return weight_one_space(ans)


def unique_to_qexp(chi,forms,sturm=None):
	if sturm == None:
		sturm = STURM
	ans = []
	for f in forms:
		### need to allow it to fail on this next line
		f.grab_eigens(sturm=sturm)
		f.lift_eigen_system()
		f.find_qexp()

		ans += [q_exp(ev0,sturm,chi)]

	return ans

def verify(f,chi,log=None):
	print "Verfying for chi =",chi
	if log != None:
		file = open(log,'a')
		file.write("Attempting to verify possible weight 1 form"+'\n')
		file.close()
	if verbose:
		print "Attempting to verify possible weight 1 form"
	sturm = ceil(Gamma0(chi.modulus()).index()/3) ## IS THIS RIGHT????
	f.form_q_exp(sturm)
	S = ModularSymbols(f.chi()**2,2,1).cuspidal_subspace()
	B = S.q_expansion_basis(sturm)
	g = f.q_exp() * E1chi(f.chi(),sturm)
	bool = is_in(g,S,sturm)
	print "f E_1(chi) test is:",bool
	if log != None:
		file = open(log,'a')
		file.write(" f E_1(chi) test is: "+str(bool)+'\n')
		file.close()
	if bool:
		bool = is_in(f.q_exp()**2,S,sturm)
		print "f^2 test is:",bool
		if log != None:
			file = open(log,'a')
			file.write(" f^2 test is: "+str(bool)+'\n')
			file.write(str(f)+'\n')
			file.close()
			file = open(log+".data",'a')
			file.write(str(chi)+'\n')
			file.write(str(f)+'\n')
			file.write('------\n')
			file.close()
	if bool:
		print "Success!"
		print f
	else:
		print "did not verify"

	return bool




def wt1_space_modp(p,chi,verbose=False,sturm=None,log=None):
	K = chi(1).parent()
	if K != QQ:
		pp = K.prime_above(p)
	else:
		pp = ideal(p)
	M = maximal_eigendoubled_Artin(chi,p,pp,sturm,log=log,verbose=verbose)
	D = decompose(M,chi,sturm,[p],p)
	D._pK = pp
	if D.lower_bound() == D.upper_bound():
		return EigenDecomp([],chi)
	else:
		if p > 2:
			D.remove_CM()

	return D


## 	M = ModularSymbols(chi,p,1,GF(p)).cuspidal_subspace()
##  pp is prime over p in Q(chi)
def maximal_eigendoubled_Artin(chi,p,pp,sturm,log=None,verbose=False):
	if sturm == None:
		sturm == STURM
	N = chi.modulus()

	kk = pp.residue_field()
	if verbose > 2:
		print "Forming modsym space"
	if log != None:
		file = open(log,'a')
		file.write('Forming modsym space\n')
		file.close()

	M = ModularSymbols(chi,p,1,kk).cuspidal_subspace().new_subspace()

	if chi.order() == 2 and N.is_prime():
		K = QuadraticField(-N)
		C = K.class_group()
		lb = (len(C)-1)/2
	else:
		if CM.keys().count(chi)==0:
			lb = 0
		else:
			lb = len(CM[chi])


	N = chi.modulus()
	Nc = chi.conductor()					


#	exclude = [q for q in primes(sturm) if N%q==0] + [p]
	exclude = [p]
	ell = 2
	while (M.dimension() >= 2*lb + 2*euler_phi(chi.order())) and (ell<=sturm):  
	## can we do better here in general?  Are exotic forms never over Q and thus always come in pairs?
		if exclude.count(ell) == 0 and N.valuation(ell) == Nc.valuation(ell):
		## second condition is imposed because otherwise T_ell is identically 0.
			M = maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=verbose,log=log)
		ell = next_prime(ell)

	return M

def maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=False,log=None):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	R = PolynomialRing(GF(p),'x')
	x = R.gen()

	if verbose > 2:
		print "Using T_",ell,"on",M.dimension(),"-dimensional space"
	if log != None:
		file = open(log,'a')
		file.write('Using T_'+str(ell)+' on '+str(M.dimension())+'-dimensional space\n')
		file.close()
	T_ell = M.hecke_operator(ell)
	f_ell = T_ell.charpoly()
	facts = f_ell.factor()
	if verbose > 2:
		print "  Collecting irreducible factors with doubled socle and Artin type	"
	if log != None:
		file = open(log,'a')
		file.write('  Collecting irreducible factors with doubled socle and Artin type\n')
		file.close()
	f_passed = 1
	passed = false
	for D in facts:
		g = D[0]
		e = D[1]
		if e > 1:  ## doubled
			if verbose > 2:
				print "    Poly =",g,"is doubled.  Checking Artin and eigen-doubled"
			if log != None:
				file = open(log,'a')
				file.write('    Poly = '+str(g)+' is doubled.  Checking Artin and eigen-doubled\n')
				file.close()

			if chi.modulus() % ell != 0:
				v = FC.possible_Artin_polys(g,chi(ell),p)
			elif N.valuation(ell) == chi.conductor().valuation(ell):
				v = FC.possible_Artin_polys(g,chi,p)
			elif  g == x:
				v = [x]
			else:
				v = []
			if len(v) > 0:  ## Artin type
				socle = g.substitute(T_ell).kernel()
				passed = socle.dimension() >= 2*g.degree()
				if verbose > 2:
					if passed:
						print "      passed --- eigen-doubled and Artin"
					else:
						print "      not eigen-doubled"
				if passed:
					to_file(log,"      passed --- eigen-doubled and Artin")
				else:
					to_file(log,"      not eigen-doubled")
			else:
				if verbose > 2:
					print "      not Artin"
				to_file(log,"      not Artin")
				passed = false
			if passed:
				f_passed *= g**e
	if f_passed != 1:
		if verbose > 2:
			print "Restricting to",f_passed.factor()
		to_file(log,"Restricting to "+str(f_passed.factor()))

		M = (f_passed.substitute(T_ell)).kernel()
	else:
		M = M.zero_submodule()

	return M

def to_file(log,str):
	file = open(log,'a')
	file.write(str+'\n')
	file.close()

## no steinberg primes not dividing conductor
def no_steinberg(chi):
	M = chi.modulus()
	N = chi.conductor()
	d = M/N
	fact = d.factor()
	exps = [a[1] for a in fact]
	return len(exps) == 0 or min(exps) > 1

def decompose(M,chi,sturm,exclude,p,eigendoubled=True):
	if sturm == None:
		sturm = STURM
	D = EigenDecomp(decompose_helper([M],sturm,exclude,eigendoubled=eigendoubled),chi)
	bad_spaces = []
	for r in range(D.num_spaces()):
		if D.eigen_multiplicity(r,exclude,sturm=sturm) < 2:
			bad_spaces.append(D[r])
	for M in bad_spaces:
		D.remove(M)

	return D


def decompose_helper(Ms,sturm,exclude,eigendoubled=True):
	newMs = Ms
	for q in primes(sturm+1):
		if exclude.count(q)==0:
			newMs = decompose_helper_at_q(newMs,q,eigendoubled=eigendoubled)
	return newMs

def decompose_helper_at_q(Ms,q,eigendoubled=True):
	if len(Ms)>0:
		M = Ms[0]
		newMs = []
		Tq = M.hecke_operator(q)
		fq = Tq.charpoly()
		fact = fq.factor()
		for D in fact:
			g = D[0]
			e = D[1]
			if eigendoubled:
				if e > 1:
					if g.substitute(Tq).kernel().dimension() >= 2 * g.degree():
						newMs += [((g**e).substitute(Tq)).kernel()]
			else:
				newMs += [((g**e).substitute(Tq)).kernel()]
		return newMs + decompose_helper_at_q(Ms[1:len(Ms)+1],q,eigendoubled=eigendoubled)
	else:
		return []

def convert_character_to_database(chi):
	chis = chi.galois_orbit()
	if max([CM.keys().count(psi) for psi in chis]) > 0: # conjugate of chi is a key in CM form database
		j = [CM.keys().count(psi) for psi in chis].index(1)
		return chis[j]
	else:
		return chi.minimize_base_ring()

# q-expansion of E_1(chi)
def E1chi(chi,acc):
	L = chi(1).parent()
	R = PolynomialRing(L,'q')
	q = R.gens()[0]

	ans = R(-chi.bernoulli(1)/2)

	for n in range(1,acc):
		coef = 0
		for d in divisors(n):
			coef += chi(d)
		ans += coef * q**n

	return ans

#	return phi(-chi.bernoulli(1)/2) + form_q_exp(d,acc,chi)

## is the q-expansion f in the space S
def is_in(f,S,acc):
	L = f.parent().base_ring()
	K = S.base_ring()
	phi = Hom(K,L).an_element()
	q = f.parent().gens()[0]

	assert acc > S.dimension()+2,"not enough accuracy"

	B = S.q_expansion_basis(acc)

	C = []
	for b in B:
		C += [sum([phi(b.list()[j]) * q**j for j in range(len(b.list()))])]



	RR = PowerSeriesRing(L,acc,'q')

	bool = (f-sum([C[n]*f[C[n].valuation()] for n in range(len(B))])).truncate(acc) == 0
	if not bool:
		print (f-sum([C[n]*f[C[n].valuation()] for n in range(len(B))])).truncate(acc)

	return bool

