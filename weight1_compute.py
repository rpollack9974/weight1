
## TO DO --- make a find ap procedure that works and put it where used
##	     --- fix the upper bound stuff for FC at p.


### STURM is a global variable which gives the bound to which all initial Hecke decompositions are done
STURM = 20

def collect_wt1_data(Nmin=None,Nmax=None,Ns=None,sturm=None,verbose=false,pass_buck=false):
#	t = cputime()
	if Ns != None:
		v = Ns
	else:
		v = range(Nmin,Nmax+1)
	for N in v:
		log = "DATA/LOGS/wt1."+str(N)+".log"
		G = DirichletGroup(N)
		Gc = G.galois_orbits()
		Gc = [psi[0] for psi in Gc if psi[0](-1)==-1 and no_steinberg(psi[0])]
		if verbose > 0:
			print "----------------------------------------------------"
			print "Working with level",N
			print " There are",len(Gc),"space(s) to consider\n"
		file = open(log,'a')
		file.write("\n------------------------------------------------\n")
		file.write("Working with level "+str(N)+"\n")
		file.write(" There are "+str(len(Gc))+" space(s) to consider\n\n")
		file.close()

		for chi in Gc:
			chi = convert_character_to_database(chi)
			chi = chi.minimize_base_ring()
			# if verbose > 0:
			# 	print "\nWorking with",chi
			# file = open(log,'a')
			# file.write("\nWorking with "+str(chi)+"\n")
			# file.close()
			A = wt1(chi,log=log,verbose=verbose,pass_buck=pass_buck)
#			output(log,verbose,0,"time: "+str(cputime(t))+"\n")

def wt1(chi,sturm=None,log=None,verbose=false,pass_buck=false):
	"""Computes the space of weight 1 forms with character chi
	
	INPUT:
	chi -- Dirichlet character

	OUTPUT:
    A list of the q-expansions (up to Galois conjugacy) of the weight 1 forms with nebentype chi
	"""
	t = cputime()	
	ans = []
	output(log,verbose,1,"Working with "+str(chi))
	if CM.keys().count(chi) > 0:
		lb = len(CM[chi])
	else:
		lb = 0
	output(log,verbose,1," There are "+str(lb)+" CM form(s).")
	U = cut_down_to_unique(chi,sturm=sturm,log=log,verbose=verbose)
	if U[0].num_forms() == 0:
		output(log,verbose,0,"time: "+str(cputime(t))+"\n")
		return []
	else:
		if not pass_buck:
			need_more_primes = false
			bad_fs = []
			upper = upper_bound(U)
			lower = 0
			for S in U:
				if S.unique():
					break
			N = chi.modulus()
			strong_sturm = ceil(Gamma0(N).index() / 3)
			output(log,verbose,1,"Computing to higher precision")
			forms_used = []
			for f in S.forms():
				if forms_used.count(f) == 0:
					forms_used += [f]
					fs = [f]
					for r in range(1,len(U)):
						for g in U[r]:
							if g == f:
								fs += [g]
								break
					Kf = f.FC_field()
					d = f.disc()
					for g in fs:
						p = g.p()
						if d % p != 0:
							break
					fq,bool,need_more_primes,chi = form_qexp(g,fs,upper,log=log,verbose=verbose)
					if need_more_primes:
						bad_fs += [g]
					elif bool:
						bool = verify(fq,chi,log=log,verbose=verbose)
						if bool:
							ans += [fq]
							lower += f.degree() / euler_phi(chi.order())
						else:
							output(log,verbose,1,"Failed to verify")
							while U[0].multiplicity(f) > 0:
								U[0].remove(f)
							if U[0].num_forms() == 0:
								upper = 0
								break
							upper = upper_bound(U)
					else:
						output(log,verbose,2,"Failed to verify!")
						while U[0].multiplicity(f) > 0:
							U[0].remove(f)
						if U[0].num_forms() == 0:
							upper = 0
							break
						upper = upper_bound(U)

			for f in bad_fs:
				if need_more_primes:
					primes_used = [S.p() for S in U]
					pmax = max(primes_used)
					p = next_prime(p)
					U = add_on_another_prime(chi,U,p,sturm=sturm,log=log,verbose=verbose)
					upper = upper_bound(U)
				fs = [f]
				for r in range(1,len(U)):
					for g in U[r]:
						if g == f:
							fs += [g]
							break
				fq,bool,need_more_primes,chi = form_qexp(f,fs,upper,log=log,verbose=verbose)
				if need_more_primes:
					bad_fs += [g]
				elif bool:
					bool = verify(fq,chi,log=log,verbose=verbose)
					if bool:
						ans += [fq]
						lower += f.degree() / euler_phi(chi.order())
					else:
						output(log,verbose,1,"Failed to verify")
						while U[0].multiplicity(f) > 0:
							U[0].remove(f)
						if U[0].num_forms() == 0:
							upper = 0
							break
						upper = upper_bound(U)
				else:
					output(log,verbose,1,"Failed to verify!")
					while U[0].multiplicity(f) > 0:
						U[0].remove(f)
					if U[0].num_forms() == 0:
						upper = 0
						break
					upper = upper_bound(U)


			if lower != upper:
				output(log+str('.fail'),verbose,0,str(chi))
				output(log+str('.fail'),verbose,0,"lower = "+str(lower)+"; upper = "+str(upper))

			output(log,verbose,0,"time: "+str(cputime(t))+"\n")

			return ans,lower == upper
		else:
			output(log,verbose,-1,"PASSING THE BUCK ON THIS ONE!!!")
			output("DATA/hard_levels",verbose,-1,str(chi.modulus()))
			output(log,verbose,0,"time: "+str(cputime(t))+"\n")
			return chi

def add_on_another_prime(chi,spaces,p,sturm=None,log=None,verbose=false):
	if sturm == None:
		sturm = STURM
	N = chi.modulus()

	Sp = wt1_space_modp(p,chi,sturm=sturm,verbose=verbose,log=log)
	if Sp.num_forms() > 0:
		output(log,verbose,2,"    Intersecting")
	for Sq in spaces:
		Sp = Sp.intersect(Sq)
	for i in range(len(spaces)):
		spaces[i] = spaces[i].intersect(Sp)
	for Sq in spaces:
		Sp = Sp.intersect(Sq)
	for i in range(len(spaces)):
		spaces[i] = spaces[i].intersect(Sp)
	spaces += [Sp]
	if Sp.num_forms() > 0:
		output(log,verbose,1,"  -Found something")
		output(log,verbose,2,"DATA so far")
		for S in spaces:
			p = S.p()
			output(log,verbose,2,"prime "+str(p)+":")
			forms = S.forms()
			used = []
			for f in forms:
				if used.count(f) == 0:
					output(log,verbose,2,str(f))
				used += [f]

	return spaces


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
	primes_used = []
	unramified_prime = false

	while not (empty and started) and not (unique and unramified_prime):
		if gcd(p,chi.modulus()) == 1:
			primes_used += [p]
			if started:
				if not unique:
					output(log,verbose,1,"Min polys of FC not yet uniquely defined")
				if not unramified_prime:
					output(log,verbose,1,"No prime found yet with unique liftings of mod p e-vals")
			spaces = add_on_another_prime(chi,spaces,p,sturm=sturm,log=log,verbose=verbose)
			started = true

			if len(spaces) == 0:
				empty = true
			for Sq in spaces:
				empty = empty or not Sq.is_nontrivial()
		if empty and started:
			output(log,verbose,1,'  -nothing there after intersection')
			spaces = []
		elif started:
			unique = false
			for Sq in spaces:
				unique = unique or Sq.unique()
			if unique and not empty:
				unramified_prime = true
				for f in spaces[0]:
					bool = false
					poly = 1
					for q in f.primes():
						poly *= f[q][0]
					poly = square_free(poly)
					d = poly.disc()
#					output(log,verbose,3,"polynomial discriminant is: "+str(d.factor()))
					for q in primes_used:
						bool = bool or d % q != 0
					unramified_prime = unramified_prime and bool

		p = next_prime(p)
		p = ZZ(p)

	if empty:
		output(log,verbose,1,"Weight 1 space has no exotic forms"+'\n')
		return [weight_one_space([])]
	else:		
		return spaces

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

def verify(fq,chi,log=None,verbose=false):
	# # print "Verifying for chi =",chi
	# # if log != None:
	# # 	file = open(log,'a')
	# # 	file.write("Attempting to verify possible weight 1 form"+'\n')
	# # 	file.close()
	# # if verbose:
	# # 	print "Attempting to verify possible weight 1 form"

	# poly = 1
	# for q in f.primes():
	# 	poly *= f[q][0]
	# Kf = poly.splitting_field('a')
	sturm = ceil(Gamma0(chi.modulus()).index()/3) ## IS THIS RIGHT????
	# f.form_q_exp(sturm,Kf=Kf,verbose=verbose)

	output(log,verbose,1,"  forming q_expansion basis")
	S = ModularSymbols(chi**2,2,1).cuspidal_subspace()
	B = S.q_expansion_basis(sturm)
	g = fq * E1chi(chi,sturm)
	bool = is_in(g,S,sturm)
	output(log,verbose,0,"f E_1(chi) test is: "+str(bool))
	if bool:
		bool = is_in(fq**2,S,sturm)
		output(log,verbose,0,"f^2 test is: "+str(bool))
		output(log,verbose,-1,"Weight 1 form: "+str(fq))
		if bool:
			if log != None:
				file = open("DATA/wt1.data",'a')
				file.write(str(chi)+'\n')
				a = chi.base_ring().gen()
				file.write(str(a)+' satisfies '+str(a.minpoly())+'\n')
				file.write(str(fq)+'\n')
				file.write('------\n')
				file.close()

	return bool


def wt1_space_modp(p,chi,verbose=False,sturm=None,log=None):
	"""
	Returns a sum of Hecke-eigenspaces in weight p which are eigen-doubled and of Artin-type
	"""
	output(log,verbose,1,"   Working with p = "+str(p)+":")

	Kchi = chi(1).parent()
	### THIS IS AN IMPORTANT CHOICE AND MUST BE KEPT TRACK OF
	if Kchi != QQ:
		pchi = Kchi.prime_above(p)
	else:
		pchi = ideal(p)
	M,done = maximal_eigendoubled_Artin(chi,p,pchi,sturm,log=log,verbose=verbose)
	output(log,verbose,1,"    Maximal Artin eigendoubled subspace at "+str(p)+" has dimension "+str(M.dimension())+
		" which gives an upper bound of "+str(floor(M.dimension()/2)))
	if done:
		output(log,verbose,1,"done by lower/upper bound considerations")
		return weight_one_space([])
	else:
		D = decompose(M,chi,sturm,[p],p,log,verbose)
		output(log,verbose,1,"    After decomposition into eigenspaces the upper bound is "+str(D.upper_bound()))
		D._pchi = pchi
		if D.upper_bound() == D.lower_bound():
			output(log,verbose,1,"done by lower/upper bound considerations")
			return weight_one_space([])
		else:
			if p > 2:
				D.remove_CM()

		return D.wt1_space(sturm=sturm)

##  pp is prime over p in Q(chi)
def maximal_eigendoubled_Artin(chi,p,pp,sturm,log=None,verbose=False):
	if sturm == None:
		sturm == STURM
	N = chi.modulus()

	kk = pp.residue_field()
	output(log,verbose,3,"     Forming modsym space")

	M = ModularSymbols(chi,p,1,kk).cuspidal_subspace().new_subspace()
	R = PolynomialRing(M.base_ring(),'x')

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

	exclude = [p]
	ell = 2
	output(log,verbose,2,"    Passing to maximal Artin eigen-doubled subspace")
	while (M.dimension() > 2*lb) and (ell<=sturm):  
	## can we do better here in general?  Are exotic forms never over Q(chi) and thus always come in pairs?
		if exclude.count(ell) == 0 and N.valuation(ell) == Nc.valuation(ell):
		## second condition is imposed because otherwise T_ell is identically 0.
			M = maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=verbose,log=log)
		ell = next_prime(ell)

	return M,M.dimension() <= 2*lb


## returns the maximal subspace of M which at ell is of Artin type (wrt chi) and has doubled eigensocle.
def maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=False,log=None):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	R = PolynomialRing(GF(p),'x')
	x = R.gen()

	output(log,verbose,2,'      Using T_'+str(ell)+' on '+str(M.dimension())+'-dimensional space')

	T_ell = M.hecke_operator(ell)
	f_ell = T_ell.charpoly()
	facts = f_ell.factor()

	output(log,verbose,3,'       Collecting irreducible factors with doubled socle and Artin type')

	f_passed = 1
	passed = false
	for D in facts:
		g = D[0]
		e = D[1]
		if e > 1:  ## doubled
			output(log,verbose,3,'        Poly = '+str(g)+' is doubled.  Checking Artin and eigen-doubled')

			v = FC.possible_Artin_polys(g,chi,ell,p,upper=floor(M.dimension()/2))
				### upper bound above rejects artin polys whose degree is too big to be plausible in this space
			if len(v) > 0:  ## Artin type
				socle = g.substitute(T_ell).kernel()
				passed = socle.dimension() >= 2*g.degree()
				if passed:
					output(log,verbose,3,"         passed --- eigen-doubled and Artin")
				else:
					output(log,verbose,3,"         not eigen-doubled")
			else:
				output(log,verbose,3,"         not Artin")
				passed = false
			if passed:
				f_passed *= g**e
	if f_passed != 1:
		output(log,verbose,3,"      Restricting to "+str(f_passed.factor()))
		M = (f_passed.substitute(T_ell)).kernel()
	else:
		M = M.zero_submodule()

	return M

def decompose(M,chi,sturm,exclude,p,log=None,verbose=false):
	if sturm == None:
		sturm = STURM
	output(log,verbose,2,"    Decomposing by Hecke away from p")
	D = EigenDecomp(decompose_helper([M],sturm,exclude,log=log,verbose=verbose),chi)
	output(log,verbose,3,"    Verifying that each Hecke-system is still eigen-doubled")
	bad_spaces = []
	for r in range(D.num_spaces()):
		if D.eigen_multiplicity(r,exclude,sturm=sturm) < 2:
			bad_spaces.append(D[r])
	for M in bad_spaces:
		D.remove(M)

	return D


def decompose_helper(Ms,sturm,exclude,log=None,verbose=false):
	newMs = Ms
	for q in primes(sturm+1):
		if exclude.count(q)==0:
			output(log,verbose,3,"      decomposing with Hecke operator at "+str(q))
			newMs = decompose_helper_at_q(newMs,q,log=log,verbose=verbose)
	return newMs

def decompose_helper_at_q(Ms,q,log=None,verbose=false):
	if len(Ms)>0:
		M = Ms[0]
		newMs = []
		Tq = M.hecke_operator(q)
		fq = Tq.charpoly()
		fact = fq.factor()
		for D in fact:
			g = D[0]
			e = D[1]
			if e > 1:
				if g.substitute(Tq).kernel().dimension() >= 2 * g.degree():
					newMs += [((g**e).substitute(Tq)).kernel()]
		return newMs + decompose_helper_at_q(Ms[1:len(Ms)+1],q,log=log,verbose=verbose)
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

## no steinberg primes not dividing conductor
def no_steinberg(chi):
	M = chi.modulus()
	N = chi.conductor()
	d = M/N
	fact = d.factor()
	exps = [a[1] for a in fact]
	return len(exps) == 0 or min(exps) > 1


def output(log,verbose,level,str):
	if log != None:
		file = open(log,'a')
		file.write(str+'\n')
		file.close()
	if verbose > level:
		print str

def to_file(log,str):
	if log != None:
		file = open(log,'a')
		file.write(str+'\n')
		file.close()

def to_screen(verbose,level,str):
	if verbose > level:
		print str

### f is the form we are trying to get q_exp
### fs is a list of all forms equal to f we have computed at various primes
def form_qexp(f,fs,upper,log=None,verbose=None):
	p = f.p()
	chi = f.chi()
	N = chi.modulus()
	strong_sturm = ceil(Gamma0(N).index() / 3)  ### CHECK THIS!!!!
	M = f.space()[0]
	kchi = M.base_ring()
	Kf = f.FC_field()
	R = PolynomialRing(Kf,'x')
	pf = Kf.prime_above(p)
	kf = pf.residue_field()
	phibar = Hom(kchi,kf)[0]

	need_more_primes = false

	d = M.dimension()
	V = kf**d 
	W = V
	Ws = [W]
	q = 2
	while W.dimension() > 2:		
		if q != p:
			output(log,verbose,2,"-in form_qexp cutting down to 2-dimensional space with q="+str(q))
			T = M.hecke_operator(q)
			A = T.matrix()
			A = A.apply_map(phibar)
			for WW in Ws:
				A = A.restrict(WW)
			W = A.left_eigenspaces()[0][1]
			Ws.append(W)
		q = next_prime(q)

	fail = W.dimension() < 2
	if fail:
		print "failed in ???!"
		return 0,not fail,need_more_prime,chi
	## confused here by the 190 example but maybe dimension can still be 1 at this point

	if not fail:
		output(log,verbose,2,"--finished cutting down to 2-dimensional space.  Computing e-vals now")

		evs_modp = {}
		hecke = {}
		evs = {}
		for q in primes(strong_sturm):
			output(log,verbose,2,"-in form_qexp computing mod "+str(p)+" eigenvalue at q="+str(q))

			T = M.hecke_operator(q)
			A = T.matrix()
			A = A.apply_map(phibar)
			for WW in Ws:
				A = A.restrict(WW)
			if q != p:
				evs_modp[q] = A.charpoly().roots()[0][0]
			else:
				fp = A.charpoly()
				ap = -fp[1]
				evs_modp[q] = ap
			hecke[q] = FC.possible_Artin_polys(evs_modp[q].minpoly(),chi,q,p,upper=upper)
			if len(hecke[q]) == 0:
				return 0,false,need_more_primes,chi

#			print q,hecke[q]
			if len(hecke[q]) > 1:
				for g in fs:
					if g.p() != p:
						output(log,verbose,2,"--not uniquely determined: using p="+str(g.p())+" to help")
						Mg = g.space()[0]   ### USING ONLY THE FIRST SPACE HERE!!  IS THIS A PROBLEM???
						Kg = g.FC_field()
						pg = Kg.prime_above(g.p())
						kg = pg.residue_field()
						fq = Mg.hecke_polynomial(q)
						if g.p() != q:
							fq = fq.factor()[0][0]
							pi_qs = FC.possible_Artin_polys(fq,chi,q,g.p(),upper=upper)
						else:
							ans,fail = find_ap_minpoly(Mg,kf=kg)
							pi_qs = FC.possible_Artin_polys(ans,chi,q,q)
#						print q,pi_qs
						if len(pi_qs) == 0:
							fail = true
							break  ### LOOKS LIKE I"m NOT BREAKING FAR ENOUGH
						else:
							S1 = set(hecke[q])
							S2 = set(pi_qs)
							hecke[q] = list(S1.intersection(S2))
						if len(hecke[q]) == 1:
							break
						if len(hecke[q]) == 0:
							fail = true

#			print "ans:",hecke[q]
			if fail:
				return 0,not fail,need_more_primes,chi

			if len(hecke[q]) != 1:
				need_more_primes = True
				break
			else:
				fq = hecke[q][0]
				rs = R(fq).roots()
				done = false
				j = 0
				possible_lifts = [r[0] for r in rs if evs_modp[q] == kf(r[0])]
				assert len(possible_lifts)>0, "no congruent root found "+str(rs)+str(fq)
				assert len(possible_lifts)==1, "lift not unique!"
				evs[q] = possible_lifts[0]

		if not need_more_primes:
			### Looking for phi: K_chi --> K_f consistent with other choices
			Kchi = chi(1).parent()
			if Kchi == QQ:
				Kchi = CyclotomicField(2)
			pchi = f.space()._pchi
			found = false
			r = 0
			H = Hom(Kchi,Kf)
			while not found:
				phi = H[r]
				found = phibar(kchi(Kchi.gen())) == kf(phi(Kchi.gen()))
				r += 1
			chi = chi.change_ring(phi)  ### do i want to do this?

			R = PowerSeriesRing(Kf,'q')
			q = R.gens()[0]
			ans = 0
			for n in range(1,strong_sturm):
				ans += an(evs,n,chi) * q**n

			return ans,not fail,need_more_primes,chi
		else:
			output(log,verbose,1,"Min polys not uniquely determined: need to compute with more primes")
			return 0,not fail,need_more_primes,chi

def an(evs,n,chi):
	if n == 1:
		return 1
	else:
		fact = ZZ(n).factor()
		if len(fact) > 1:
			ans = 1
			for f in fact:
				q = f[0]
				e = f[1]
				ans *= an(evs,q**e,chi)
			return ans
		else:
			q = fact[0][0]	
			e = fact[0][1]
			if e == 1:
				return evs[q]
			else:
				return an(evs,q**(e-1),chi) * evs[q] - chi(q) * an(evs,q**(e-2),chi)





def upper_bound(U):
	ans = Infinity
	for S in U:
		ans = min(ans,S.num_forms())

	return ans