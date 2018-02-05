
## can compute up to sturm to kick out CM forms --- maybe worth it in some examples e.g. 145
## no T5 in 145 example above (comes in lift_to_char0)
## lower bound is wrong in maximal_eigendoubled_Artin
## cut out wrong at p

### STURM is a global variable which gives the bound to which all initial Hecke decompositions are done
STURM = 20
exotic = {}

def collect_wt1_data(Nmin=None,Nmax=None,Ns=None,sturm=None,verbose=false,pass_buck=false):
#	t = cputime()
	ans = []
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

		worked = true
		for chi in Gc:
			chi = convert_character_to_database(chi)
			chi = chi.minimize_base_ring()
			# if verbose > 0:
			# 	print "\nWorking with",chi
			# file = open(log,'a')
			# file.write("\nWorking with "+str(chi)+"\n")
			# file.close()
			A,bool = wt1(chi,log=log,verbose=verbose,pass_buck=pass_buck)
			if len(A) > 0:
				ans += [[chi,A]]
			worked = worked and bool
#			output(log,verbose,0,"time: "+str(cputime(t))+"\n")
	return ans,worked
	

def wt1(chi,sturm=None,log=None,verbose=false,pass_buck=false):
	"""Computes the space of weight 1 forms with character chi
	
	INPUT:
	chi -- Dirichlet character

	OUTPUT:
    A list of the q-expansions (up to Galois conjugacy) of the weight 1 forms with nebentype chi
	"""
	chi = convert_character_to_database(chi)
	chi = chi.minimize_base_ring()

	if not no_steinberg(chi):
		record_to_exotic(chi,[])
		return [],true

	t = cputime()	
	ans = []
	output(log,verbose,1,"Working with "+str(chi))

	output(log,verbose,2,"-Checking old subspace")
	low_exotic = lower_bound_from_old_exotic(chi,log,verbose)
	output(log,verbose,2,"Dimension of old exotic space is "+str(low_exotic))

	N = chi.modulus()
	Nc = chi.conductor()

	lb = lower_bound(chi)
	output(log,verbose,1,"There are "+str(lb)+" CM form(s)")
	spaces = cut_down_to_unique(chi,sturm=sturm,log=log,verbose=verbose)
	upper = upper_bound(spaces)

	if upper == 0:
		output(log,verbose,0,"time: "+str(cputime(t))+"\n")
		record_to_exotic(chi,[])		
		return [],true
	else:
		if not pass_buck:
			need_more_primes = false
			bad_fs = []
			lower = 0
			S = unique_space(spaces)

			strong_sturm = ceil(Gamma0(N).index() / 3)  ### IS THIS RIGHT?????

			output(log,verbose,1,"Computing to higher precision")
			forms_used = []
			for f in S.forms():
				if forms_used.count(f) == 0:
					fq,phi,need_more_primes,lifted,worked = test_form(f,chi,spaces,log=log,verbose=verbose)
					if need_more_primes:
						bad_fs += [f]
					elif lifted:
						if worked:
							ans += galois_conjugates(fq,chi,phi)
							output_answer('DATA/wt1.data',ans,chi,phi)							
							lower = len(ans)
						else:
							output(log,verbose,1,"Failed to verify")
							remove_form(spaces,f)
					else:
						output(log,verbose,2,"eliminated after computing more e-vals")
						remove_form(spaces,f)
				upper = upper_bound(spaces)
				if lower == upper:					
					record_to_exotic(chi,ans)
					return ans,True

			for f in bad_fs:
				if need_more_primes:
					primes_used = [S.p() for S in spaces]
					pmax = max(primes_used)
					p = next_good_prime(pmax,chi)
					spaces = add_on_another_prime(chi,spaces,p,sturm=sturm,log=log,verbose=verbose)
					upper = upper_bound(spaces)
					if lower == upper:
						record_to_exotic(chi,ans)
						return ans,true
				fq,phi,need_more_primes,lifted,worked = test_form(f,chi,spaces,log=log,verbose=verbose)
				if need_more_primes:
					bad_fs += [f]
				elif lifted:
					if worked:
						ans += galois_conjugates(fq,chi,phi)
						output_answer('DATA/wt1.data',ans,chi,phi)							
						lower += len(ans)
					else:
						output(log,verbose,1,"Failed to verify")
						remove_form(spaces,f)
				else:
					output(log,verbose,1,"Failed to verify!")
					remove_form(spaces,f)
				upper = upper_bound(spaces)
				if lower == upper:
					record_to_exotic(chi,ans)
					return ans,True

			if lower != upper:
				if log != None:
					filename = log+str('.fail')
				else:
					filename = None
				output(filename,verbose,0,str(chi))
				output(filename,verbose,0,"lower = "+str(lower)+"; upper = "+str(upper))

			output(log,verbose,0,"time: "+str(cputime(t))+"\n")

			record_to_exotic(chi,ans)
			return ans,lower == upper
		else:
			output(log,verbose,-1,"PASSING THE BUCK ON THIS ONE!!!")
			output("DATA/hard_levels",verbose,-1,str(chi.modulus()))
			output(log,verbose,0,"time: "+str(cputime(t))+"\n")
			return chi,false


def fixes_chi(sigma,chi,phi):
	vals = chi.values_on_gens()
	bool = true
	for v in vals:
		bool = bool and sigma(phi(v)) == phi(v)
	return bool

def galois_conjugates(fq,chi,phi):
	ans = []
	K = fq.base_ring()
	R = PowerSeriesRing(K,'q')
	q = R.gen()
	GG = K.galois_group()
	for sigma in list(GG):
		if fixes_chi(sigma,chi,phi):
			t = 0
			for n in range(fq.degree()):
				t += sigma(fq[n]) * q**n
			ans += [t]
	return ans



def lower_bound_from_old_exotic(chi,log=None,verbose=False):
	Nc = chi.conductor()
	N = chi.modulus()
	lb = 0
	for d in divisors(N/Nc):
		if d != N/Nc:
			G_old = DirichletGroup(Nc * d)
			chi_old = G_old(chi)
			chi_old = convert_character_to_database(chi_old)
			chi_old = chi_old.minimize_base_ring()
			if not exotic.has_key(chi_old):
				output(log,verbose,2," Computing old subspace attached to "+str(chi_old))
				ans,bool = wt1(chi_old,log=log,verbose=verbose)
				assert bool,"Failed in computing oldforms"
			else:
				output(log,verbose,2," Old subspace attached to "+str(chi_old)+" already computed")
			lb += len(exotic[chi_old])
	return lb



def output_DATA_so_far(spaces,log,verbose):
	output(log,verbose,1,"  -Found something")
	output(log,verbose,2,"DATA so far")
	for S in spaces:
		p = S.p()
		output(log,verbose,2,"prime "+str(p)+":")
		used = []
		for f in S.forms():
			if used.count(f) == 0:
				output(log,verbose,2,str(f))
			used += [f]


def record_to_exotic(chi,ans):
#	print "IN RECORD WITH",chi,ans
	exotic[chi] = []
	for f in ans:
		exotic[chi] += [[f,chi]]

def test_form(f,chi,spaces,log=None,verbose=False):
	fs = forms_equal_to_f(spaces,f)
	d = f.disc()
	### chooses a form at a prime for which mod p reduction has no kernel on these evals
	for g in fs:
		p = g.p()
		if d % p != 0:
			break
	upper = upper_bound(spaces)
	fq,phi,lifted,need_more_primes,chi = form_qexp(g,fs,upper,log=log,verbose=verbose)
	if not need_more_primes and lifted:
		worked = verify(fq,chi,phi,log=log,verbose=verbose)
	else:
		worked = false

	return fq,phi,need_more_primes,lifted,worked

### chooses a form in each (unique) space equal to f 
def forms_equal_to_f(spaces,f):
	fs = []
	for r in range(len(spaces)):
		for g in spaces[r]:
			if g == f:
				fs += [g]
				break
	return fs

def remove_form(spaces,f):
	for S in spaces:
		while S.multiplicity(f) > 0:
			S.remove(f)

def next_good_prime(p,chi):
	N = chi.modulus()
	Nc = chi.conductor()
	p = next_prime(p)
	while N.valuation(p) != Nc.valuation(p):
		p = next_prime(p)

	return ZZ(p)

def min_num_forms(spaces):
	return min([S.num_forms() for S in spaces])

### true if there exists a space with min polys uniquely determined
def is_unique(spaces):
	unique = false
	for S in spaces:
		unique = unique or S.unique()
	return unique

def unique_space(spaces):
	for S in spaces:
		if S.unique():
			break
	assert S.unique(),"no unique space exists in unique_space"
	return S


def has_unramified_prime(spaces):
	primes_used = [S.p() for S in spaces]
	S = unique_space(spaces)
	unramified_prime = true
	for f in S:
		bool = false
		d = 1
		for q in f.primes():
			d *= f[q][0].disc()
		for q in primes_used:
			bool = bool or d % q != 0
		unramified_prime = unramified_prime and bool
	return unramified_prime

def upper_bound(spaces):
	if len(spaces) == 0:
		return 0
	else:
		ans = 0
		used_forms = []
		S = unique_space(spaces)
		for f in S:
			if used_forms.count(f) == 0:
				m = min([S.multiplicity(f) for S in spaces if S.unique()])
				ans += m
				used_forms += [f]
	return ans

def lower_bound(chi):
	N = chi.modulus()
	Nc = chi.conductor()
	lb = 0
	for d in divisors(N/Nc):
		G_old = DirichletGroup(Nc * d)
		Nt = N / (Nc * d)
		chi_old = G_old(chi)
		chi_old = convert_character_to_database(chi_old)
		chi_old = chi_old.minimize_base_ring()
		t = 1
		if CM.keys().count(chi_old) != 0:
#			print "CM at level",Nc*d
			for ell in prime_divisors(Nt):
				if d % ell == 0:
					t *= valuation(Nt,ell)+1
				elif Nc % ell == 0:
					t *= min(1,valuation(Nt,ell))
				else:
					t *= valuation(Nt,ell)-1

			lb += t * len(CM[chi_old])
	return lb

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
	if min_num_forms(spaces) > lower_bound(chi):
		output_DATA_so_far(spaces,log,verbose)
	else:
		output(log,verbose,1,"done by upper/lower bound considerations")

	return spaces

def cut_down_to_unique(chi,sturm=None,log=None,verbose=false):
### get character to agree with Buzzard-Lauder (Huh?)
	if sturm == None:
		sturm = STURM
	N = chi.modulus()
	Nc = chi.conductor()
	unique = false
	empty = false

	p = 1
	j = 0
	spaces = []
	unramified_prime = false
	old_and_CM_gone = false

	while not (unique and unramified_prime and old_and_CM_gone):
		p = next_good_prime(p,chi)
		spaces = add_on_another_prime(chi,spaces,p,sturm=sturm,log=log,verbose=verbose)
		if min_num_forms(spaces) == 0:
			output(log,verbose,1,"Weight 1 space has no exotic forms"+'\n')
			return []
		else:
			unique = is_unique(spaces)
			if unique:
				unramified_prime = has_unramified_prime(spaces)
		if unique and unramified_prime:
			### time to try to remove CM and old exotic forms
			for S in spaces:
				if is_unique(S) and S.p() != 2:
					break
			bool = S.remove_old_and_CM(log,verbose)
			assert bool,"failed on the remove CM/old step"
			if S.num_forms() == 0:
				print "all found forms were CM or old exotic"
				output(log,verbose,1,"Weight 1 space has no exotic forms"+'\n')
				return []
#					print "result at ",S.p(),":",bool,empty
			old_and_CM_gone = old_and_CM_gone or bool
		output(log,verbose,2,"At the end of computing with p="+str(p)+" we have:")
		if not unique:
			output(log,verbose,2," Min polys of FC not yet uniquely defined")
		if not unramified_prime:
			output(log,verbose,2," No prime found yet with unique liftings of mod p e-vals")
		if not old_and_CM_gone:
			output(log,verbose,2," old and CM forms not yet removed")
		if unique and unramified_prime and old_and_CM_gone:
			output(log,verbose,2," We are done here!")


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

def output_answer(filename,ans,chi,phi):
	if filename != None:
		file = open(filename,'a')
		file.write(str(chi)+'\n')
		file.write(str(chi.change_ring(phi))+'\n')
		a = chi.change_ring(phi).base_ring().gen()
		file.write(str(a)+' satisfies '+str(a.minpoly())+'\n')
		for fq in ans:
			file.write(str(fq)+'\n')
			file.write('---\n')
		file.write('------\n')
		file.close()


def verify(fq,chi,phi,log=None,verbose=false):
	sturm = ceil(Gamma0(chi.modulus()).index()/3) ## IS THIS RIGHT????

	output(log,verbose,1,"  forming q_expansion basis")
	S = ModularSymbols(chi**2,2,1).cuspidal_subspace()
	B = S.q_expansion_basis(sturm)
	g = fq * E1chi(chi,phi,sturm)
	bool = is_in(g,S,phi,sturm)
	output(log,verbose,0,"f E_1(chi) test is: "+str(bool))
	if bool:
		bool = is_in(fq**2,S,phi,sturm)
		output(log,verbose,0,"f^2 test is: "+str(bool))
		output(log,verbose,-1,"Weight 1 form: "+str(fq))
		# if bool:
		# 	if log != None:
		# 		file = open("DATA/wt1.data",'a')
		# 		file.write(str(chi)+'\n')
		# 		file.write(str(chi.change_ring(phi))+'\n')
		# 		a = chi.base_ring().gen()
		# 		file.write(str(a)+' satisfies '+str(a.minpoly())+'\n')
		# 		file.write(str(fq)+'\n')
		# 		file.write('------\n')
		# 		file.close()

	return bool


def wt1_space_modp(p,chi,verbose=False,sturm=None,log=None):
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
	output(log,verbose,1,"----")
	output(log,verbose,1,"   Working with p = "+str(p)+":")
	N = chi.modulus()
	Nc = chi.conductor()
	Nt = N / Nc
	assert Nt % p != 0,"working at supercuspidal prime!"
	if N % p != 0:
		e = 2
	else:
		e = 1

	Kchi = chi(1).parent()
	### THIS IS AN IMPORTANT CHOICE AND MUST BE KEPT TRACK OF
	if Kchi != QQ:
		pchi = Kchi.prime_above(p)
	else:
		pchi = ideal(p)
	M,done = maximal_eigendoubled_Artin(chi,p,pchi,sturm=sturm,log=log,verbose=verbose)
	output(log,verbose,1,"    Maximal Artin eigendoubled subspace mod "+str(p)+" has dimension "+str(M.dimension())+
		" which gives an upper bound of "+str(floor(M.dimension()/e)))
	if done:
		output(log,verbose,1,"done by lower/upper bound considerations")
		return weight_one_space([],chi)
	else:
		if N % p != 0:
			exclude = [p]
		else:
			exclude = []
		D = decompose(M,chi,sturm,exclude,p,log,verbose)
		output(log,verbose,1,"    After decomposition into eigenspaces the upper bound is "+str(D.upper_bound()))
		D._pchi = pchi
		if D.upper_bound() == D.lower_bound():
			output(log,verbose,1,"done by lower/upper bound considerations")
			return weight_one_space([],chi)

		S = D.wt1_space(sturm=sturm)

		return S

# THIS CODE HAS PROBLEMS AS Q(chi) MAY NOT CONTAIN Q(omega)
# ##  pp is prime over p in Q(chi)
# ##  N is the conductor of the character
# ##  p || N
# def teich_char(N,pp):
# 	K_chi = pp.ring()
# 	p = pp.residue_field().characteristic()
# 	print K_chi,p
# 	assert p!=2,"no teich for p=2"
# 	G = DirichletGroup(N)
# 	N_tame = N / p**(N.valuation(p))
# 	chis = [chi for chi in list(G) if chi.conductor()==p]
# 	## dumb problem here with code crashing if K_chi = QQ
# 	if p == 3:
# 		return chis[0]
# 	else:
# 		g = primitive_root(p)
# 		while gcd(g,N_tame) != 1:
# 			g += p
# 		for chi in chis:
# 			if valuation(chi(g)-g,pp) > 0:
# 				break
# 	return chi




##  pp is prime over p in Q(chi)
def maximal_eigendoubled_Artin(chi,p,pp,sturm=None,log=None,verbose=False):
	N = chi.modulus()
	if N % p != 0:
		e = 2
	else:
		e = 1
	if sturm == None:
		sturm = STURM
	N = chi.modulus()

	kk = pp.residue_field()
	output(log,verbose,3,"     Forming modsym space")

	M = ModularSymbols(chi,p,1,kk).cuspidal_subspace()
		# if N % p != 0 or p == 2:
		# 	M = ModularSymbols(chi,p,1,kk).cuspidal_subspace()
		# else:
		# 	omega = teich_char(N,pp)
		# 	M = ModularSymbols(chi*omega**(-1),2,1,kk).cuspidal_subspace()
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

	if N % p != 0:
		exclude = [p]
	else:
		exclude = []
	ell = 2
	output(log,verbose,2,"    Passing to maximal Artin eigen-doubled subspace")
	while (floor(M.dimension()/e) > lb) and (ell<=sturm):  
	## can we do better here in general?  Are exotic forms never over Q(chi) and thus always come in pairs?
		if exclude.count(ell) == 0 and N.valuation(ell) == Nc.valuation(ell):
		## second condition is imposed because otherwise T_ell is identically 0.
			M = maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=verbose,log=log)
		ell = next_prime(ell)

	return M,floor(M.dimension()/e) <= lb


## returns the maximal subspace of M which at ell is of Artin type (wrt chi) and has doubled eigensocle.
def maximal_eigendoubled_Artin_at_ell(M,chi,ell,sturm,verbose=False,log=None):
	N = chi.modulus()
	p = M.base_ring().characteristic()
	R = PolynomialRing(GF(p),'x')
	x = R.gen()

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

def convert_character_to_database(chi):
	chis = chi.galois_orbit()
	if max([CM.keys().count(psi) for psi in chis]) > 0: # conjugate of chi is a key in CM form database
		j = [CM.keys().count(psi) for psi in chis].index(1)
		return chis[j]
	else:
		return chi.minimize_base_ring()

# q-expansion of E_1(chi)
def E1chi(chi,phi,acc):
	L = phi(chi(1)).parent()
	R = PolynomialRing(L,'q')
	q = R.gens()[0]

	ans = R(-phi(chi.bernoulli(1))/2)

	for n in range(1,acc):
		coef = 0
		for d in divisors(n):
			coef += phi(chi(d))
		ans += coef * q**n

	return ans

#	return phi(-chi.bernoulli(1)/2) + form_q_exp(d,acc,chi)

## is the q-expansion f in the space S
def is_in(f,S,phi,acc):
	L = f.parent().base_ring()
#	K = S.base_ring()
#	phi = Hom(K,L).an_element()
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
	bool = true
	for q in prime_divisors(d):
		if N.valuation(q) == 0:
			bool = bool and M.valuation(q) > 1
	return bool

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

	fail = (W.dimension() < 2) and (N % p != 0)
	if fail:
		print "failed in ???!"
		return 0,0,not fail,need_more_primes,chi

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
				return 0,0,false,need_more_primes,chi

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
				return 0,0,not fail,need_more_primes,chi

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
#			chi = chi.change_ring(phi)  ### do i want to do this?

			R = PowerSeriesRing(Kf,'q')
			q = R.gens()[0]
			ans = 0
			for n in range(1,strong_sturm):
				ans += an(evs,n,chi,phi) * q**n

			return ans,phi,not fail,need_more_primes,chi
		else:
			output(log,verbose,1,"Min polys not uniquely determined: need to compute with more primes")
			return 0,0,not fail,need_more_primes,chi

def an(evs,n,chi,phi):
	if n == 1:
		return 1
	else:
		fact = ZZ(n).factor()
		if len(fact) > 1:
			ans = 1
			for f in fact:
				q = f[0]
				e = f[1]
				ans *= an(evs,q**e,chi,phi)
			return ans
		else:
			q = fact[0][0]	
			e = fact[0][1]
			if e == 1:
				return evs[q]
			else:
				return an(evs,q**(e-1),chi,phi) * evs[q] - phi(chi(q)) * an(evs,q**(e-2),chi,phi)






