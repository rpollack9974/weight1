class EigenDecomp(SageObject):

	def __init__(self,Ms,chi,pp=None,p=None):
		if (not (type(Ms) is list)) and (not (type(Ms) is sage.structure.sequence.Sequence_generic)):
			Ms = [Ms]
		self._spaces = Ms
		self._chi = chi
		if len(Ms) != 0:
			self._p = Ms[0].base_ring().characteristic()
		else:
			self._p = p

	def p(self):
		return self._p

	def chi(self):
		return self._chi

	def spaces(self):
		return self._spaces

	def num_spaces(self):
		return len(self.spaces())

	def __repr__(self):
		return repr(self._spaces)

	def __getitem__(self,j):
		return self._spaces[j]

	##Throw away space M
	def remove(self,M):
		self._spaces.remove(M)

	def hecke_polynomial(self,ell):
		ans = 1
		for j in range(self.num_spaces()):
			ans *= self[j].hecke_polynomial(ell)
		return ans

	## returns the irreducible factor of T_ell on j-th space 
	def hecke_irred(self,j,ell):
		facts = self[j].hecke_polynomial(ell).factor()
		assert len(facts)==1, "Not irreducible in hecke_irred!"
		return facts[0][0]

	def dimension(self):
		ans = 0
		for j in range(self.num_spaces()):
			ans += self[j].dimension()
		return ans

	## this is the degree of the smallest field over which all eigenvectors are defined
	def core_dimension(self,j,exclude,sturm=None):
		M = self[j]
		d = M.dimension()
		if sturm == None:
			sturm = STURM # M.sturm_bound()
		hp_degs = []
		for ell in primes(sturm):
			if exclude.count(ell) == 0:
				f_ell = self.hecke_irred(j,ell)
				hp_degs += [f_ell.degree()]
		return max(hp_degs)



	## returns the multiplicity that the j-th space occurs wrt Hecke algebra with primes in exclude excluded
	def multiplicity(self,j,exclude,sturm=None):
		d = self[j].dimension()
		return d / self.core_dimension(j,exclude,sturm=sturm)

	## returns the dimension of the true eigenspace of j-th space occurs wrt Hecke algebra with primes in exclude excluded
	def eigen_multiplicity(self,j,exclude,sturm=None):
		M = self[j]
		d = M.dimension()
		if sturm == None:
			sturm = STURM 
		for ell in primes(sturm):
			if exclude.count(ell) == 0:
				T = M.hecke_operator(ell)
				f = T.charpoly().factor()[0][0]
				M = f.substitute(T).kernel()
		return M.dimension() / self.core_dimension(j,exclude)

	def hecke_polys(self,j,ps=None,exclude=None,sturm=None,verbose=False):
		if ps == None:
			if sturm == None:
				sturm = STURM # self[j].sturm_bound()
			if exclude != None:
				ps = [q for q in primes(sturm) if exclude.count(q)==0]
			else:		
				ps = [q for q in primes(sturm)]
		ans = {}
		for q in ps:
			if verbose > 2:
				print "In hecke_poly q =",q
			ans[q] = self.hecke_irred(j,q) 
		return ans

	### CHEATING HERE!!!!!  ONLY COMPARING WITH MIN POLY AND 	

	## polys is a dictionary with polys[q] = min_poly of ev
	def hecke_occurs(self,polys):
		ps = polys.keys()
		occurs = False
		j = 0
		while not occurs and j < self.num_spaces():
			h_ev = self.hecke_polys(j,ps=ps)
#			occurs = h_ev == polys
			occurs = true
			for q in h_ev.keys():
				occurs = occurs and polys[q] % h_ev[q] == 0
			j += 1
		return occurs,j-1

	def lift_to_char0_minpolys(self,j,exclude=[],sturm=None):
		chi = self.chi()
		upper = self.upper_bound()
		p = self.p()
		N = chi.modulus()
		h = self.hecke_polys(j,exclude=[p],sturm=sturm)
		### need to do this separately becaues hecke_polys wants to only return irred polys
		if exclude.count(p) == 0:
			h[p] = self[j].hecke_polynomial(p)

		h0 = {}
		fail = false
		### Getting minpolys away from p
		for q in h.keys():
 			if exclude.count(q) == 0 and ((N % p == 0 and q == p) or q != p):
				h0[q] = FC.possible_Artin_polys(h[q],chi,q,p,upper=upper)
#				print q,h0[q]
				if len(h0[q]) == 0:
					fail = true

		###!! why exclude p|N here???
		if exclude.count(p) == 0:
			assert N % p == 0 or len(h[p].factor()) <= 2, "have not decomposed far enough (seen at p)"
			assert N % p != 0 or len(h[p].factor()) <= 1, "have not decomposed far enough (seen at p)"
			pi_alpha = h[p].factor()[0][0]
			kchi = self[j].base_ring()
			l,phibar = pi_alpha.splitting_field('a',map=true)
			alpha = hom_to_poly(pi_alpha,phibar).roots()[0][0]
			if N % p != 0:
				ap = alpha + phibar(kchi(chi(p)))/alpha
			else:
				ap = alpha
			fp = minpoly_over(ap,kchi,phibar)
			h0[p] = FC.possible_Artin_polys(fp,chi,p,p,upper=upper)
#			print p,h0[p]
			if len(h0[p]) == 0:
				fail = true
			
		return weight_one_form(chi,h0,space=EigenDecomp(self[j],self.chi())),not fail

	def upper_bound(self):
		p = self.p()
		N = self.chi().modulus()
		if N % p != 0:
			e = 2
		else:
			e = 1		
		ans = 0
		for j in range(self.num_spaces()):
			ans += floor(self[j].dimension() / e)
		return ans

	def lower_bound(self):
		chi = self.chi()
		N = chi.modulus()
		Nc = chi.conductor()
		lb = 0
		for d in divisors(N/Nc):
			G_old = DirichletGroup(Nc * d)
			chi_old = G_old(chi)
			chi_old = convert_character_to_database(chi_old)
			chi_old = chi_old.minimize_base_ring()
			if CM.keys().count(chi_old) != 0:
				lb += len(divisors((N/Nc)/d)) * len(CM[chi_old])
		return lb

	def unique_lift(self,j):
		bool = true
		ts = self.Artin_types(j)

		bool = len(ts)==1

		if bool:
			G = ts[0]
			f = self.lift_to_char0_minpolys(j,G)
			r = 0
			while bool and r < len(f.keys()):
				q = f.keys()[r]
				bool = bool and len(f[q])==1
				r += 1

		return bool 

	def wt1_space(self,sturm=None):
		p = self.p()
		N = self.chi().modulus()
		if N % p != 0:
			e = 2
		else:
			e = 1
		forms = []
		for r in range(self.num_spaces()):
			f,bool = self.lift_to_char0_minpolys(r,sturm=sturm)
			if bool:
				forms += floor(self[r].dimension()/e) * [f]

		return weight_one_space(forms,self.chi())
	

def unique(d):
	bool = true
	for q in d.keys():
		bool = bool and len(d[q])==1
	return bool





# def find_ap_minpoly(pi_p):
# 	F,phi = pi_p.splitting_field('a',map=true)
# 	rs = pi_p.map_coefficients(phi).roots()
# 	assert len(rs) <= 2 and len(rs)>=1,"problem at p in find_ap_minpoly"
# 	alpha = rs[0][0]
# 	if len(rs) == 1:  ## alpha = beta
# 		ans = (2*alpha).minpoly()
# 	else:
# 		beta = rs[1][0]
# 		ans = (alpha+beta).minpoly()
#	return ans

## h is a dictionary which send q to a polynomial f_q
## M is space of modular symbols for T_q acts by f_q to a power
def find_ap_minpoly(M,h=None,kf=None):
	kchi = M.base_ring()
	p = kchi.characteristic()
	R = PolynomialRing(kchi,'x')
	if kf == None:
		ans = 1
		for q in h.keys():
			ans *= R(h[q])

		d = 1
		fs = ans.factor()
		for Q in fs:			
			d = lcm(d,Q[0].degree())

		if d > 1:
			kf = kchi.extension(d,'a')
		else:
			kf = kchi

	phibar = Hom(kchi,kf)[0]  ## what am I choosing here???? CHECK THIS!
	d = M.dimension()
	V = kf**d 
	W = V
	Ws = [W]
	q = 2
	while W.dimension() > 2 and q < STURM:		
		if q != p:
			T = M.hecke_operator(q)
			A = T.matrix()
			A = A.apply_map(phibar)
			for WW in Ws:
				A = A.restrict(WW)
			W = A.left_eigenspaces()[0][1]
			Ws.append(W)
		q = next_prime(q)

	fail = W.dimension()<2

	T = M.hecke_operator(p)
	A = T.matrix()
	A = A.apply_map(phibar)
	for WW in Ws:
		A = A.restrict(WW)
	f = A.charpoly()
	ap = -f[1]
	ans = ap.minpoly()

	return ans,fail


def reductions_mod_p(f,p,chi,phi,sturm):
	K = f.base_ring()
	Qchi = chi.base_ring()
	if Qchi == QQ:
		Qchi = CyclotomicField(2)
	z = Qchi.gen()
	if pp.has_key((chi,p)):
		pchi = pp[(chi,p)]
	else:
		pchi = Qchi.prime_above(p)
		pp[(chi,p)] = pchi
	kchi = pchi.residue_field()
	if K.degree() != 1:
		pps = K.primes_above(pchi) ##! is this right?
	else:
		pps = [ideal(p)]
	ans = []
	for pf in pps:
		h = {}
		kf = pf.residue_field()
		### make subroutine here
		H = Hom(kchi,kf)
		for phibar in H:
			if phibar(kchi(z)) == kf(phi(z)):
				break
		for q in primes(sturm):
			###!! want to handle p here
			if q != p:
				h[q] = minpoly_over(kf(f[q]),kchi,phibar)
		ans += [h]
	return ans

## finds min poly of alpha over K where phi : K --> L; L a field containing alpha
def minpoly_over(alpha,K,phi):
	L = alpha.parent()
	P = alpha.minpoly()
	R = PolynomialRing(K,'x')
	facts = R(P).factor()
	for Q in facts:
		if hom_to_poly(Q[0],phi).substitute(alpha) == 0:
			return Q[0]

def hom_to_poly(P,phi):
	L = phi(1).parent()
	R = PolynomialRing(L,'x')
	x = R.gen()
	ans = 0
	for j in range(P.degree()+1):
		ans += phi(P[j]) * x**j
	return ans


def galois_compare(chi1,chi2):
	K = chi1.base_ring()
	G = K.galois_group()
	chi1_vals = chi1.values_on_gens()
	chi2_vals = chi2.values_on_gens()
	worked = false
	for sigma in G:
		if map(sigma,chi1_vals) == list(chi2_vals):
			worked = true
			break

	assert worked,"no conjugate char found"

	return sigma
